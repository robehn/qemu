/*
 * Copyright (C) 2019, Alex Bennée <alex.bennee@linaro.org>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include <inttypes.h>
#include <assert.h>
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>
#include <unistd.h>
#include <stdio.h>
#include <glib.h>

#include <qemu-plugin.h>

/* An instruction sequence is 4 to 8 instruction.
 * If you think it's some other numbers, you are wrong.
 */
#define SEQ_MAX 20
#define SEQ_MIN 4
#define HOT_SEQS 20

//-d plugin

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static bool do_inline = true;
static GHashTable *instructionblock_table = 0;
static GMutex lock;

typedef struct {
    struct    qemu_plugin_scoreboard *sb_count;
    uintptr_t start_addr;
    size_t    num_ins;
    size_t    tb_count;
    uint32_t  *instructions;
} InstructionBlock;

#ifdef LOG_IB
static void log_instruction_block(InstructionBlock* ib)
{
    uint64_t exe_count = qemu_plugin_u64_sum(qemu_plugin_scoreboard_u64(ib->sb_count));
    g_autoptr(GString) ib_str = g_string_new("-------------- IB --------------\n");
    g_string_append_printf(ib_str, "Execution count  :%lu\n", exe_count);
    g_string_append_printf(ib_str, "Address          :0x%lx\n", ib->start_addr);
    g_string_append_printf(ib_str, "Instruction count:%zu\n", ib->num_ins);
    g_string_append_printf(ib_str, "Translation count:%zu\n", ib->tb_count);
    g_string_append_printf(ib_str, "Opcodes: {");
    for (size_t i = 0; i < ib->num_ins; i++) {
      g_string_append_printf(ib_str, "0x%x, ", ib->instructions[i]);
    }
    g_string_append_printf(ib_str, "0x0 }\n");
    qemu_plugin_outs(ib_str->str);
}

static void log_ib_table() {
    GList * block_it = g_hash_table_get_values(instructionblock_table);
    if (block_it != 0) {
        for (; block_it->next != 0; block_it = block_it->next) {
            InstructionBlock *ib = (InstructionBlock *) block_it->data;
            log_instruction_block(ib);
        }
    }
}
#endif

struct tree_node {
  uint32_t opcode;
  uint64_t count;
  int end;
  int size;
  struct tree_node **next;
  uint32_t *opc_next; // sort for binary search
};

int tree_node_pos_add(struct tree_node *node, uint32_t opcode) {
  int pos = node->end;
  if (node->end == node->size) {
    int asize = node->size == 0 ? 10 : 2*(node->size);
    node->next = g_realloc(node->next, asize * sizeof(struct tree_node *));
    node->opc_next = g_realloc(node->opc_next, asize * sizeof(uint32_t));
    node->size = asize;
  }

  struct tree_node *new_node = g_new0(struct tree_node, 1);
  new_node->opcode = opcode;
  node->opc_next[pos] = new_node->opcode;
  node->next[pos] = new_node;
  node->end++;
  return pos;
}

int tree_node_pos_next(struct tree_node *node, uint32_t opcode)
{
  for (int i = 0; i < node->end; i++) {
    if (node->opc_next[i] == opcode) {
      return i;
    }
  }
  return -1;
}

struct tree_node* tree_node_next(struct tree_node *node, uint32_t opcode, uint64_t add_count)
{
  int pos = tree_node_pos_next(node, opcode);
  if (pos == -1) {
    pos = tree_node_pos_add(node, opcode);
  }
  struct tree_node* ret = node->next[pos];
  ret->count += add_count;
  return ret;
}

struct tree_node root = {0};
static uint64_t total_executed = 0;

static void build_tree() {
    GList * block_it = g_hash_table_get_values(instructionblock_table);
    struct tree_node *curser = &root;
    if (block_it != 0) {
        for (; block_it->next != 0; block_it = block_it->next) {
            InstructionBlock *ib = (InstructionBlock *) block_it->data;
            uint64_t exe_count = qemu_plugin_u64_sum(qemu_plugin_scoreboard_u64(ib->sb_count));
            total_executed += exe_count * ib->num_ins;
            for (size_t i = 0; i < ib->num_ins; i++) {
                curser = &root;
                for (size_t k = i; k < ib->num_ins && k < SEQ_MAX; k++) {
                    curser = tree_node_next(curser, ib->instructions[k], exe_count);
                }
                break;
            }
        }
    }
}

struct hot_seq {
    uint64_t count;
    int seq[SEQ_MAX];
};

static struct hot_seq hot_seqs[HOT_SEQS];

static void add_hot_seq(struct hot_seq *new_seq)
{
    for (int i = 0; i < HOT_SEQS; i++) {
        if (hot_seqs[i].count < new_seq->count) {
            hot_seqs[i] = *new_seq;
            return;
        }
    }
}

static uint64_t hot_seq_instructions(struct hot_seq *count)
{
    uint64_t ret = 0;
    for (int k = 0; k < SEQ_MAX; k++) {
        int pos = count->seq[k];
        if (pos < 0) {
            break;
        }
        ret++;
    }
    return ret;
}

static void sort_hot_seq()
{
    // Bubble sort FTW !
    for (int i = 0; i < HOT_SEQS; i++) {
        uint64_t i_count = hot_seq_instructions(&hot_seqs[i]);
        for (int k = i + 1; k < HOT_SEQS; k++) {
            uint64_t k_count = hot_seq_instructions(&hot_seqs[k]);
            if ((hot_seqs[k].count * k_count) > (hot_seqs[i].count * i_count)) {
                struct hot_seq temp = hot_seqs[i];
                hot_seqs[i] = hot_seqs[k];
                hot_seqs[k] = temp;
            }
        }
    }
}

static uint64_t hot_seq_low()
{
    uint64_t ret = UINT_MAX;
    for (int i = 0; i < HOT_SEQS; i++) {
        ret = hot_seqs[i].count < ret ? hot_seqs[i].count : ret;
    }
    return ret;
}

static void find_matching_ibs(uint32_t opcodes[]) {
    GList * block_it = g_hash_table_get_values(instructionblock_table);
    g_autoptr(GString) str = g_string_new("At:");
    if (block_it != 0) {
        for (; block_it->next != 0; block_it = block_it->next) {
            InstructionBlock *ib = (InstructionBlock *) block_it->data;
            int match = 1;
            for (int i = 0; i < ib->num_ins && i < SEQ_MAX; i++) {
                if (opcodes[i] == 0) {
                    break;
                }
                if (ib->instructions[i] != opcodes[i]) {
                    match = 0;
                    break;
                }
            }
            if (match == 1) {
                g_string_append_printf(str, " 0x%lx ", ib->start_addr);
            }
        }
    }
    g_string_append_printf(str, "\n");
    qemu_plugin_outs(str->str);
}

static void log_hot_seq()
{
    for (int i = 0; i < HOT_SEQS; i++) {
        uint32_t opcodes[SEQ_MAX] = {0};
        struct tree_node *curser = &root;
        if (hot_seqs[i].count == 0) {
              continue;
        }
        uint64_t last_count = 0;
        uint64_t instruction_count = 0;
        g_autoptr(GString) hs_str = g_string_new("{");
        for (int k = 0; k < SEQ_MAX; k++) {
            int pos = hot_seqs[i].seq[k];
            if (pos < 0) {
                g_string_append_printf(hs_str, "0x0");
                break;
            }
            curser = curser->next[pos];
            g_string_append_printf(hs_str, "0x%x, ", curser->opcode);
            opcodes[k] = curser->opcode;
            last_count = curser->count;
            instruction_count++;
        }
        uint64_t nins =  last_count * instruction_count;
        double   perc = (nins*1.0) / total_executed;
        g_string_append_printf(hs_str, "} Executed: %lu, %lu of %lu == %g, ",
                               last_count, nins, total_executed, perc);
        qemu_plugin_outs(hs_str->str);
        find_matching_ibs(opcodes);
    }
}

static void find_next(struct tree_node* current, struct hot_seq *new_seq, int pos, int index)
{
    if (pos == SEQ_MAX) {
      return;
    }

    uint64_t old_count = new_seq->count;
    new_seq->count = current->count;
    new_seq->seq[pos] = index;
    if (pos < SEQ_MIN) {
        for (int i = 0; i < current->end; i++) {
          find_next(current->next[i], new_seq, pos+1, i);
        }
    } else {
        uint64_t same_count = 0;
        for (int i = 0; i < current->end; i++) {
            same_count = current->next[i]->count;
            if (same_count == current->count) {
              break;
            }
        }
        if (same_count < current->count) {
            add_hot_seq(new_seq);
        }
        for (int i = 0; i < current->end; i++) {
            find_next(current->next[i], new_seq, pos+1, i);
        }
    }
    new_seq->count = old_count;
    new_seq->seq[pos] = -1;
}

static void process_tree() {
    for (int i = 0; i < HOT_SEQS; i++) {
        hot_seqs[i].count = 0;
        for (int k = 0; k < SEQ_MAX; k++) {
            hot_seqs[i].seq[k] = -1;
        }
    }
    for (int i = 0; i < root.end ; i++) {
        int64_t low = hot_seq_low();
        if (root.next[i]->count > low) {
            struct hot_seq new_seq;
            new_seq.count = 0;
            for (int k = 0; k < SEQ_MAX; k++) {
              new_seq.seq[k] = -1;
            }
            find_next(root.next[i], &new_seq, 0, i);
        }
    }
}

static void plugin_init(void)
{
    instructionblock_table = g_hash_table_new(NULL, g_direct_equal);
}

static void plugin_exit(qemu_plugin_id_t id, void *p)
{
#ifdef LOG_IB
    log_ib_table();
#endif
    build_tree();
    process_tree();
    sort_hot_seq();
    log_hot_seq();
    // We skip freeing since we are exiting, it just takes more time.
}

static void tb_exec(unsigned int cpu_index, void *udata)
{
    InstructionBlock *ib = (InstructionBlock *)udata;
    qemu_plugin_u64_add(qemu_plugin_scoreboard_u64(ib->sb_count), cpu_index, 1);
}

static void new_tb_added(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
    InstructionBlock *ib = 0;
    uint64_t pc      = qemu_plugin_tb_vaddr(tb);
    size_t ins_in_tb = qemu_plugin_tb_n_insns(tb);
    uint64_t hash    = pc ^ ins_in_tb;

    g_mutex_lock(&lock);

    ib = (InstructionBlock *) g_hash_table_lookup(instructionblock_table, (gconstpointer) hash);
    if (ib != 0) {
        ib->tb_count++;
    } else {
        ib = g_new0(InstructionBlock, 1);
        ib->sb_count = qemu_plugin_scoreboard_new(sizeof(uint64_t));
        ib->start_addr = pc;
        ib->num_ins    = ins_in_tb;
        ib->tb_count   = 1;
        ib->instructions = g_new0(uint32_t, ins_in_tb);

        for (size_t i = 0; i < ins_in_tb; i++) {
          uint32_t opcode = 0;
          struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
          qemu_plugin_insn_data(insn, &opcode, sizeof(opcode));
          ib->instructions[i] = opcode;
        }
        g_hash_table_insert(instructionblock_table, (gpointer) hash, (gpointer) ib);
    }

    g_mutex_unlock(&lock);

    if (do_inline) {
        qemu_plugin_register_vcpu_tb_exec_inline_per_vcpu(
           tb, QEMU_PLUGIN_INLINE_ADD_U64, qemu_plugin_scoreboard_u64(ib->sb_count), 1);
    } else {
        qemu_plugin_register_vcpu_tb_exec_cb(
           tb, tb_exec, QEMU_PLUGIN_CB_NO_REGS, (void *)ib);
    }
}

QEMU_PLUGIN_EXPORT
int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info, int argc, char **argv)
{
    for (int i = 0; i < argc; i++) {
        char *opt = argv[i];
        g_auto(GStrv) tokens = g_strsplit(opt, "=", 2);
        if (g_strcmp0(tokens[0], "inline") == 0) {
            if (!qemu_plugin_bool_parse(tokens[0], tokens[1], &do_inline)) {
                fprintf(stderr, "boolean argument parsing failed: %s\n", opt);
                return -1;
            }
        } else {
            fprintf(stderr, "option parsing failed: %s\n", opt);
            return -1;
        }
    }

    plugin_init();

    qemu_plugin_register_vcpu_tb_trans_cb(id, new_tb_added);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

    return 0;
}

