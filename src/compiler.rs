use std::collections::BTreeSet;
use std::io::{BufRead, Write};

use crate::codegen::c::Generator;
use crate::nodes::*;
use crate::opt;

pub struct Compiler {
    cellsize: u32,
    debugging: bool,
    lower_to_vars: bool,
    finite_sim_steps: usize,
}

impl Compiler {
    pub fn new(cellsize: u32, debugging: bool) -> Self {
        Compiler {
            cellsize,
            debugging,
            lower_to_vars: false,
            finite_sim_steps: opt::finite_sim::Config::default().max_steps,
        }
    }

    pub fn set_lower_to_vars(&mut self, v: bool) {
        self.lower_to_vars = v;
    }

    pub fn set_finite_sim_steps(&mut self, steps: usize) {
        self.finite_sim_steps = steps;
    }

    pub fn optimize(&self, node: &mut Node) {
        opt::flatten::transform(node);
        opt::finite_sim::transform(node, self.cellsize, self.finite_sim_steps);
        opt::simple_loop::transform(node, self.cellsize);
        opt::initial_memory::transform(node);
        opt::propagate::transform(node, self.cellsize);
        opt::more_loop::transform(node);
        opt::simple_loop::transform(node, self.cellsize);
        opt::propagate::transform(node, self.cellsize);
        opt::more_loop::transform(node);
        opt::affine_loop::transform(node, self.cellsize);
        opt::copy_prop::transform(node);
        opt::range_prop::transform(node);
        opt::remove_dead::transform(node);
        opt::stdlib::transform(node);
    }

    pub fn analyze_memory(&self, node: &Node) -> Option<BTreeSet<i32>> {
        opt::mem_layout::analyze(node)
    }

    pub fn generate<W: Write>(
        &self,
        node: &Node,
        out: &mut W,
        used_cells: Option<&BTreeSet<i32>>,
    ) -> std::io::Result<()> {
        let gen = Generator::new(
            self.cellsize,
            self.debugging,
            used_cells,
            self.lower_to_vars,
        );
        gen.generate(node, out)
    }

    pub fn compile<R: BufRead, W: Write>(
        &self,
        reader: R,
        out: &mut W,
        input_format: &str,
    ) -> Result<(), String> {
        let mut node = match input_format {
            "bfrle" => crate::parser::bfrle::parse(reader)?,
            _ => crate::parser::brainfuck::parse(reader)?,
        };
        self.optimize(&mut node);
        let used_cells = self.analyze_memory(&node);
        self.generate(&node, out, used_cells.as_ref())
            .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    fn compile_bf(src: &str) -> String {
        let compiler = Compiler::new(8, false);
        let mut out = Vec::new();
        compiler
            .compile(BufReader::new(src.as_bytes()), &mut out, "brainfuck")
            .unwrap();
        String::from_utf8(out).unwrap()
    }

    fn compile_bf_vars(src: &str) -> String {
        let mut compiler = Compiler::new(8, false);
        compiler.set_lower_to_vars(true);
        let mut out = Vec::new();
        compiler
            .compile(BufReader::new(src.as_bytes()), &mut out, "brainfuck")
            .unwrap();
        String::from_utf8(out).unwrap()
    }

    fn compile_bfrle(src: &str) -> String {
        let compiler = Compiler::new(8, false);
        let mut out = Vec::new();
        compiler
            .compile(BufReader::new(src.as_bytes()), &mut out, "bfrle")
            .unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn hello_world() {
        let src = ">+++++++++[<++++++++>-]<.>+++++++[<++++>-]<+.+++++++..+++.\
                   >>>++++++++[<++++>-]<.>>>++++++++++[<+++++++++>-]<---.\
                   <<<<.+++.------.--------.>>+.";
        let output = compile_bf(src);
        assert!(output.contains("PUTS(\"Hello World!\")"));
    }

    #[test]
    fn empty_program() {
        let output = compile_bf("");
        assert!(output.contains("int main(void)"));
        assert!(output.contains("return 0;"));
    }

    #[test]
    fn cat_program() {
        let output = compile_bf(",[.,]");
        assert!(output.contains("GETC()"));
        assert!(output.contains("PUTC("));
        assert!(output.contains("while"));
    }

    #[test]
    fn clear_loop_optimized() {
        let output = compile_bf("+++[-]");
        // After optimization, the +++ and [-] should cancel out
        assert!(!output.contains("while"));
    }

    #[test]
    fn infinite_loop() {
        let output = compile_bf("+[]");
        assert!(output.contains("while (1);"));
    }

    #[test]
    fn empty_loop_on_known_zero_cell_is_removed() {
        let output = compile_bf(">[]<+.");
        assert!(
            !output.contains("while (1);"),
            "known-zero empty loop should be removed: {}",
            output
        );
        assert!(
            output.contains("PUTC(1)") || output.contains("PUTS(\"\\001\")"),
            "program should continue past skipped loop: {}",
            output
        );
    }

    #[test]
    fn regression_no_spurious_infinite_loop() {
        let src = ">++++++++[-<+++++++++>]<.>[][<-]>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.\n\
                   >->+++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
        let output = compile_bf(src);
        assert!(
            !output.contains("while (1); /* infinite loop */"),
            "bad.b should not compile to a spurious infinite loop: {}",
            output
        );
    }

    #[test]
    fn non_zero_stride_loop_simulates_to_hello_world() {
        let src = ">++++++++[-<+++++++++>]<.>[][<-]>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.
                   >->+++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.";
        let output = compile_bf(src);
        assert!(
            output.contains("PUTS(\"Hello World!\\n\")"),
            "bad.b should compile to direct Hello World output: {}",
            output
        );
        assert!(
            !output.contains("PUTC("),
            "bad.b output should be collapsed to a constant string: {}",
            output
        );
    }

    #[test]
    fn finite_sim_steps_are_configurable() {
        let mut compiler = Compiler::new(8, false);
        compiler.set_finite_sim_steps(1);
        let mut out = Vec::new();
        compiler
            .compile(BufReader::new("+++.".as_bytes()), &mut out, "brainfuck")
            .unwrap();
        let output = String::from_utf8(out).unwrap();
        assert!(
            output.contains("PUTS(\"\\003\")"),
            "finite-sim step setting should still produce valid optimized output: {}",
            output
        );
    }

    #[test]
    fn cellsize_16() {
        let compiler = Compiler::new(16, false);
        let mut out = Vec::new();
        compiler
            .compile(BufReader::new("".as_bytes()), &mut out, "brainfuck")
            .unwrap();
        let output = String::from_utf8(out).unwrap();
        assert!(output.contains("uint16_t"));
    }

    #[test]
    fn bfrle_format() {
        let output = compile_bfrle("+*72.");
        // +*72 sets cell to 72 ('H'), then output
        assert!(output.contains("PUTS(\"H\")") || output.contains("PUTC(72)"));
    }

    #[test]
    fn memory_sized_to_usage() {
        let output = compile_bf(",>,[-<+>]<.");
        assert!(
            output.contains("m[2]"),
            "array should be sized to 2: {}",
            output
        );
        assert!(!output.contains("m[30000]"));
    }

    #[test]
    fn memory_falls_back_for_dynamic_pointer() {
        // [>] has dynamic pointer movement
        let output = compile_bf(",+[>]");
        assert!(
            output.contains("m[30000]"),
            "should fall back to 30000 for dynamic pointer: {}",
            output
        );
    }

    #[test]
    fn lower_to_vars_basic() {
        let output = compile_bf_vars(",[.,]");
        assert!(
            output.contains("static uint8_t c0 = 0;"),
            "should declare c0 variable: {}",
            output
        );
        assert!(!output.contains("*p"));
        assert!(output.contains("c0 = GETC()"));
        assert!(output.contains("while (c0)"));
        assert!(output.contains("PUTC(c0)"));
    }

    #[test]
    fn lower_to_vars_multi_cell() {
        let output = compile_bf_vars(",>,[-<+>]<.");
        assert!(
            output.contains("c0 = 0, c1 = 0"),
            "should declare c0, c1: {}",
            output
        );
        assert!(!output.contains("*p"));
    }

    #[test]
    fn lower_to_vars_falls_back_for_dynamic() {
        let output = compile_bf_vars(",+[>]");
        assert!(
            output.contains("m[30000]"),
            "should fall back to array for dynamic pointer: {}",
            output
        );
    }

    #[test]
    fn dead_code_eliminated() {
        // +++--- at end of program, never read -> eliminated
        let output = compile_bf("+++---");
        assert!(output.contains("return 0;"));
        // No actual operations should remain
        let main_body = output.split("int main(void) {").nth(1).unwrap();
        assert!(!main_body.contains("p[0]"));
    }

    #[test]
    fn move_value() {
        // ,[->>+<<] copies cell 0 to cell 2
        let output = compile_bf(",[->>+<<]>>.");
        // The output should reference the moved value
        assert!(output.contains("PUTC(") || output.contains("p[2]") || output.contains("p[0]"));
    }

    #[test]
    fn parse_error_propagated() {
        let compiler = Compiler::new(8, false);
        let mut out = Vec::new();
        let result = compiler.compile(BufReader::new("[".as_bytes()), &mut out, "brainfuck");
        assert!(result.is_err());
    }

    #[test]
    fn branch_merge_preserves_constant() {
        // p[0] = 'A' (65)
        // If(p[1]) { set p[1]=0 } — doesn't touch p[0]
        // Output p[0] — should still be 'A'
        // >++++++++[<++++++++>-]<+  sets p[0]=65
        // >,[[-]<.>]<.              input p[1]; if nonzero, clear p[1] and output p[0]; output p[0]
        // The final output of p[0] should be PUTC(65) since p[0] is 65 in both branches
        let src = ">++++++++[<++++++++>-]<+ >,[ [-] < . > ] < .";
        let output = compile_bf(src);
        assert!(
            output.contains("PUTC(65)") || output.contains("PUTS(\"A"),
            "p[0] should be constant-folded to 65 after branch merge: {}",
            output
        );
    }

    #[test]
    fn post_while_zero_propagates() {
        // After [-], cell is 0. Output it → should be constant
        // ,[-].
        let src = ",[-].";
        let output = compile_bf(src);
        assert!(
            output.contains("PUTC(0)") || output.contains("PUTS(\"\\0\")"),
            "after [-], cell should be known 0: {}",
            output
        );
    }

    #[test]
    fn copy_survives_unrelated_if() {
        // Set p[0] = 'A' (65), copy to p[2], then branch on p[1] (modifying p[3]),
        // then output p[2]. The copy alias p[2]=p[0] should survive the branch.
        //
        // >++++++++[<++++++++>-]<+  → p[0] = 65
        // >>[-]<<                    → p[2] = 0
        // [->+>+<<]                  → would be complex, let's use direct approach
        //
        // Simpler: set p[0]=65, copy to p[1], branch on p[2], output p[1]
        // +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++(65 plusses)
        // >[-]<[->+<]               → p[1] = p[0], p[0] = 0 (move p[0] to p[1])
        // >>,[[-]>+<]<<             → input p[2]; if nonzero, clear it and inc p[3]
        // >.                         → output p[1]
        //
        // With branch-aware copy prop, the optimizer can track that p[1]'s value
        // is unaffected by the branch on p[2], enabling better optimization.
        let src = ">++++++++[<++++++++>-]<+ >[-]< [->+<] >>,[[-]>+<]<< >.";
        let output = compile_bf(src);
        // The key check: p[1] should be output, and ideally as a constant
        assert!(
            output.contains("PUTC(65)")
                || output.contains("PUTS(\"A\")")
                || output.contains("p[1]"),
            "p[1] should be preserved or constant-folded: {}",
            output
        );
    }

    #[test]
    fn alias_preserved_across_conditional_clear() {
        // This tests that copy propagation preserves aliases across If nodes.
        // Pattern: set two values, then branch on a third cell, then output.
        //
        // +++++++++     (p[0] = 9)
        // >+++++        (p[1] = 5)
        // >,[ [-] ]     (input p[3]; if nonzero, clear it — unrelated conditional)
        // <<.           (output p[0], should still be known as 9)
        let src = "+++++++++ >+++++ >,[ [-] ] <<.";
        let output = compile_bf(src);
        assert!(
            output.contains("PUTC(9)") || output.contains("PUTS(\"\\t\")"),
            "p[0] should remain known after unrelated conditional: {}",
            output
        );
    }

    #[test]
    fn dead_move_overwritten_by_input() {
        // ,[->>+<<]>>,. — move p[0] to p[2], then overwrite p[2] with input
        // The move loop stores are dead because p[2] is overwritten and p[0] is never read
        let src = ",[->>+<<]>>,.";
        let output = compile_bf(src);
        let main_body = output.split("int main(void) {").nth(1).unwrap();
        assert!(
            !main_body.contains("if ") && !main_body.contains("if("),
            "dead move inside conditional should be eliminated: {}",
            output
        );
    }

    #[test]
    fn conditional_dead_store_removed() {
        // Set p[0]=5, input p[1], if p[1]!=0 move p[0] to p[2] and clear p[1],
        // then clear p[2] and output it.
        // The move to p[2] inside the if is dead because p[2] is cleared after.
        let src = "+++++ >,[ ->+<  [-] ] >[-] .";
        let output = compile_bf(src);
        let main_body = output.split("int main(void) {").nth(1).unwrap();
        assert!(
            !main_body.contains("p[2] =") && !main_body.contains("p[2] +="),
            "dead store to p[2] inside if should be removed: {}",
            output
        );
    }

    #[test]
    fn live_conditional_store_preserved() {
        // Same pattern but p[2] is output instead of being cleared
        // ,[->>+<<]>>. — move p[0] to p[2] then output p[2]
        // The move IS used, so it must be preserved
        let src = ",[->>+<<]>>.";
        let output = compile_bf(src);
        assert!(
            output.contains("PUTC(") || output.contains("p[2]") || output.contains("p[0]"),
            "live move should produce output code: {}",
            output
        );
    }

    #[test]
    fn regression_puts_once_with_exact_message() {
        let src = "
            >[-]<[-]++++++[->+++++++++++<]>+.-[---<+++++>]<+.--.+++.+++++.-.>+++++[<
            ---->-]<+.->+++++[<++++>-]<.-----------.++++++.-.--[--->+<]>----.+++++[-
            <+++>]<.---------.[--->+<]>--.---[-<++++>]<.------------.---.--[--->+<]>
            -.+[-<+++>]<++.++++.--.+.++++++++++++.------------.--[--->+<]>--.+++[-<+
            ++>]<.++++.+++.-----------.--..--.+.++++++++++.-------.--[--->+<]>-.++++
            [-<+++>]<++.+++++++.--------.-----------.+++.+++++++++++++.[--->+<]>----
            --.[-<+++>]<+.+.+++++++++++++.+++.++.---------------.-.-[--->+<]>-.+[-<+
            ++>]<+.+>++++[<++++>-]<.>++++[<---->-]<.--[--->+<]>-.---[-<++++>]<.-----
            .[--->+<]>-----.---[-<++++>]<.------------.---.--[--->+<]>-.+++[-<+++>]<
            .++++..----.+++++.---------.+++++++++.++++++.[---->+<]>+++.+[-<+++>]<++.
            +++++++++.----------.-[--->+<]>-.+++++[-<+++>]<.---------.[--->+<]>--.--
            -[-<++++>]<.------------.---.--[--->+<]>-.---[-<++++>]<+.-------.-----.+
            ++++++++++++.>++++[<---->-]<-.+++++++++++++.+.--------------.-[-->+<]>--
            --.[-]++++++++++.[-]<
        ";
        let output = compile_bf(src);
        assert_eq!(
            output.matches("PUTS(\"").count(),
            1,
            "expected single PUTS call: {output}"
        );
        assert!(
            !output.contains("PUTC("),
            "expected no PUTC calls: {output}"
        );
        assert!(
            output.contains(
                "PUTS(\"Computation of the eighth impeccable number aborted due to the imminent end of the universe.\\n\")"
            ),
            "expected exact PUTS message: {output}"
        );
    }
}
