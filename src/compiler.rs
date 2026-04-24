use std::io::{BufRead, Write};

use crate::codegen::c::Generator;
use crate::nodes::*;
use crate::opt;

pub struct Compiler {
    cellsize: u32,
    debugging: bool,
}

impl Compiler {
    pub fn new(cellsize: u32, debugging: bool) -> Self {
        Compiler {
            cellsize,
            debugging,
        }
    }

    pub fn optimize(&self, node: &mut Node) {
        opt::flatten::transform(node);
        opt::simple_loop::transform(node, self.cellsize);
        opt::initial_memory::transform(node);
        opt::propagate::transform(node);
        opt::more_loop::transform(node);
        opt::simple_loop::transform(node, self.cellsize);
        opt::propagate::transform(node);
        opt::more_loop::transform(node);
        opt::affine_loop::transform(node, self.cellsize);
        opt::copy_prop::transform(node);
        opt::range_prop::transform(node);
        opt::remove_dead::transform(node);
        opt::stdlib::transform(node);
    }

    pub fn generate<W: Write>(&self, node: &Node, out: &mut W) -> std::io::Result<()> {
        let gen = Generator::new(self.cellsize, self.debugging);
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
        self.generate(&node, out).map_err(|e| e.to_string())
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
}
