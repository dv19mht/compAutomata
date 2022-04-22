/*
 * FFLOAT  Copyright (C) 2015  Riccardo De Masellis.
 *
 * This program comes with ABSOLUTELY NO WARRANTY.
 * This is free software, and you are welcome to redistribute it
 * under certain conditions; see http://www.gnu.org/licenses/gpl-3.0.html for details.
 */

package utils;

import antlr4_generated.*;
import formula.ldlf.LDLfFormula;
import formula.ldlf.LDLfLocalFormula;
import formula.ltlf.LTLfFormula;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import visitors.LDLfVisitors.LDLfVisitor;
import visitors.LTLfVisitors.LTLfVisitor;
import visitors.PropVisitor.LocalVisitor;

/**
 * Created by Riccardo De Masellis on 28/06/16.
 */
public class ParserUtils {

    public static LTLfFormula parseLTLfFormula(String input){
        LTLfFormula output;

        LTLfFormulaParserLexer lexer = new LTLfFormulaParserLexer(new ANTLRInputStream(input));
        LTLfFormulaParserParser parser = new LTLfFormulaParserParser(new CommonTokenStream(lexer));

        ParseTree tree = parser.expression();

        output = new LTLfVisitor().visit(tree);

        return output;
    }

    public static LDLfFormula parseLDLfFormula(String input){
        LDLfFormula output;

        LDLfFormulaParserLexer lexer = new LDLfFormulaParserLexer(new ANTLRInputStream(input));
        LDLfFormulaParserParser parser = new LDLfFormulaParserParser(new CommonTokenStream(lexer));

        ParseTree tree = parser.expression();

        output = new LDLfVisitor().visit(tree);

        return output;
    }

    public static LDLfLocalFormula parseLocalFormula(String input) {
        LDLfLocalFormula output;

        PropFormulaParserLexer lexer = new PropFormulaParserLexer(new ANTLRInputStream(input));
        PropFormulaParserParser parser = new PropFormulaParserParser(new CommonTokenStream(lexer));
        ParseTree tree = parser.propositionalFormula();
        LocalVisitor<LDLfLocalFormula> implementation = new LocalVisitor(LDLfLocalFormula.class);
        output = implementation.visit(tree);

        return output;
    }
}
