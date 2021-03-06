// Generated from /Users/demas/Lavoro/IntelliJ-Workspace/FLLOAT/src/main/antlr4-grammars/PropFormulaParser.g4 by ANTLR 4.9.1

	package antlr4_generated;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class PropFormulaParserLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		ID=1, TRUE=2, FALSE=3, DOUBLEIMPLY=4, IMPLY=5, OR=6, AND=7, NOT=8, LSEPARATOR=9, 
		RSEPARATOR=10, WS=11;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"ID", "TRUE", "FALSE", "DOUBLEIMPLY", "IMPLY", "OR", "AND", "NOT", "LSEPARATOR", 
			"RSEPARATOR", "WS"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "ID", "TRUE", "FALSE", "DOUBLEIMPLY", "IMPLY", "OR", "AND", "NOT", 
			"LSEPARATOR", "RSEPARATOR", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public PropFormulaParserLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "PropFormulaParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\rY\b\1\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\3\2\5\2\33\n\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\5\3)\n\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4"+
		"\3\4\5\4:\n\4\3\5\3\5\3\5\3\5\3\6\3\6\3\6\3\7\3\7\3\7\5\7F\n\7\3\b\3\b"+
		"\3\b\5\bK\n\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\6\fT\n\f\r\f\16\fU\3\f\3\f"+
		"\2\2\r\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\3\2\4\7\2\62"+
		";AAC\\aac|\5\2\13\f\17\17\"\"\2_\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2"+
		"\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2"+
		"\2\2\2\25\3\2\2\2\2\27\3\2\2\2\3\32\3\2\2\2\5(\3\2\2\2\79\3\2\2\2\t;\3"+
		"\2\2\2\13?\3\2\2\2\rE\3\2\2\2\17J\3\2\2\2\21L\3\2\2\2\23N\3\2\2\2\25P"+
		"\3\2\2\2\27S\3\2\2\2\31\33\t\2\2\2\32\31\3\2\2\2\33\4\3\2\2\2\34\35\7"+
		"V\2\2\35\36\7t\2\2\36\37\7w\2\2\37)\7g\2\2 !\7V\2\2!\"\7T\2\2\"#\7W\2"+
		"\2#)\7G\2\2$%\7v\2\2%&\7t\2\2&\'\7w\2\2\')\7g\2\2(\34\3\2\2\2( \3\2\2"+
		"\2($\3\2\2\2)\6\3\2\2\2*+\7H\2\2+,\7c\2\2,-\7n\2\2-.\7u\2\2.:\7g\2\2/"+
		"\60\7H\2\2\60\61\7C\2\2\61\62\7N\2\2\62\63\7U\2\2\63:\7G\2\2\64\65\7h"+
		"\2\2\65\66\7c\2\2\66\67\7n\2\2\678\7u\2\28:\7g\2\29*\3\2\2\29/\3\2\2\2"+
		"9\64\3\2\2\2:\b\3\2\2\2;<\7>\2\2<=\7/\2\2=>\7@\2\2>\n\3\2\2\2?@\7/\2\2"+
		"@A\7@\2\2A\f\3\2\2\2BC\7~\2\2CF\7~\2\2DF\7~\2\2EB\3\2\2\2ED\3\2\2\2F\16"+
		"\3\2\2\2GH\7(\2\2HK\7(\2\2IK\7(\2\2JG\3\2\2\2JI\3\2\2\2K\20\3\2\2\2LM"+
		"\7#\2\2M\22\3\2\2\2NO\7*\2\2O\24\3\2\2\2PQ\7+\2\2Q\26\3\2\2\2RT\t\3\2"+
		"\2SR\3\2\2\2TU\3\2\2\2US\3\2\2\2UV\3\2\2\2VW\3\2\2\2WX\b\f\2\2X\30\3\2"+
		"\2\2\t\2\32(9EJU\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}