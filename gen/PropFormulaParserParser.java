// Generated from /Users/demas/Lavoro/IntelliJ-Workspace/FLLOAT/src/main/antlr4-grammars/PropFormulaParser.g4 by ANTLR 4.9.1

	package antlr4_generated;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class PropFormulaParserParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		ID=1, TRUE=2, FALSE=3, DOUBLEIMPLY=4, IMPLY=5, OR=6, AND=7, NOT=8, LSEPARATOR=9, 
		RSEPARATOR=10, WS=11;
	public static final int
		RULE_propositionalFormula = 0, RULE_doubleImplicationProp = 1, RULE_implicationProp = 2, 
		RULE_orProp = 3, RULE_andProp = 4, RULE_notProp = 5, RULE_atom = 6;
	private static String[] makeRuleNames() {
		return new String[] {
			"propositionalFormula", "doubleImplicationProp", "implicationProp", "orProp", 
			"andProp", "notProp", "atom"
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

	@Override
	public String getGrammarFileName() { return "PropFormulaParser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public PropFormulaParserParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class PropositionalFormulaContext extends ParserRuleContext {
		public DoubleImplicationPropContext doubleImplicationProp() {
			return getRuleContext(DoubleImplicationPropContext.class,0);
		}
		public PropositionalFormulaContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_propositionalFormula; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterPropositionalFormula(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitPropositionalFormula(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitPropositionalFormula(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PropositionalFormulaContext propositionalFormula() throws RecognitionException {
		PropositionalFormulaContext _localctx = new PropositionalFormulaContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_propositionalFormula);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(14);
			doubleImplicationProp();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DoubleImplicationPropContext extends ParserRuleContext {
		public List<ImplicationPropContext> implicationProp() {
			return getRuleContexts(ImplicationPropContext.class);
		}
		public ImplicationPropContext implicationProp(int i) {
			return getRuleContext(ImplicationPropContext.class,i);
		}
		public List<TerminalNode> DOUBLEIMPLY() { return getTokens(PropFormulaParserParser.DOUBLEIMPLY); }
		public TerminalNode DOUBLEIMPLY(int i) {
			return getToken(PropFormulaParserParser.DOUBLEIMPLY, i);
		}
		public DoubleImplicationPropContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_doubleImplicationProp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterDoubleImplicationProp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitDoubleImplicationProp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitDoubleImplicationProp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DoubleImplicationPropContext doubleImplicationProp() throws RecognitionException {
		DoubleImplicationPropContext _localctx = new DoubleImplicationPropContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_doubleImplicationProp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(16);
			implicationProp();
			setState(21);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==DOUBLEIMPLY) {
				{
				{
				setState(17);
				match(DOUBLEIMPLY);
				setState(18);
				implicationProp();
				}
				}
				setState(23);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ImplicationPropContext extends ParserRuleContext {
		public List<OrPropContext> orProp() {
			return getRuleContexts(OrPropContext.class);
		}
		public OrPropContext orProp(int i) {
			return getRuleContext(OrPropContext.class,i);
		}
		public List<TerminalNode> IMPLY() { return getTokens(PropFormulaParserParser.IMPLY); }
		public TerminalNode IMPLY(int i) {
			return getToken(PropFormulaParserParser.IMPLY, i);
		}
		public ImplicationPropContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_implicationProp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterImplicationProp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitImplicationProp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitImplicationProp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ImplicationPropContext implicationProp() throws RecognitionException {
		ImplicationPropContext _localctx = new ImplicationPropContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_implicationProp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(24);
			orProp();
			setState(29);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==IMPLY) {
				{
				{
				setState(25);
				match(IMPLY);
				setState(26);
				orProp();
				}
				}
				setState(31);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class OrPropContext extends ParserRuleContext {
		public List<AndPropContext> andProp() {
			return getRuleContexts(AndPropContext.class);
		}
		public AndPropContext andProp(int i) {
			return getRuleContext(AndPropContext.class,i);
		}
		public List<TerminalNode> OR() { return getTokens(PropFormulaParserParser.OR); }
		public TerminalNode OR(int i) {
			return getToken(PropFormulaParserParser.OR, i);
		}
		public OrPropContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_orProp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterOrProp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitOrProp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitOrProp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OrPropContext orProp() throws RecognitionException {
		OrPropContext _localctx = new OrPropContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_orProp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(32);
			andProp();
			setState(37);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==OR) {
				{
				{
				setState(33);
				match(OR);
				setState(34);
				andProp();
				}
				}
				setState(39);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AndPropContext extends ParserRuleContext {
		public List<NotPropContext> notProp() {
			return getRuleContexts(NotPropContext.class);
		}
		public NotPropContext notProp(int i) {
			return getRuleContext(NotPropContext.class,i);
		}
		public List<TerminalNode> AND() { return getTokens(PropFormulaParserParser.AND); }
		public TerminalNode AND(int i) {
			return getToken(PropFormulaParserParser.AND, i);
		}
		public AndPropContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_andProp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterAndProp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitAndProp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitAndProp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AndPropContext andProp() throws RecognitionException {
		AndPropContext _localctx = new AndPropContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_andProp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(40);
			notProp();
			setState(45);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==AND) {
				{
				{
				setState(41);
				match(AND);
				setState(42);
				notProp();
				}
				}
				setState(47);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NotPropContext extends ParserRuleContext {
		public AtomContext atom() {
			return getRuleContext(AtomContext.class,0);
		}
		public TerminalNode NOT() { return getToken(PropFormulaParserParser.NOT, 0); }
		public TerminalNode LSEPARATOR() { return getToken(PropFormulaParserParser.LSEPARATOR, 0); }
		public PropositionalFormulaContext propositionalFormula() {
			return getRuleContext(PropositionalFormulaContext.class,0);
		}
		public TerminalNode RSEPARATOR() { return getToken(PropFormulaParserParser.RSEPARATOR, 0); }
		public NotPropContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_notProp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterNotProp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitNotProp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitNotProp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NotPropContext notProp() throws RecognitionException {
		NotPropContext _localctx = new NotPropContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_notProp);
		int _la;
		try {
			setState(59);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(49);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==NOT) {
					{
					setState(48);
					match(NOT);
					}
				}

				setState(51);
				atom();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(53);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==NOT) {
					{
					setState(52);
					match(NOT);
					}
				}

				setState(55);
				match(LSEPARATOR);
				setState(56);
				propositionalFormula();
				setState(57);
				match(RSEPARATOR);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AtomContext extends ParserRuleContext {
		public List<TerminalNode> ID() { return getTokens(PropFormulaParserParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(PropFormulaParserParser.ID, i);
		}
		public TerminalNode TRUE() { return getToken(PropFormulaParserParser.TRUE, 0); }
		public TerminalNode FALSE() { return getToken(PropFormulaParserParser.FALSE, 0); }
		public AtomContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_atom; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).enterAtom(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof PropFormulaParserListener ) ((PropFormulaParserListener)listener).exitAtom(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof PropFormulaParserVisitor ) return ((PropFormulaParserVisitor<? extends T>)visitor).visitAtom(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AtomContext atom() throws RecognitionException {
		AtomContext _localctx = new AtomContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_atom);
		int _la;
		try {
			setState(69);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
			case DOUBLEIMPLY:
			case IMPLY:
			case OR:
			case AND:
			case RSEPARATOR:
				enterOuterAlt(_localctx, 1);
				{
				setState(64);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==ID) {
					{
					{
					setState(61);
					match(ID);
					}
					}
					setState(66);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				break;
			case TRUE:
				enterOuterAlt(_localctx, 2);
				{
				setState(67);
				match(TRUE);
				}
				break;
			case FALSE:
				enterOuterAlt(_localctx, 3);
				{
				setState(68);
				match(FALSE);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\rJ\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\3\2\3\2\3\3\3\3\3\3\7\3\26"+
		"\n\3\f\3\16\3\31\13\3\3\4\3\4\3\4\7\4\36\n\4\f\4\16\4!\13\4\3\5\3\5\3"+
		"\5\7\5&\n\5\f\5\16\5)\13\5\3\6\3\6\3\6\7\6.\n\6\f\6\16\6\61\13\6\3\7\5"+
		"\7\64\n\7\3\7\3\7\5\78\n\7\3\7\3\7\3\7\3\7\5\7>\n\7\3\b\7\bA\n\b\f\b\16"+
		"\bD\13\b\3\b\3\b\5\bH\n\b\3\b\2\2\t\2\4\6\b\n\f\16\2\2\2L\2\20\3\2\2\2"+
		"\4\22\3\2\2\2\6\32\3\2\2\2\b\"\3\2\2\2\n*\3\2\2\2\f=\3\2\2\2\16G\3\2\2"+
		"\2\20\21\5\4\3\2\21\3\3\2\2\2\22\27\5\6\4\2\23\24\7\6\2\2\24\26\5\6\4"+
		"\2\25\23\3\2\2\2\26\31\3\2\2\2\27\25\3\2\2\2\27\30\3\2\2\2\30\5\3\2\2"+
		"\2\31\27\3\2\2\2\32\37\5\b\5\2\33\34\7\7\2\2\34\36\5\b\5\2\35\33\3\2\2"+
		"\2\36!\3\2\2\2\37\35\3\2\2\2\37 \3\2\2\2 \7\3\2\2\2!\37\3\2\2\2\"\'\5"+
		"\n\6\2#$\7\b\2\2$&\5\n\6\2%#\3\2\2\2&)\3\2\2\2\'%\3\2\2\2\'(\3\2\2\2("+
		"\t\3\2\2\2)\'\3\2\2\2*/\5\f\7\2+,\7\t\2\2,.\5\f\7\2-+\3\2\2\2.\61\3\2"+
		"\2\2/-\3\2\2\2/\60\3\2\2\2\60\13\3\2\2\2\61/\3\2\2\2\62\64\7\n\2\2\63"+
		"\62\3\2\2\2\63\64\3\2\2\2\64\65\3\2\2\2\65>\5\16\b\2\668\7\n\2\2\67\66"+
		"\3\2\2\2\678\3\2\2\289\3\2\2\29:\7\13\2\2:;\5\2\2\2;<\7\f\2\2<>\3\2\2"+
		"\2=\63\3\2\2\2=\67\3\2\2\2>\r\3\2\2\2?A\7\3\2\2@?\3\2\2\2AD\3\2\2\2B@"+
		"\3\2\2\2BC\3\2\2\2CH\3\2\2\2DB\3\2\2\2EH\7\4\2\2FH\7\5\2\2GB\3\2\2\2G"+
		"E\3\2\2\2GF\3\2\2\2H\17\3\2\2\2\13\27\37\'/\63\67=BG";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}