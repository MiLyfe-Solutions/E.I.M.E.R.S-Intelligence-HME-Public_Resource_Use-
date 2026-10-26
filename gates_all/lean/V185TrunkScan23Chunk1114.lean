import V185TrunkScan23Chunk1113

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6598146 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6598146 : Nat := 118140960795 + 6598146 * 2 ^ 59
def prefixEnd_6598146 : Nat := 4983230072969 + 3 ^ 40 * 6598146 * 2
def baseEnd_6598146 : Nat := 3388020326540846957130685

theorem tailTrace_6598146 : CollatzResearch.WordTrace tailWord_6598146 prefixEnd_6598146 3388020326540846957130685 := by
  unfold tailWord_6598146
  simp only [CollatzResearch.WordTrace]
  refine ⟨60163538788512847616729573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160436103436034260311278861 60163538788512847616729573)
  ·
    refine ⟨11280663522846158928136795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60163538788512847616729573 11280663522846158928136795)
    ·
      refine ⟨16920995284269238392205193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280663522846158928136795 16920995284269238392205193)
      ·
        refine ⟨12690746463201928794153895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16920995284269238392205193 12690746463201928794153895)
        ·
          refine ⟨19036119694802893191230843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12690746463201928794153895 19036119694802893191230843)
          ·
            refine ⟨28554179542204339786846265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19036119694802893191230843 28554179542204339786846265)
            ·
              refine ⟨21415634656653254840134699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28554179542204339786846265 21415634656653254840134699)
              ·
                refine ⟨32123451984979882260202049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21415634656653254840134699 32123451984979882260202049)
                ·
                  refine ⟨24092588988734911695151537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32123451984979882260202049 24092588988734911695151537)
                  ·
                    refine ⟨18069441741551183771363653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24092588988734911695151537 18069441741551183771363653)
                    ·
                      refine ⟨3388020326540846957130685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18069441741551183771363653 3388020326540846957130685)
                      ·
                        rfl

theorem cell23_6598146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6598146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598146 prefixEnd_6598146 := by exact prefixLift 6598146
  have htrace : WordTrace (prefixWord ++ tailWord_6598146) baseStart_6598146 baseEnd_6598146 := by
    simpa [prefixWord, tailWord_6598146, baseEnd_6598146] using wordTrace_append hprefix tailTrace_6598146
  have hstable : (prefixWord ++ tailWord_6598146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598146).length < 2 ^ (prefixWord ++ tailWord_6598146).sum := by decide
  have hdescent : baseEnd_6598146 < baseStart_6598146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598152 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_6598152 : Nat := 118140960795 + 6598152 * 2 ^ 59
def prefixEnd_6598152 : Nat := 4983230072969 + 3 ^ 40 * 6598152 * 2
def baseEnd_6598152 : Nat := 1129341135808257977885219

theorem tailTrace_6598152 : CollatzResearch.WordTrace tailWord_6598152 prefixEnd_6598152 1129341135808257977885219 := by
  unfold tailWord_6598152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120327186996014826745818355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160436249328019768994424473 120327186996014826745818355)
  ·
    refine ⟨180490780494022240118727533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120327186996014826745818355 180490780494022240118727533)
    ·
      refine ⟨67684042685258340044522825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180490780494022240118727533 67684042685258340044522825)
      ·
        refine ⟨50763032013943755033392119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67684042685258340044522825 50763032013943755033392119)
        ·
          refine ⟨76144548020915632550088179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50763032013943755033392119 76144548020915632550088179)
          ·
            refine ⟨114216822031373448825132269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76144548020915632550088179 114216822031373448825132269)
            ·
              refine ⟨42831308261765043309424601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114216822031373448825132269 42831308261765043309424601)
              ·
                refine ⟨32123481196323782482068451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42831308261765043309424601 32123481196323782482068451)
                ·
                  refine ⟨48185221794485673723102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32123481196323782482068451 48185221794485673723102677)
                  ·
                    refine ⟨1129341135808257977885219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48185221794485673723102677 1129341135808257977885219)
                    ·
                      rfl

theorem cell23_6598152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6598152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598152 prefixEnd_6598152 := by exact prefixLift 6598152
  have htrace : WordTrace (prefixWord ++ tailWord_6598152) baseStart_6598152 baseEnd_6598152 := by
    simpa [prefixWord, tailWord_6598152, baseEnd_6598152] using wordTrace_append hprefix tailTrace_6598152
  have hstable : (prefixWord ++ tailWord_6598152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598152).length < 2 ^ (prefixWord ++ tailWord_6598152).sum := by decide
  have hdescent : baseEnd_6598152 < baseStart_6598152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598226 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_6598226 : Nat := 118140960795 + 6598226 * 2 ^ 59
def prefixEnd_6598226 : Nat := 4983230072969 + 3 ^ 40 * 6598226 * 2
def baseEnd_6598226 : Nat := 3388061404993206644130317

theorem tailTrace_6598226 : CollatzResearch.WordTrace tailWord_6598226 prefixEnd_6598226 3388061404993206644130317 := by
  unfold tailWord_6598226
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164268248440391032457633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160438048662507709419887021 60164268248440391032457633)
  ·
    refine ⟨45123201186330293274343225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60164268248440391032457633 45123201186330293274343225)
    ·
      refine ⟨33842400889747719955757419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45123201186330293274343225 33842400889747719955757419)
      ·
        refine ⟨50763601334621579933636129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33842400889747719955757419 50763601334621579933636129)
        ·
          refine ⟨38072701000966184950227097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50763601334621579933636129 38072701000966184950227097)
          ·
            refine ⟨28554525750724638712670323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38072701000966184950227097 28554525750724638712670323)
            ·
              refine ⟨42831788626086958069005485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28554525750724638712670323 42831788626086958069005485)
              ·
                refine ⟨16061920734782609275877057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42831788626086958069005485 16061920734782609275877057)
                ·
                  refine ⟨12046440551086956956907793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16061920734782609275877057 12046440551086956956907793)
                  ·
                    refine ⟨9034830413315217717680845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12046440551086956956907793 9034830413315217717680845)
                    ·
                      refine ⟨3388061404993206644130317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034830413315217717680845 3388061404993206644130317)
                      ·
                        rfl

theorem cell23_6598226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_6598226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598226 prefixEnd_6598226 := by exact prefixLift 6598226
  have htrace : WordTrace (prefixWord ++ tailWord_6598226) baseStart_6598226 baseEnd_6598226 := by
    simpa [prefixWord, tailWord_6598226, baseEnd_6598226] using wordTrace_append hprefix tailTrace_6598226
  have hstable : (prefixWord ++ tailWord_6598226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598226).length < 2 ^ (prefixWord ++ tailWord_6598226).sum := by decide
  have hdescent : baseEnd_6598226 < baseStart_6598226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6598232 : Nat := 118140960795 + 6598232 * 2 ^ 59
def prefixEnd_6598232 : Nat := 4983230072969 + 3 ^ 40 * 6598232 * 2
def baseEnd_6598232 : Nat := 3388064485877133620655289

theorem tailTrace_6598232 : CollatzResearch.WordTrace tailWord_6598232 prefixEnd_6598232 3388064485877133620655289 := by
  unfold tailWord_6598232
  simp only [CollatzResearch.WordTrace]
  refine ⟨120328645915869913577274475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160438194554493218103032633 120328645915869913577274475)
  ·
    refine ⟨180492968873804870365911713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120328645915869913577274475 180492968873804870365911713)
    ·
      refine ⟨135369726655353652774433785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180492968873804870365911713 135369726655353652774433785)
      ·
        refine ⟨101527294991515239580825339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135369726655353652774433785 101527294991515239580825339)
        ·
          refine ⟨152290942487272859371238009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101527294991515239580825339 152290942487272859371238009)
          ·
            refine ⟨114218206865454644528428507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152290942487272859371238009 114218206865454644528428507)
            ·
              refine ⟨171327310298181966792642761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114218206865454644528428507 171327310298181966792642761)
              ·
                refine ⟨128495482723636475094482071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171327310298181966792642761 128495482723636475094482071)
                ·
                  refine ⟨192743224085454712641723107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128495482723636475094482071 192743224085454712641723107)
                  ·
                    refine ⟨289114836128182068962584661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192743224085454712641723107 289114836128182068962584661)
                    ·
                      refine ⟨3388064485877133620655289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289114836128182068962584661 3388064485877133620655289)
                      ·
                        rfl

theorem cell23_6598232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6598232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598232 prefixEnd_6598232 := by exact prefixLift 6598232
  have htrace : WordTrace (prefixWord ++ tailWord_6598232) baseStart_6598232 baseEnd_6598232 := by
    simpa [prefixWord, tailWord_6598232, baseEnd_6598232] using wordTrace_append hprefix tailTrace_6598232
  have hstable : (prefixWord ++ tailWord_6598232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598232).length < 2 ^ (prefixWord ++ tailWord_6598232).sum := by decide
  have hdescent : baseEnd_6598232 < baseStart_6598232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598250 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_6598250 : Nat := 118140960795 + 6598250 * 2 ^ 59
def prefixEnd_6598250 : Nat := 4983230072969 + 3 ^ 40 * 6598250 * 2
def baseEnd_6598250 : Nat := 1129357909509638183410069

theorem tailTrace_6598250 : CollatzResearch.WordTrace tailWord_6598250 prefixEnd_6598250 1129357909509638183410069 := by
  unfold tailWord_6598250
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164487086418654057176051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160438632230449744152469469 60164487086418654057176051)
  ·
    refine ⟨90246730629627981085764077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60164487086418654057176051 90246730629627981085764077)
    ·
      refine ⟨33842523986110492907161529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90246730629627981085764077 33842523986110492907161529)
      ·
        refine ⟨25381892989582869680371147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33842523986110492907161529 25381892989582869680371147)
        ·
          refine ⟨38072839484374304520556721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25381892989582869680371147 38072839484374304520556721)
          ·
            refine ⟨28554629613280728390417541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38072839484374304520556721 28554629613280728390417541)
            ·
              refine ⟨5353993052490136573203289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28554629613280728390417541 5353993052490136573203289)
              ·
                refine ⟨4015494789367602429902467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353993052490136573203289 4015494789367602429902467)
                ·
                  refine ⟨6023242184051403644853701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015494789367602429902467 6023242184051403644853701)
                  ·
                    refine ⟨1129357909509638183410069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023242184051403644853701 1129357909509638183410069)
                    ·
                      rfl

theorem cell23_6598250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_6598250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598250 prefixEnd_6598250 := by exact prefixLift 6598250
  have htrace : WordTrace (prefixWord ++ tailWord_6598250) baseStart_6598250 baseEnd_6598250 := by
    simpa [prefixWord, tailWord_6598250, baseEnd_6598250] using wordTrace_append hprefix tailTrace_6598250
  have hstable : (prefixWord ++ tailWord_6598250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598250).length < 2 ^ (prefixWord ++ tailWord_6598250).sum := by decide
  have hdescent : baseEnd_6598250 < baseStart_6598250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598273 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_6598273 : Nat := 118140960795 + 6598273 * 2 ^ 59
def prefixEnd_6598273 : Nat := 4983230072969 + 3 ^ 40 * 6598273 * 2
def baseEnd_6598273 : Nat := 3388085538583967960242601

theorem tailTrace_6598273 : CollatzResearch.WordTrace tailWord_6598273 prefixEnd_6598273 3388085538583967960242601 := by
  unfold tailWord_6598273
  simp only [CollatzResearch.WordTrace]
  refine ⟨240658787224591291156791473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160439191483060860771194315 240658787224591291156791473)
  ·
    refine ⟨180494090418443468367593605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240658787224591291156791473 180494090418443468367593605)
    ·
      refine ⟨33842641953458150318923801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180494090418443468367593605 33842641953458150318923801)
      ·
        refine ⟨25381981465093612739192851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33842641953458150318923801 25381981465093612739192851)
        ·
          refine ⟨38072972197640419108789277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25381981465093612739192851 38072972197640419108789277)
          ·
            refine ⟨14277364574115157165795979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38072972197640419108789277 14277364574115157165795979)
            ·
              refine ⟨21416046861172735748693969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14277364574115157165795979 21416046861172735748693969)
              ·
                refine ⟨16062035145879551811520477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21416046861172735748693969 16062035145879551811520477)
                ·
                  refine ⟨6023263179704831929320179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16062035145879551811520477 6023263179704831929320179)
                  ·
                    refine ⟨9034894769557247893980269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6023263179704831929320179 9034894769557247893980269)
                    ·
                      refine ⟨3388085538583967960242601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034894769557247893980269 3388085538583967960242601)
                      ·
                        rfl

theorem cell23_6598273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_6598273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598273 prefixEnd_6598273 := by exact prefixLift 6598273
  have htrace : WordTrace (prefixWord ++ tailWord_6598273) baseStart_6598273 baseEnd_6598273 := by
    simpa [prefixWord, tailWord_6598273, baseEnd_6598273] using wordTrace_append hprefix tailTrace_6598273
  have hstable : (prefixWord ++ tailWord_6598273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598273).length < 2 ^ (prefixWord ++ tailWord_6598273).sum := by decide
  have hdescent : baseEnd_6598273 < baseStart_6598273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598309 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_6598309 : Nat := 118140960795 + 6598309 * 2 ^ 59
def prefixEnd_6598309 : Nat := 4983230072969 + 3 ^ 40 * 6598309 * 2
def baseEnd_6598309 : Nat := 3388104023887529819392435

theorem tailTrace_6598309 : CollatzResearch.WordTrace tailWord_6598309 prefixEnd_6598309 3388104023887529819392435 := by
  unfold tailWord_6598309
  simp only [CollatzResearch.WordTrace]
  refine ⟨240660100252460869305101981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160440066834973912870067987 240660100252460869305101981)
  ·
    refine ⟨90247537594672825989413243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240660100252460869305101981 90247537594672825989413243)
    ·
      refine ⟨135371306392009238984119865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90247537594672825989413243 135371306392009238984119865)
      ·
        refine ⟨101528479794006929238089899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135371306392009238984119865 101528479794006929238089899)
        ·
          refine ⟨152292719691010393857134849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101528479794006929238089899 152292719691010393857134849)
          ·
            refine ⟨114219539768257795392851137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152292719691010393857134849 114219539768257795392851137)
            ·
              refine ⟨85664654826193346544638353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114219539768257795392851137 85664654826193346544638353)
              ·
                refine ⟨64248491119645009908478765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85664654826193346544638353 64248491119645009908478765)
                ·
                  refine ⟨24093184169866878715679537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64248491119645009908478765 24093184169866878715679537)
                  ·
                    refine ⟨18069888127400159036759653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24093184169866878715679537 18069888127400159036759653)
                    ·
                      refine ⟨3388104023887529819392435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18069888127400159036759653 3388104023887529819392435)
                      ·
                        rfl

theorem cell23_6598309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_6598309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598309 prefixEnd_6598309 := by exact prefixLift 6598309
  have htrace : WordTrace (prefixWord ++ tailWord_6598309) baseStart_6598309 baseEnd_6598309 := by
    simpa [prefixWord, tailWord_6598309, baseEnd_6598309] using wordTrace_append hprefix tailTrace_6598309
  have hstable : (prefixWord ++ tailWord_6598309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598309).length < 2 ^ (prefixWord ++ tailWord_6598309).sum := by decide
  have hdescent : baseEnd_6598309 < baseStart_6598309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598323 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 2, 4]
def baseStart_6598323 : Nat := 118140960795 + 6598323 * 2 ^ 59
def prefixEnd_6598323 : Nat := 4983230072969 + 3 ^ 40 * 6598323 * 2
def baseEnd_6598323 : Nat := 1129370404205564254872457

theorem tailTrace_6598323 : CollatzResearch.WordTrace tailWord_6598323 prefixEnd_6598323 1129370404205564254872457 := by
  unfold tailWord_6598323
  simp only [CollatzResearch.WordTrace]
  refine ⟨240660610874410149696111623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160440407249606766464074415 240660610874410149696111623)
  ·
    refine ⟨360990916311615224544167435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240660610874410149696111623 360990916311615224544167435)
    ·
      refine ⟨541486374467422836816251153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360990916311615224544167435 541486374467422836816251153)
      ·
        refine ⟨406114780850567127612188365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541486374467422836816251153 406114780850567127612188365)
        ·
          refine ⟨152293042818962672854570637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406114780850567127612188365 152293042818962672854570637)
          ·
            refine ⟨57109891057111002320463989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152293042818962672854570637 57109891057111002320463989)
            ·
              refine ⟨5354052286604156467543499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57109891057111002320463989 5354052286604156467543499)
              ·
                refine ⟨8031078429906234701315249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354052286604156467543499 8031078429906234701315249)
                ·
                  refine ⟨6023308822429676025986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8031078429906234701315249 6023308822429676025986437)
                  ·
                    refine ⟨1129370404205564254872457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023308822429676025986437 1129370404205564254872457)
                    ·
                      rfl

theorem cell23_6598323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 4].length) (baseStart_6598323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598323 prefixEnd_6598323 := by exact prefixLift 6598323
  have htrace : WordTrace (prefixWord ++ tailWord_6598323) baseStart_6598323 baseEnd_6598323 := by
    simpa [prefixWord, tailWord_6598323, baseEnd_6598323] using wordTrace_append hprefix tailTrace_6598323
  have hstable : (prefixWord ++ tailWord_6598323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598323).length < 2 ^ (prefixWord ++ tailWord_6598323).sum := by decide
  have hdescent : baseEnd_6598323 < baseStart_6598323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598333 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6598333 : Nat := 118140960795 + 6598333 * 2 ^ 59
def prefixEnd_6598333 : Nat := 4983230072969 + 3 ^ 40 * 6598333 * 2
def baseEnd_6598333 : Nat := 3388116347423237725492325

theorem tailTrace_6598333 : CollatzResearch.WordTrace tailWord_6598333 prefixEnd_6598333 3388116347423237725492325 := by
  unfold tailWord_6598333
  simp only [CollatzResearch.WordTrace]
  refine ⟨240660975604373921403975653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160440650402915947602650435 240660975604373921403975653)
  ·
    refine ⟨45123932925820110263245435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240660975604373921403975653 45123932925820110263245435)
    ·
      refine ⟨67685899388730165394868153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45123932925820110263245435 67685899388730165394868153)
      ·
        refine ⟨50764424541547624046151115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67685899388730165394868153 50764424541547624046151115)
        ·
          refine ⟨76146636812321436069226673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50764424541547624046151115 76146636812321436069226673)
          ·
            refine ⟨57109977609241077051920005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76146636812321436069226673 57109977609241077051920005)
            ·
              refine ⟨10708120801732701947235001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57109977609241077051920005 10708120801732701947235001)
              ·
                refine ⟨8031090601299526460426251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10708120801732701947235001 8031090601299526460426251)
                ·
                  refine ⟨12046635901949289690639377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031090601299526460426251 12046635901949289690639377)
                  ·
                    refine ⟨9034976926461967267979533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12046635901949289690639377 9034976926461967267979533)
                    ·
                      refine ⟨3388116347423237725492325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034976926461967267979533 3388116347423237725492325)
                      ·
                        rfl

theorem cell23_6598333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6598333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598333 prefixEnd_6598333 := by exact prefixLift 6598333
  have htrace : WordTrace (prefixWord ++ tailWord_6598333) baseStart_6598333 baseEnd_6598333 := by
    simpa [prefixWord, tailWord_6598333, baseEnd_6598333] using wordTrace_append hprefix tailTrace_6598333
  have hstable : (prefixWord ++ tailWord_6598333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598333).length < 2 ^ (prefixWord ++ tailWord_6598333).sum := by decide
  have hdescent : baseEnd_6598333 < baseStart_6598333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598359 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_6598359 : Nat := 118140960795 + 6598359 * 2 ^ 59
def prefixEnd_6598359 : Nat := 4983230072969 + 3 ^ 40 * 6598359 * 2
def baseEnd_6598359 : Nat := 3388129697920254623767205

theorem tailTrace_6598359 : CollatzResearch.WordTrace tailWord_6598359 prefixEnd_6598359 3388129697920254623767205 := by
  unfold tailWord_6598359
  simp only [CollatzResearch.WordTrace]
  refine ⟨240661923902279727844422131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160441282601519818562948087 240661923902279727844422131)
  ·
    refine ⟨360992885853419591766633197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240661923902279727844422131 360992885853419591766633197)
    ·
      refine ⟨135372332195032346912487449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360992885853419591766633197 135372332195032346912487449)
      ·
        refine ⟨101529249146274260184365587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135372332195032346912487449 101529249146274260184365587)
        ·
          refine ⟨152293873719411390276548381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101529249146274260184365587 152293873719411390276548381)
          ·
            refine ⟨57110202644779271353705643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152293873719411390276548381 57110202644779271353705643)
            ·
              refine ⟨85665303967168907030558465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57110202644779271353705643 85665303967168907030558465)
              ·
                refine ⟨64248977975376680272918849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85665303967168907030558465 64248977975376680272918849)
                ·
                  refine ⟨48186733481532510204689137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64248977975376680272918849 48186733481532510204689137)
                  ·
                    refine ⟨36140050111149382653516853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48186733481532510204689137 36140050111149382653516853)
                    ·
                      refine ⟨3388129697920254623767205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36140050111149382653516853 3388129697920254623767205)
                      ·
                        rfl

theorem cell23_6598359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_6598359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598359 prefixEnd_6598359 := by exact prefixLift 6598359
  have htrace : WordTrace (prefixWord ++ tailWord_6598359) baseStart_6598359 baseEnd_6598359 := by
    simpa [prefixWord, tailWord_6598359, baseEnd_6598359] using wordTrace_append hprefix tailTrace_6598359
  have hstable : (prefixWord ++ tailWord_6598359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598359).length < 2 ^ (prefixWord ++ tailWord_6598359).sum := by decide
  have hdescent : baseEnd_6598359 < baseStart_6598359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598364 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6598364 : Nat := 118140960795 + 6598364 * 2 ^ 59
def prefixEnd_6598364 : Nat := 4983230072969 + 3 ^ 40 * 6598364 * 2
def baseEnd_6598364 : Nat := 3388132265323527104204683

theorem tailTrace_6598364 : CollatzResearch.WordTrace tailWord_6598364 prefixEnd_6598364 3388132265323527104204683 := by
  unfold tailWord_6598364
  simp only [CollatzResearch.WordTrace]
  refine ⟨120331053133630806849177073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160441404178174409132236097 120331053133630806849177073)
  ·
    refine ⟨90248289850223105136882805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120331053133630806849177073 90248289850223105136882805)
    ·
      refine ⟨8460777173458416106582763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90248289850223105136882805 8460777173458416106582763)
      ·
        refine ⟨12691165760187624159874145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460777173458416106582763 12691165760187624159874145)
        ·
          refine ⟨9518374320140718119905609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691165760187624159874145 9518374320140718119905609)
          ·
            refine ⟨7138780740105538589929207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9518374320140718119905609 7138780740105538589929207)
            ·
              refine ⟨10708171110158307884893811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138780740105538589929207 10708171110158307884893811)
              ·
                refine ⟨16062256665237461827340717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10708171110158307884893811 16062256665237461827340717)
                ·
                  refine ⟨6023346249464048185252769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16062256665237461827340717 6023346249464048185252769)
                  ·
                    refine ⟨4517509687098036138939577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023346249464048185252769 4517509687098036138939577)
                    ·
                      refine ⟨3388132265323527104204683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517509687098036138939577 3388132265323527104204683)
                      ·
                        rfl

theorem cell23_6598364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6598364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598364 prefixEnd_6598364 := by exact prefixLift 6598364
  have htrace : WordTrace (prefixWord ++ tailWord_6598364) baseStart_6598364 baseEnd_6598364 := by
    simpa [prefixWord, tailWord_6598364, baseEnd_6598364] using wordTrace_append hprefix tailTrace_6598364
  have hstable : (prefixWord ++ tailWord_6598364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598364).length < 2 ^ (prefixWord ++ tailWord_6598364).sum := by decide
  have hdescent : baseEnd_6598364 < baseStart_6598364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598373 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6598373 : Nat := 118140960795 + 6598373 * 2 ^ 59
def prefixEnd_6598373 : Nat := 4983230072969 + 3 ^ 40 * 6598373 * 2
def baseEnd_6598373 : Nat := 3388136886649417568992141

theorem tailTrace_6598373 : CollatzResearch.WordTrace tailWord_6598373 prefixEnd_6598373 3388136886649417568992141 := by
  unfold tailWord_6598373
  simp only [CollatzResearch.WordTrace]
  refine ⟨240662434524229008235431773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160441623016152672156954515 240662434524229008235431773)
  ·
    refine ⟨90248412946585878088286915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240662434524229008235431773 90248412946585878088286915)
    ·
      refine ⟨135372619419878817132430373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90248412946585878088286915 135372619419878817132430373)
      ·
        refine ⟨25382366141227278212330695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135372619419878817132430373 25382366141227278212330695)
        ·
          refine ⟨38073549211840917318496043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25382366141227278212330695 38073549211840917318496043)
          ·
            refine ⟨57110323817761375977744065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38073549211840917318496043 57110323817761375977744065)
            ·
              refine ⟨42832742863321031983308049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57110323817761375977744065 42832742863321031983308049)
              ·
                refine ⟨32124557147490773987481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42832742863321031983308049 32124557147490773987481037)
                ·
                  refine ⟨12046708930309040245305389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32124557147490773987481037 12046708930309040245305389)
                  ·
                    refine ⟨4517515848865890091989521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12046708930309040245305389 4517515848865890091989521)
                    ·
                      refine ⟨3388136886649417568992141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517515848865890091989521 3388136886649417568992141)
                      ·
                        rfl

theorem cell23_6598373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6598373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598373 prefixEnd_6598373 := by exact prefixLift 6598373
  have htrace : WordTrace (prefixWord ++ tailWord_6598373) baseStart_6598373 baseEnd_6598373 := by
    simpa [prefixWord, tailWord_6598373, baseEnd_6598373] using wordTrace_append hprefix tailTrace_6598373
  have hstable : (prefixWord ++ tailWord_6598373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598373).length < 2 ^ (prefixWord ++ tailWord_6598373).sum := by decide
  have hdescent : baseEnd_6598373 < baseStart_6598373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598379 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 6]
def baseStart_6598379 : Nat := 118140960795 + 6598379 * 2 ^ 59
def prefixEnd_6598379 : Nat := 4983230072969 + 3 ^ 40 * 6598379 * 2
def baseEnd_6598379 : Nat := 1129379989177781515172371

theorem tailTrace_6598379 : CollatzResearch.WordTrace tailWord_6598379 prefixEnd_6598379 1129379989177781515172371 := by
  unfold tailWord_6598379
  simp only [CollatzResearch.WordTrace]
  refine ⟨240662653362207271260150191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160441768908138180840100127 240662653362207271260150191)
  ·
    refine ⟨360993980043310906890225287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240662653362207271260150191 360993980043310906890225287)
    ·
      refine ⟨541490970064966360335337931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360993980043310906890225287 541490970064966360335337931)
      ·
        refine ⟨812236455097449540503006897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541490970064966360335337931 812236455097449540503006897)
        ·
          refine ⟨609177341323087155377255173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812236455097449540503006897 609177341323087155377255173)
          ·
            refine ⟨114220751498078841633235345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609177341323087155377255173 114220751498078841633235345)
            ·
              refine ⟨85665563623559131224926509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114220751498078841633235345 85665563623559131224926509)
              ·
                refine ⟨32124586358834674209347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85665563623559131224926509 32124586358834674209347441)
                ·
                  refine ⟨24093439769126005657010581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32124586358834674209347441 24093439769126005657010581)
                  ·
                    refine ⟨1129379989177781515172371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24093439769126005657010581 1129379989177781515172371)
                    ·
                      rfl

theorem cell23_6598379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_6598379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598379 prefixEnd_6598379 := by exact prefixLift 6598379
  have htrace : WordTrace (prefixWord ++ tailWord_6598379) baseStart_6598379 baseEnd_6598379 := by
    simpa [prefixWord, tailWord_6598379, baseEnd_6598379] using wordTrace_append hprefix tailTrace_6598379
  have hstable : (prefixWord ++ tailWord_6598379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598379).length < 2 ^ (prefixWord ++ tailWord_6598379).sum := by decide
  have hdescent : baseEnd_6598379 < baseStart_6598379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598380 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 3]
def baseStart_6598380 : Nat := 118140960795 + 6598380 * 2 ^ 59
def prefixEnd_6598380 : Nat := 4983230072969 + 3 ^ 40 * 6598380 * 2
def baseEnd_6598380 : Nat := 3388140481013999041604609

theorem tailTrace_6598380 : CollatzResearch.WordTrace tailWord_6598380 prefixEnd_6598380 3388140481013999041604609 := by
  unfold tailWord_6598380
  simp only [CollatzResearch.WordTrace]
  refine ⟨120331344917601824215468297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160441793223469098953957729 120331344917601824215468297)
  ·
    refine ⟨90248508688201368161601223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120331344917601824215468297 90248508688201368161601223)
    ·
      refine ⟨135372763032302052242401835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90248508688201368161601223 135372763032302052242401835)
      ·
        refine ⟨203059144548453078363602753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135372763032302052242401835 203059144548453078363602753)
        ·
          refine ⟨152294358411339808772702065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203059144548453078363602753 152294358411339808772702065)
          ·
            refine ⟨114220768808504856579526549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152294358411339808772702065 114220768808504856579526549)
            ·
              refine ⟨5354098537898665152165307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114220768808504856579526549 5354098537898665152165307)
              ·
                refine ⟨8031147806847997728247961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354098537898665152165307 8031147806847997728247961)
                ·
                  refine ⟨6023360855135998296185971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8031147806847997728247961 6023360855135998296185971)
                  ·
                    refine ⟨9035041282703997444278957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6023360855135998296185971 9035041282703997444278957)
                    ·
                      refine ⟨3388140481013999041604609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035041282703997444278957 3388140481013999041604609)
                      ·
                        rfl

theorem cell23_6598380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_6598380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598380 prefixEnd_6598380 := by exact prefixLift 6598380
  have htrace : WordTrace (prefixWord ++ tailWord_6598380) baseStart_6598380 baseEnd_6598380 := by
    simpa [prefixWord, tailWord_6598380, baseEnd_6598380] using wordTrace_append hprefix tailTrace_6598380
  have hstable : (prefixWord ++ tailWord_6598380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598380).length < 2 ^ (prefixWord ++ tailWord_6598380).sum := by decide
  have hdescent : baseEnd_6598380 < baseStart_6598380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598390 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6598390 : Nat := 118140960795 + 6598390 * 2 ^ 59
def prefixEnd_6598390 : Nat := 4983230072969 + 3 ^ 40 * 6598390 * 2
def baseEnd_6598390 : Nat := 3388145615820544002479563

theorem tailTrace_6598390 : CollatzResearch.WordTrace tailWord_6598390 prefixEnd_6598390 3388145615820544002479563 := by
  unfold tailWord_6598390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041440910322963758675039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160442036376778280092533749 15041440910322963758675039)
  ·
    refine ⟨22562161365484445638012559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15041440910322963758675039 22562161365484445638012559)
    ·
      refine ⟨33843242048226668457018839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22562161365484445638012559 33843242048226668457018839)
      ·
        refine ⟨50764863072340002685528259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33843242048226668457018839 50764863072340002685528259)
        ·
          refine ⟨76147294608510004028292389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50764863072340002685528259 76147294608510004028292389)
          ·
            refine ⟨14277617739095625755304823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76147294608510004028292389 14277617739095625755304823)
            ·
              refine ⟨21416426608643438632957235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14277617739095625755304823 21416426608643438632957235)
              ·
                refine ⟨32124639912965157949435853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21416426608643438632957235 32124639912965157949435853)
                ·
                  refine ⟨12046739967361934231038445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32124639912965157949435853 12046739967361934231038445)
                  ·
                    refine ⟨4517527487760725336639417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12046739967361934231038445 4517527487760725336639417)
                    ·
                      refine ⟨3388145615820544002479563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517527487760725336639417 3388145615820544002479563)
                      ·
                        rfl

theorem cell23_6598390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6598390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598390 prefixEnd_6598390 := by exact prefixLift 6598390
  have htrace : WordTrace (prefixWord ++ tailWord_6598390) baseStart_6598390 baseEnd_6598390 := by
    simpa [prefixWord, tailWord_6598390, baseEnd_6598390] using wordTrace_append hprefix tailTrace_6598390
  have hstable : (prefixWord ++ tailWord_6598390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598390).length < 2 ^ (prefixWord ++ tailWord_6598390).sum := by decide
  have hdescent : baseEnd_6598390 < baseStart_6598390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598403 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 6, 2, 2]
def baseStart_6598403 : Nat := 118140960795 + 6598403 * 2 ^ 59
def prefixEnd_6598403 : Nat := 4983230072969 + 3 ^ 40 * 6598403 * 2
def baseEnd_6598403 : Nat := 3388152291069052451617003

theorem tailTrace_6598403 : CollatzResearch.WordTrace tailWord_6598403 prefixEnd_6598403 3388152291069052451617003 := by
  unfold tailWord_6598403
  simp only [CollatzResearch.WordTrace]
  refine ⟨240663528714120323359023863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160442352476080215572682575 240663528714120323359023863)
  ·
    refine ⟨360995293071180485038535795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240663528714120323359023863 360995293071180485038535795)
    ·
      refine ⟨541492939606770727557803693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360995293071180485038535795 541492939606770727557803693)
      ·
        refine ⟨203059852352539022834176385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541492939606770727557803693 203059852352539022834176385)
        ·
          refine ⟨152294889264404267125632289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203059852352539022834176385 152294889264404267125632289)
          ·
            refine ⟨114221166948303200344224217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152294889264404267125632289 114221166948303200344224217)
            ·
              refine ⟨85665875211227400258168163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114221166948303200344224217 85665875211227400258168163)
              ·
                refine ⟨128498812816841100387252245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85665875211227400258168163 128498812816841100387252245)
                ·
                  refine ⟨6023381850789426580652449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128498812816841100387252245 6023381850789426580652449)
                  ·
                    refine ⟨4517536388092069935489337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023381850789426580652449 4517536388092069935489337)
                    ·
                      refine ⟨3388152291069052451617003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517536388092069935489337 3388152291069052451617003)
                      ·
                        rfl

theorem cell23_6598403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_6598403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598403 prefixEnd_6598403 := by exact prefixLift 6598403
  have htrace : WordTrace (prefixWord ++ tailWord_6598403) baseStart_6598403 baseEnd_6598403 := by
    simpa [prefixWord, tailWord_6598403, baseEnd_6598403] using wordTrace_append hprefix tailTrace_6598403
  have hstable : (prefixWord ++ tailWord_6598403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598403).length < 2 ^ (prefixWord ++ tailWord_6598403).sum := by decide
  have hdescent : baseEnd_6598403 < baseStart_6598403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598456 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_6598456 : Nat := 118140960795 + 6598456 * 2 ^ 59
def prefixEnd_6598456 : Nat := 4983230072969 + 3 ^ 40 * 6598456 * 2
def baseEnd_6598456 : Nat := 1129393168514580248084753

theorem tailTrace_6598456 : CollatzResearch.WordTrace tailWord_6598456 prefixEnd_6598456 1129393168514580248084753 := by
  unfold tailWord_6598456
  simp only [CollatzResearch.WordTrace]
  refine ⟨120332730891464156705351611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160443641188618875607135481 120332730891464156705351611)
  ·
    refine ⟨180499096337196235058027417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120332730891464156705351611 180499096337196235058027417)
    ·
      refine ⟨135374322252897176293520563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180499096337196235058027417 135374322252897176293520563)
      ·
        refine ⟨203061483379345764440280845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135374322252897176293520563 203061483379345764440280845)
        ·
          refine ⟨76148056267254661665105317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203061483379345764440280845 76148056267254661665105317)
          ·
            refine ⟨14277760550110249062207247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76148056267254661665105317 14277760550110249062207247)
            ·
              refine ⟨21416640825165373593310871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14277760550110249062207247 21416640825165373593310871)
              ·
                refine ⟨32124961237748060389966307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21416640825165373593310871 32124961237748060389966307)
                ·
                  refine ⟨48187441856622090584949461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32124961237748060389966307 48187441856622090584949461)
                  ·
                    refine ⟨1129393168514580248084753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48187441856622090584949461 1129393168514580248084753)
                    ·
                      rfl

theorem cell23_6598456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_6598456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598456 prefixEnd_6598456 := by exact prefixLift 6598456
  have htrace : WordTrace (prefixWord ++ tailWord_6598456) baseStart_6598456 baseEnd_6598456 := by
    simpa [prefixWord, tailWord_6598456, baseEnd_6598456] using wordTrace_append hprefix tailTrace_6598456
  have hstable : (prefixWord ++ tailWord_6598456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598456).length < 2 ^ (prefixWord ++ tailWord_6598456).sum := by decide
  have hdescent : baseEnd_6598456 < baseStart_6598456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598503 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 3, 4]
def baseStart_6598503 : Nat := 118140960795 + 6598503 * 2 ^ 59
def prefixEnd_6598503 : Nat := 4983230072969 + 3 ^ 40 * 6598503 * 2
def baseEnd_6598503 : Nat := 1129401213044834020122181

theorem tailTrace_6598503 : CollatzResearch.WordTrace tailWord_6598503 prefixEnd_6598503 1129401213044834020122181 := by
  unfold tailWord_6598503
  simp only [CollatzResearch.WordTrace]
  refine ⟨240667176013758040437664163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160444784009172026958442775 240667176013758040437664163)
  ·
    refine ⟨361000764020637060656496245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240667176013758040437664163 361000764020637060656496245)
    ·
      refine ⟨33843821626934724436546523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361000764020637060656496245 33843821626934724436546523)
      ·
        refine ⟨50765732440402086654819785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33843821626934724436546523 50765732440402086654819785)
        ·
          refine ⟨38074299330301564991114839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50765732440402086654819785 38074299330301564991114839)
          ·
            refine ⟨57111448995452347486672259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38074299330301564991114839 57111448995452347486672259)
            ·
              refine ⟨85667173493178521230008389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57111448995452347486672259 85667173493178521230008389)
              ·
                refine ⟨16062595029970972730626573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85667173493178521230008389 16062595029970972730626573)
                ·
                  refine ⟨6023473136239114773984965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16062595029970972730626573 6023473136239114773984965)
                  ·
                    refine ⟨1129401213044834020122181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023473136239114773984965 1129401213044834020122181)
                    ·
                      rfl

theorem cell23_6598503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_6598503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598503 prefixEnd_6598503 := by exact prefixLift 6598503
  have htrace : WordTrace (prefixWord ++ tailWord_6598503) baseStart_6598503 baseEnd_6598503 := by
    simpa [prefixWord, tailWord_6598503, baseEnd_6598503] using wordTrace_append hprefix tailTrace_6598503
  have hstable : (prefixWord ++ tailWord_6598503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598503).length < 2 ^ (prefixWord ++ tailWord_6598503).sum := by decide
  have hdescent : baseEnd_6598503 < baseStart_6598503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598513 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_6598513 : Nat := 118140960795 + 6598513 * 2 ^ 59
def prefixEnd_6598513 : Nat := 4983230072969 + 3 ^ 40 * 6598513 * 2
def baseEnd_6598513 : Nat := 3388208773941047021241497

theorem tailTrace_6598513 : CollatzResearch.WordTrace tailWord_6598513 prefixEnd_6598513 3388208773941047021241497 := by
  unfold tailWord_6598513
  simp only [CollatzResearch.WordTrace]
  refine ⟨240667540743721812145528193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160445027162481208097018795 240667540743721812145528193)
  ·
    refine ⟨180500655557791359109146145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240667540743721812145528193 180500655557791359109146145)
    ·
      refine ⟨135375491668343519331859609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180500655557791359109146145 135375491668343519331859609)
      ·
        refine ⟨101531618751257639498894707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135375491668343519331859609 101531618751257639498894707)
        ·
          refine ⟨152297428126886459248342061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101531618751257639498894707 152297428126886459248342061)
          ·
            refine ⟨57111535547582422218128273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152297428126886459248342061 57111535547582422218128273)
            ·
              refine ⟨42833651660686816663596205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57111535547582422218128273 42833651660686816663596205)
              ·
                refine ⟨16062619372757556248848577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42833651660686816663596205 16062619372757556248848577)
                ·
                  refine ⟨12046964529568167186636433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16062619372757556248848577 12046964529568167186636433)
                  ·
                    refine ⟨9035223397176125389977325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12046964529568167186636433 9035223397176125389977325)
                    ·
                      refine ⟨3388208773941047021241497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035223397176125389977325 3388208773941047021241497)
                      ·
                        rfl

theorem cell23_6598513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_6598513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598513 prefixEnd_6598513 := by exact prefixLift 6598513
  have htrace : WordTrace (prefixWord ++ tailWord_6598513) baseStart_6598513 baseEnd_6598513 := by
    simpa [prefixWord, tailWord_6598513, baseEnd_6598513] using wordTrace_append hprefix tailTrace_6598513
  have hstable : (prefixWord ++ tailWord_6598513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598513).length < 2 ^ (prefixWord ++ tailWord_6598513).sum := by decide
  have hdescent : baseEnd_6598513 < baseStart_6598513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598537 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 1, 4]
def baseStart_6598537 : Nat := 118140960795 + 6598537 * 2 ^ 59
def prefixEnd_6598537 : Nat := 4983230072969 + 3 ^ 40 * 6598537 * 2
def baseEnd_6598537 : Nat := 1129407032492251642447129

theorem tailTrace_6598537 : CollatzResearch.WordTrace tailWord_6598537 prefixEnd_6598537 1129407032492251642447129 := by
  unfold tailWord_6598537
  simp only [CollatzResearch.WordTrace]
  refine ⟨240668416095634864244401865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160445610730423242829601243 240668416095634864244401865)
  ·
    refine ⟨180501312071726148183301399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240668416095634864244401865 180501312071726148183301399)
    ·
      refine ⟨270751968107589222274952099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180501312071726148183301399 270751968107589222274952099)
      ·
        refine ⟨406127952161383833412428149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270751968107589222274952099 406127952161383833412428149)
        ·
          refine ⟨38074495515129734382415139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406127952161383833412428149 38074495515129734382415139)
          ·
            refine ⟨57111743272694601573622709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38074495515129734382415139 57111743272694601573622709)
            ·
              refine ⟨5354225931815118897527129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57111743272694601573622709 5354225931815118897527129)
              ·
                refine ⟨4015669448861339173145347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354225931815118897527129 4015669448861339173145347)
                ·
                  refine ⟨6023504173292008759718021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015669448861339173145347 6023504173292008759718021)
                  ·
                    refine ⟨1129407032492251642447129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023504173292008759718021 1129407032492251642447129)
                    ·
                      rfl

theorem cell23_6598537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_6598537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598537 prefixEnd_6598537 := by exact prefixLift 6598537
  have htrace : WordTrace (prefixWord ++ tailWord_6598537) baseStart_6598537 baseEnd_6598537 := by
    simpa [prefixWord, tailWord_6598537, baseEnd_6598537] using wordTrace_append hprefix tailTrace_6598537
  have hstable : (prefixWord ++ tailWord_6598537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598537).length < 2 ^ (prefixWord ++ tailWord_6598537).sum := by decide
  have hdescent : baseEnd_6598537 < baseStart_6598537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598553 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 5, 2]
def baseStart_6598553 : Nat := 118140960795 + 6598553 * 2 ^ 59
def prefixEnd_6598553 : Nat := 4983230072969 + 3 ^ 40 * 6598553 * 2
def baseEnd_6598553 : Nat := 3388229313167226864741313

theorem tailTrace_6598553 : CollatzResearch.WordTrace tailWord_6598553 prefixEnd_6598553 3388229313167226864741313 := by
  unfold tailWord_6598553
  simp only [CollatzResearch.WordTrace]
  refine ⟨240668999663576898976984313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160445999775717932651322875 240668999663576898976984313)
  ·
    refine ⟨180501749747682674232738235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240668999663576898976984313 180501749747682674232738235)
    ·
      refine ⟨270752624621524011349107353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180501749747682674232738235 270752624621524011349107353)
      ·
        refine ⟨203064468466143008511830515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270752624621524011349107353 203064468466143008511830515)
        ·
          refine ⟨304596702699214512767745773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203064468466143008511830515 304596702699214512767745773)
          ·
            refine ⟨114223763512205442287904665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304596702699214512767745773 114223763512205442287904665)
            ·
              refine ⟨85667822634154081715928499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114223763512205442287904665 85667822634154081715928499)
              ·
                refine ⟨128501733951231122573892749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85667822634154081715928499 128501733951231122573892749)
                ·
                  refine ⟨48188150231711670965209781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128501733951231122573892749 48188150231711670965209781)
                  ·
                    refine ⟨4517639084222969152988417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48188150231711670965209781 4517639084222969152988417)
                    ·
                      refine ⟨3388229313167226864741313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517639084222969152988417 3388229313167226864741313)
                      ·
                        rfl

theorem cell23_6598553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_6598553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598553 prefixEnd_6598553 := by exact prefixLift 6598553
  have htrace : WordTrace (prefixWord ++ tailWord_6598553) baseStart_6598553 baseEnd_6598553 := by
    simpa [prefixWord, tailWord_6598553, baseEnd_6598553] using wordTrace_append hprefix tailTrace_6598553
  have hstable : (prefixWord ++ tailWord_6598553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598553).length < 2 ^ (prefixWord ++ tailWord_6598553).sum := by decide
  have hdescent : baseEnd_6598553 < baseStart_6598553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598588 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_6598588 : Nat := 118140960795 + 6598588 * 2 ^ 59
def prefixEnd_6598588 : Nat := 4983230072969 + 3 ^ 40 * 6598588 * 2
def baseEnd_6598588 : Nat := 1129415761663378075934551

theorem tailTrace_6598588 : CollatzResearch.WordTrace tailWord_6598588 prefixEnd_6598588 1129415761663378075934551 := by
  unfold tailWord_6598588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120335138109225049977254209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160446850812300066636338945 120335138109225049977254209)
  ·
    refine ⟨90251353581918787482940657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120335138109225049977254209 90251353581918787482940657)
    ·
      refine ⟨67688515186439090612205493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90251353581918787482940657 67688515186439090612205493)
      ·
        refine ⟨6345798298728664744894265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67688515186439090612205493 6345798298728664744894265)
        ·
          refine ⟨4759348724046498558670699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345798298728664744894265 4759348724046498558670699)
          ·
            refine ⟨7139023086069747838006049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759348724046498558670699 7139023086069747838006049)
            ·
              refine ⟨5354267314552310878504537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139023086069747838006049 5354267314552310878504537)
              ·
                refine ⟨4015700485914233158878403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354267314552310878504537 4015700485914233158878403)
                ·
                  refine ⟨6023550728871349738317605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015700485914233158878403 6023550728871349738317605)
                  ·
                    refine ⟨1129415761663378075934551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023550728871349738317605 1129415761663378075934551)
                    ·
                      rfl

theorem cell23_6598588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_6598588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598588 prefixEnd_6598588 := by exact prefixLift 6598588
  have htrace : WordTrace (prefixWord ++ tailWord_6598588) baseStart_6598588 baseEnd_6598588 := by
    simpa [prefixWord, tailWord_6598588, baseEnd_6598588] using wordTrace_append hprefix tailTrace_6598588
  have hstable : (prefixWord ++ tailWord_6598588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598588).length < 2 ^ (prefixWord ++ tailWord_6598588).sum := by decide
  have hdescent : baseEnd_6598588 < baseStart_6598588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598603 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3]
def baseStart_6598603 : Nat := 118140960795 + 6598603 * 2 ^ 59
def prefixEnd_6598603 : Nat := 4983230072969 + 3 ^ 40 * 6598603 * 2
def baseEnd_6598603 : Nat := 3388254987199951669116083

theorem tailTrace_6598603 : CollatzResearch.WordTrace tailWord_6598603 prefixEnd_6598603 3388254987199951669116083 := by
  unfold tailWord_6598603
  simp only [CollatzResearch.WordTrace]
  refine ⟨240670823313395757516304463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160447215542263838344202975 240670823313395757516304463)
  ·
    refine ⟨361006234970093636274456695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240670823313395757516304463 361006234970093636274456695)
    ·
      refine ⟨541509352455140454411685043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361006234970093636274456695 541509352455140454411685043)
      ·
        refine ⟨812264028682710681617527565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541509352455140454411685043 812264028682710681617527565)
        ·
          refine ⟨304599010756016505606572837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812264028682710681617527565 304599010756016505606572837)
          ·
            refine ⟨57112314516753094801232407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304599010756016505606572837 57112314516753094801232407)
            ·
              refine ⟨85668471775129642201848611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57112314516753094801232407 85668471775129642201848611)
              ·
                refine ⟨128502707662694463302772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85668471775129642201848611 128502707662694463302772917)
                ·
                  refine ⟨12047128843377605934634961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128502707662694463302772917 12047128843377605934634961)
                  ·
                    refine ⟨9035346632533204450976221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12047128843377605934634961 9035346632533204450976221)
                    ·
                      refine ⟨3388254987199951669116083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035346632533204450976221 3388254987199951669116083)
                      ·
                        rfl

theorem cell23_6598603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].length) (baseStart_6598603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598603 prefixEnd_6598603 := by exact prefixLift 6598603
  have htrace : WordTrace (prefixWord ++ tailWord_6598603) baseStart_6598603 baseEnd_6598603 := by
    simpa [prefixWord, tailWord_6598603, baseEnd_6598603] using wordTrace_append hprefix tailTrace_6598603
  have hstable : (prefixWord ++ tailWord_6598603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598603).length < 2 ^ (prefixWord ++ tailWord_6598603).sum := by decide
  have hdescent : baseEnd_6598603 < baseStart_6598603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598621 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6598621 : Nat := 118140960795 + 6598621 * 2 ^ 59
def prefixEnd_6598621 : Nat := 4983230072969 + 3 ^ 40 * 6598621 * 2
def baseEnd_6598621 : Nat := 3388264229851732598691001

theorem tailTrace_6598621 : CollatzResearch.WordTrace tailWord_6598621 prefixEnd_6598621 3388264229851732598691001 := by
  unfold tailWord_6598621
  simp only [CollatzResearch.WordTrace]
  refine ⟨240671479827330546590459717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160447653218220364393639811 240671479827330546590459717)
  ·
    refine ⟨45125902467624477485711197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240671479827330546590459717 45125902467624477485711197)
    ·
      refine ⟨16922213425359179057141699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45125902467624477485711197 16922213425359179057141699)
      ·
        refine ⟨25383320138038768585712549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922213425359179057141699 25383320138038768585712549)
        ·
          refine ⟨4759372525882269109821103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25383320138038768585712549 4759372525882269109821103)
          ·
            refine ⟨7139058788823403664731655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759372525882269109821103 7139058788823403664731655)
            ·
              refine ⟨10708588183235105497097483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139058788823403664731655 10708588183235105497097483)
              ·
                refine ⟨16062882274852658245646225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10708588183235105497097483 16062882274852658245646225)
                ·
                  refine ⟨12047161706139493684234669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16062882274852658245646225 12047161706139493684234669)
                  ·
                    refine ⟨4517685639802310131588001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12047161706139493684234669 4517685639802310131588001)
                    ·
                      refine ⟨3388264229851732598691001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517685639802310131588001 3388264229851732598691001)
                      ·
                        rfl

theorem cell23_6598621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6598621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598621 prefixEnd_6598621 := by exact prefixLift 6598621
  have htrace : WordTrace (prefixWord ++ tailWord_6598621) baseStart_6598621 baseEnd_6598621 := by
    simpa [prefixWord, tailWord_6598621, baseEnd_6598621] using wordTrace_append hprefix tailTrace_6598621
  have hstable : (prefixWord ++ tailWord_6598621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598621).length < 2 ^ (prefixWord ++ tailWord_6598621).sum := by decide
  have hdescent : baseEnd_6598621 < baseStart_6598621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598693 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_6598693 : Nat := 118140960795 + 6598693 * 2 ^ 59
def prefixEnd_6598693 : Nat := 4983230072969 + 3 ^ 40 * 6598693 * 2
def baseEnd_6598693 : Nat := 3388301200458856316990669

theorem tailTrace_6598693 : CollatzResearch.WordTrace tailWord_6598693 prefixEnd_6598693 3388301200458856316990669 := by
  unfold tailWord_6598693
  simp only [CollatzResearch.WordTrace]
  refine ⟨240674105883069702887080733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160449403922046468591387155 240674105883069702887080733)
  ·
    refine ⟨90252789706151138582655275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240674105883069702887080733 90252789706151138582655275)
    ·
      refine ⟨135379184559226707873982913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90252789706151138582655275 135379184559226707873982913)
      ·
        refine ⟨101534388419420030905487185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135379184559226707873982913 101534388419420030905487185)
        ·
          refine ⟨76150791314565023179115389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101534388419420030905487185 76150791314565023179115389)
          ·
            refine ⟨28556546742961883692168271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76150791314565023179115389 28556546742961883692168271)
            ·
              refine ⟨42834820114442825538252407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28556546742961883692168271 42834820114442825538252407)
              ·
                refine ⟨64252230171664238307378611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42834820114442825538252407 64252230171664238307378611)
                ·
                  refine ⟨96378345257496357461067917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64252230171664238307378611 96378345257496357461067917)
                  ·
                    refine ⟨36141879471561134047900469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96378345257496357461067917 36141879471561134047900469)
                    ·
                      refine ⟨3388301200458856316990669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36141879471561134047900469 3388301200458856316990669)
                      ·
                        rfl

theorem cell23_6598693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_6598693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598693 prefixEnd_6598693 := by exact prefixLift 6598693
  have htrace : WordTrace (prefixWord ++ tailWord_6598693) baseStart_6598693 baseEnd_6598693 := by
    simpa [prefixWord, tailWord_6598693, baseEnd_6598693] using wordTrace_append hprefix tailTrace_6598693
  have hstable : (prefixWord ++ tailWord_6598693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598693).length < 2 ^ (prefixWord ++ tailWord_6598693).sum := by decide
  have hdescent : baseEnd_6598693 < baseStart_6598693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598703 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_6598703 : Nat := 118140960795 + 6598703 * 2 ^ 59
def prefixEnd_6598703 : Nat := 4983230072969 + 3 ^ 40 * 6598703 * 2
def baseEnd_6598703 : Nat := 3388306335265401277865623

theorem tailTrace_6598703 : CollatzResearch.WordTrace tailWord_6598703 prefixEnd_6598703 3388306335265401277865623 := by
  unfold tailWord_6598703
  simp only [CollatzResearch.WordTrace]
  refine ⟨240674470613033474594944763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160449647075355649729963175 240674470613033474594944763)
  ·
    refine ⟨361011705919550211892417145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240674470613033474594944763 361011705919550211892417145)
    ·
      refine ⟨270758779439662658919312859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361011705919550211892417145 270758779439662658919312859)
      ·
        refine ⟨406138169159493988378969289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270758779439662658919312859 406138169159493988378969289)
        ·
          refine ⟨304603626869620491284226967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406138169159493988378969289 304603626869620491284226967)
          ·
            refine ⟨456905440304430736926340451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304603626869620491284226967 456905440304430736926340451)
            ·
              refine ⟨685358160456646105389510677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456905440304430736926340451 685358160456646105389510677)
              ·
                refine ⟨32126163771405286190133313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 685358160456646105389510677 32126163771405286190133313)
                ·
                  refine ⟨24094622828553964642599985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32126163771405286190133313 24094622828553964642599985)
                  ·
                    refine ⟨18070967121415473481949989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24094622828553964642599985 18070967121415473481949989)
                    ·
                      refine ⟨3388306335265401277865623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18070967121415473481949989 3388306335265401277865623)
                      ·
                        rfl

theorem cell23_6598703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_6598703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598703 prefixEnd_6598703 := by exact prefixLift 6598703
  have htrace : WordTrace (prefixWord ++ tailWord_6598703) baseStart_6598703 baseEnd_6598703 := by
    simpa [prefixWord, tailWord_6598703, baseEnd_6598703] using wordTrace_append hprefix tailTrace_6598703
  have hstable : (prefixWord ++ tailWord_6598703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598703).length < 2 ^ (prefixWord ++ tailWord_6598703).sum := by decide
  have hdescent : baseEnd_6598703 < baseStart_6598703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598707 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 4, 2, 2]
def baseStart_6598707 : Nat := 118140960795 + 6598707 * 2 ^ 59
def prefixEnd_6598707 : Nat := 4983230072969 + 3 ^ 40 * 6598707 * 2
def baseEnd_6598707 : Nat := 3388308389188019262215605

theorem tailTrace_6598707 : CollatzResearch.WordTrace tailWord_6598707 prefixEnd_6598707 3388308389188019262215605 := by
  unfold tailWord_6598707
  simp only [CollatzResearch.WordTrace]
  refine ⟨240674616505018983278090375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160449744336679322185393583 240674616505018983278090375)
  ·
    refine ⟨361011924757528474917135563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240674616505018983278090375 361011924757528474917135563)
    ·
      refine ⟨541517887136292712375703345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361011924757528474917135563 541517887136292712375703345)
      ·
        refine ⟨406138415352219534281777509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541517887136292712375703345 406138415352219534281777509)
        ·
          refine ⟨76150952878541162677833283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406138415352219534281777509 76150952878541162677833283)
          ·
            refine ⟨114226429317811744016749925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76150952878541162677833283 114226429317811744016749925)
            ·
              refine ⟨21417455497089702003140611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114226429317811744016749925 21417455497089702003140611)
              ·
                refine ⟨32126183245634553004710917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21417455497089702003140611 32126183245634553004710917)
                ·
                  refine ⟨6023659358556478688383297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32126183245634553004710917 6023659358556478688383297)
                  ·
                    refine ⟨4517744518917359016287473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023659358556478688383297 4517744518917359016287473)
                    ·
                      refine ⟨3388308389188019262215605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517744518917359016287473 3388308389188019262215605)
                      ·
                        rfl

theorem cell23_6598707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 2, 2].length) (baseStart_6598707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598707 prefixEnd_6598707 := by exact prefixLift 6598707
  have htrace : WordTrace (prefixWord ++ tailWord_6598707) baseStart_6598707 baseEnd_6598707 := by
    simpa [prefixWord, tailWord_6598707, baseEnd_6598707] using wordTrace_append hprefix tailTrace_6598707
  have hstable : (prefixWord ++ tailWord_6598707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598707).length < 2 ^ (prefixWord ++ tailWord_6598707).sum := by decide
  have hdescent : baseEnd_6598707 < baseStart_6598707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598710 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_6598710 : Nat := 118140960795 + 6598710 * 2 ^ 59
def prefixEnd_6598710 : Nat := 4983230072969 + 3 ^ 40 * 6598710 * 2
def baseEnd_6598710 : Nat := 3388309929629982750478091

theorem tailTrace_6598710 : CollatzResearch.WordTrace tailWord_6598710 prefixEnd_6598710 3388309929629982750478091 := by
  unfold tailWord_6598710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042170370250507174403099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160449817282672076526966389 15042170370250507174403099)
  ·
    refine ⟨22563255555375760761604649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15042170370250507174403099 22563255555375760761604649)
    ·
      refine ⟨16922441666531820571203487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22563255555375760761604649 16922441666531820571203487)
      ·
        refine ⟨25383662499797730856805231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922441666531820571203487 25383662499797730856805231)
        ·
          refine ⟨38075493749696596285207847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25383662499797730856805231 38075493749696596285207847)
          ·
            refine ⟨57113240624544894427811771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38075493749696596285207847 57113240624544894427811771)
            ·
              refine ⟨85669860936817341641717657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57113240624544894427811771 85669860936817341641717657)
              ·
                refine ⟨64252395702613006231288243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85669860936817341641717657 64252395702613006231288243)
                ·
                  refine ⟨96378593553919509346932365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64252395702613006231288243 96378593553919509346932365)
                  ·
                    refine ⟨36141972582719816005099637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96378593553919509346932365 36141972582719816005099637)
                    ·
                      refine ⟨3388309929629982750478091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36141972582719816005099637 3388309929629982750478091)
                      ·
                        rfl

theorem cell23_6598710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_6598710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598710 prefixEnd_6598710 := by exact prefixLift 6598710
  have htrace : WordTrace (prefixWord ++ tailWord_6598710) baseStart_6598710 baseEnd_6598710 := by
    simpa [prefixWord, tailWord_6598710, baseEnd_6598710] using wordTrace_append hprefix tailTrace_6598710
  have hstable : (prefixWord ++ tailWord_6598710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598710).length < 2 ^ (prefixWord ++ tailWord_6598710).sum := by decide
  have hdescent : baseEnd_6598710 < baseStart_6598710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598718 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6598718 : Nat := 118140960795 + 6598718 * 2 ^ 59
def prefixEnd_6598718 : Nat := 4983230072969 + 3 ^ 40 * 6598718 * 2
def baseEnd_6598718 : Nat := 3388314037475218719178055

theorem tailTrace_6598718 : CollatzResearch.WordTrace tailWord_6598718 prefixEnd_6598718 3388314037475218719178055 := by
  unfold tailWord_6598718
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084377213497391519592601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160450011805319421437827205 30084377213497391519592601)
  ·
    refine ⟨22563282910123043639694451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084377213497391519592601 22563282910123043639694451)
    ·
      refine ⟨33844924365184565459541677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22563282910123043639694451 33844924365184565459541677)
      ·
        refine ⟨12691846636944212047328129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33844924365184565459541677 12691846636944212047328129)
        ·
          refine ⟨9518884977708159035496097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691846636944212047328129 9518884977708159035496097)
          ·
            refine ⟨7139163733281119276622073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9518884977708159035496097 7139163733281119276622073)
            ·
              refine ⟨5354372799960839457466555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139163733281119276622073 5354372799960839457466555)
              ·
                refine ⟨8031559199941259186199833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354372799960839457466555 8031559199941259186199833)
                ·
                  refine ⟨6023669399955944389649875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8031559199941259186199833 6023669399955944389649875)
                  ·
                    refine ⟨9035504099933916584474813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6023669399955944389649875 9035504099933916584474813)
                    ·
                      refine ⟨3388314037475218719178055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035504099933916584474813 3388314037475218719178055)
                      ·
                        rfl

theorem cell23_6598718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6598718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598718 prefixEnd_6598718 := by exact prefixLift 6598718
  have htrace : WordTrace (prefixWord ++ tailWord_6598718) baseStart_6598718 baseEnd_6598718 := by
    simpa [prefixWord, tailWord_6598718, baseEnd_6598718] using wordTrace_append hprefix tailTrace_6598718
  have hstable : (prefixWord ++ tailWord_6598718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598718).length < 2 ^ (prefixWord ++ tailWord_6598718).sum := by decide
  have hdescent : baseEnd_6598718 < baseStart_6598718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598740 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_6598740 : Nat := 118140960795 + 6598740 * 2 ^ 59
def prefixEnd_6598740 : Nat := 4983230072969 + 3 ^ 40 * 6598740 * 2
def baseEnd_6598740 : Nat := 3388325334049617633102953

theorem tailTrace_6598740 : CollatzResearch.WordTrace tailWord_6598740 prefixEnd_6598740 3388325334049617633102953 := by
  unfold tailWord_6598740
  simp only [CollatzResearch.WordTrace]
  refine ⟨120337910056949714957020837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160450546742599619942694449 120337910056949714957020837)
  ·
    refine ⟨22563358135678071554441407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120337910056949714957020837 22563358135678071554441407)
    ·
      refine ⟨33845037203517107331662111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22563358135678071554441407 33845037203517107331662111)
      ·
        refine ⟨50767555805275660997493167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33845037203517107331662111 50767555805275660997493167)
        ·
          refine ⟨76151333707913491496239751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50767555805275660997493167 76151333707913491496239751)
          ·
            refine ⟨114227000561870237244359627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76151333707913491496239751 114227000561870237244359627)
            ·
              refine ⟨171340500842805355866539441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114227000561870237244359627 171340500842805355866539441)
              ·
                refine ⟨128505375632104016899904581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171340500842805355866539441 128505375632104016899904581)
                ·
                  refine ⟨24094757931019503168732109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128505375632104016899904581 24094757931019503168732109)
                  ·
                    refine ⟨9035534224132313688274541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24094757931019503168732109 9035534224132313688274541)
                    ·
                      refine ⟨3388325334049617633102953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035534224132313688274541 3388325334049617633102953)
                      ·
                        rfl

theorem cell23_6598740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_6598740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598740 prefixEnd_6598740 := by exact prefixLift 6598740
  have htrace : WordTrace (prefixWord ++ tailWord_6598740) baseStart_6598740 baseEnd_6598740 := by
    simpa [prefixWord, tailWord_6598740, baseEnd_6598740] using wordTrace_append hprefix tailTrace_6598740
  have hstable : (prefixWord ++ tailWord_6598740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598740).length < 2 ^ (prefixWord ++ tailWord_6598740).sum := by decide
  have hdescent : baseEnd_6598740 < baseStart_6598740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598743 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 7]
def baseStart_6598743 : Nat := 118140960795 + 6598743 * 2 ^ 59
def prefixEnd_6598743 : Nat := 4983230072969 + 3 ^ 40 * 6598743 * 2
def baseEnd_6598743 : Nat := 1129442291497193707121813

theorem tailTrace_6598743 : CollatzResearch.WordTrace tailWord_6598743 prefixEnd_6598743 1129442291497193707121813 := by
  unfold tailWord_6598743
  simp only [CollatzResearch.WordTrace]
  refine ⟨240675929532888561426400883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160450619688592374284267255 240675929532888561426400883)
  ·
    refine ⟨361013894299332842139601325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240675929532888561426400883 361013894299332842139601325)
    ·
      refine ⟨135380210362249815802350497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361013894299332842139601325 135380210362249815802350497)
      ·
        refine ⟨101535157771687361851762873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135380210362249815802350497 101535157771687361851762873)
        ·
          refine ⟨76151368328765521388822155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101535157771687361851762873 76151368328765521388822155)
          ·
            refine ⟨114227052493148282083233233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76151368328765521388822155 114227052493148282083233233)
            ·
              refine ⟨85670289369861211562424925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114227052493148282083233233 85670289369861211562424925)
              ·
                refine ⟨32126358513697954335909347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85670289369861211562424925 32126358513697954335909347)
                ·
                  refine ⟨48189537770546931503864021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32126358513697954335909347 48189537770546931503864021)
                  ·
                    refine ⟨1129442291497193707121813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48189537770546931503864021 1129442291497193707121813)
                    ·
                      rfl

theorem cell23_6598743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_6598743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598743 prefixEnd_6598743 := by exact prefixLift 6598743
  have htrace : WordTrace (prefixWord ++ tailWord_6598743) baseStart_6598743 baseEnd_6598743 := by
    simpa [prefixWord, tailWord_6598743, baseEnd_6598743] using wordTrace_append hprefix tailTrace_6598743
  have hstable : (prefixWord ++ tailWord_6598743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598743).length < 2 ^ (prefixWord ++ tailWord_6598743).sum := by decide
  have hdescent : baseEnd_6598743 < baseStart_6598743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598764 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 5]
def baseStart_6598764 : Nat := 118140960795 + 6598764 * 2 ^ 59
def prefixEnd_6598764 : Nat := 4983230072969 + 3 ^ 40 * 6598764 * 2
def baseEnd_6598764 : Nat := 376481961953925059911427

theorem tailTrace_6598764 : CollatzResearch.WordTrace tailWord_6598764 prefixEnd_6598764 376481961953925059911427 := by
  unfold tailWord_6598764
  simp only [CollatzResearch.WordTrace]
  refine ⟨120338347732906241006457673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160451130310541654675276897 120338347732906241006457673)
  ·
    refine ⟨90253760799679680754843255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120338347732906241006457673 90253760799679680754843255)
    ·
      refine ⟨135380641199519521132264883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90253760799679680754843255 135380641199519521132264883)
      ·
        refine ⟨203070961799279281698397325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135380641199519521132264883 203070961799279281698397325)
        ·
          refine ⟨76151610674729730636898997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203070961799279281698397325 76151610674729730636898997)
          ·
            refine ⟨7139213500755912247209281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76151610674729730636898997 7139213500755912247209281)
            ·
              refine ⟨5354410125566934185406961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139213500755912247209281 5354410125566934185406961)
              ·
                refine ⟨4015807594175200639055221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354410125566934185406961 4015807594175200639055221)
                ·
                  refine ⟨376481961953925059911427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015807594175200639055221 376481961953925059911427)
                  ·
                    rfl

theorem cell23_6598764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_6598764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598764 prefixEnd_6598764 := by exact prefixLift 6598764
  have htrace : WordTrace (prefixWord ++ tailWord_6598764) baseStart_6598764 baseEnd_6598764 := by
    simpa [prefixWord, tailWord_6598764, baseEnd_6598764] using wordTrace_append hprefix tailTrace_6598764
  have hstable : (prefixWord ++ tailWord_6598764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598764).length < 2 ^ (prefixWord ++ tailWord_6598764).sum := by decide
  have hdescent : baseEnd_6598764 < baseStart_6598764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598770 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6598770 : Nat := 118140960795 + 6598770 * 2 ^ 59
def prefixEnd_6598770 : Nat := 4983230072969 + 3 ^ 40 * 6598770 * 2
def baseEnd_6598770 : Nat := 3388340738469252515727815

theorem tailTrace_6598770 : CollatzResearch.WordTrace tailWord_6598770 prefixEnd_6598770 3388340738469252515727815 := by
  unfold tailWord_6598770
  simp only [CollatzResearch.WordTrace]
  refine ⟨60169228575947686259408441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160451276202527163358422509 60169228575947686259408441)
  ·
    refine ⟨45126921431960764694556331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60169228575947686259408441 45126921431960764694556331)
    ·
      refine ⟨67690382147941147041834497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45126921431960764694556331 67690382147941147041834497)
      ·
        refine ⟨50767786610955860281375873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67690382147941147041834497 50767786610955860281375873)
        ·
          refine ⟨38075839958216895211031905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50767786610955860281375873 38075839958216895211031905)
          ·
            refine ⟨28556879968662671408273929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38075839958216895211031905 28556879968662671408273929)
            ·
              refine ⟨21417659976497003556205447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28556879968662671408273929 21417659976497003556205447)
              ·
                refine ⟨32126489964745505334308171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21417659976497003556205447 32126489964745505334308171)
                ·
                  refine ⟨48189734947118258001462257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32126489964745505334308171 48189734947118258001462257)
                  ·
                    refine ⟨36142301210338693501096693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48189734947118258001462257 36142301210338693501096693)
                    ·
                      refine ⟨3388340738469252515727815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36142301210338693501096693 3388340738469252515727815)
                      ·
                        rfl

theorem cell23_6598770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6598770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598770 prefixEnd_6598770 := by exact prefixLift 6598770
  have htrace : WordTrace (prefixWord ++ tailWord_6598770) baseStart_6598770 baseEnd_6598770 := by
    simpa [prefixWord, tailWord_6598770, baseEnd_6598770] using wordTrace_append hprefix tailTrace_6598770
  have hstable : (prefixWord ++ tailWord_6598770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598770).length < 2 ^ (prefixWord ++ tailWord_6598770).sum := by decide
  have hdescent : baseEnd_6598770 < baseStart_6598770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598800 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_6598800 : Nat := 118140960795 + 6598800 * 2 ^ 59
def prefixEnd_6598800 : Nat := 4983230072969 + 3 ^ 40 * 6598800 * 2
def baseEnd_6598800 : Nat := 3388356142888887398352677

theorem tailTrace_6598800 : CollatzResearch.WordTrace tailWord_6598800 prefixEnd_6598800 3388356142888887398352677 := by
  unfold tailWord_6598800
  simp only [CollatzResearch.WordTrace]
  refine ⟨120339004246841030080612927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160452005662454706774150569 120339004246841030080612927)
  ·
    refine ⟨180508506370261545120919391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120339004246841030080612927 180508506370261545120919391)
    ·
      refine ⟨270762759555392317681379087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180508506370261545120919391 270762759555392317681379087)
      ·
        refine ⟨406144139333088476522068631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270762759555392317681379087 406144139333088476522068631)
        ·
          refine ⟨609216208999632714783102947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406144139333088476522068631 609216208999632714783102947)
          ·
            refine ⟨913824313499449072174654421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609216208999632714783102947 913824313499449072174654421)
            ·
              refine ⟨21417757347643337629093463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 913824313499449072174654421 21417757347643337629093463)
              ·
                refine ⟨32126636021465006443640195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21417757347643337629093463 32126636021465006443640195)
                ·
                  refine ⟨48189954032197509665460293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32126636021465006443640195 48189954032197509665460293)
                  ·
                    refine ⟨9035616381037033062273805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48189954032197509665460293 9035616381037033062273805)
                    ·
                      refine ⟨3388356142888887398352677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9035616381037033062273805 3388356142888887398352677)
                      ·
                        rfl

theorem cell23_6598800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_6598800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598800 prefixEnd_6598800 := by exact prefixLift 6598800
  have htrace : WordTrace (prefixWord ++ tailWord_6598800) baseStart_6598800 baseEnd_6598800 := by
    simpa [prefixWord, tailWord_6598800, baseEnd_6598800] using wordTrace_append hprefix tailTrace_6598800
  have hstable : (prefixWord ++ tailWord_6598800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598800).length < 2 ^ (prefixWord ++ tailWord_6598800).sum := by decide
  have hdescent : baseEnd_6598800 < baseStart_6598800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598803 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 8]
def baseStart_6598803 : Nat := 118140960795 + 6598803 * 2 ^ 59
def prefixEnd_6598803 : Nat := 4983230072969 + 3 ^ 40 * 6598803 * 2
def baseEnd_6598803 : Nat := 376484187036761209623907

theorem tailTrace_6598803 : CollatzResearch.WordTrace tailWord_6598803 prefixEnd_6598803 376484187036761209623907 := by
  unfold tailWord_6598803
  simp only [CollatzResearch.WordTrace]
  refine ⟨240678117912671191673585063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160452078608447461115723375 240678117912671191673585063)
  ·
    refine ⟨361017176869006787510377595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240678117912671191673585063 361017176869006787510377595)
    ·
      refine ⟨541525765303510181265566393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361017176869006787510377595 541525765303510181265566393)
      ·
        refine ⟨406144323977632635949174795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541525765303510181265566393 406144323977632635949174795)
        ·
          refine ⟨609216485966448953923762193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406144323977632635949174795 609216485966448953923762193)
          ·
            refine ⟨456912364474836715442821645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609216485966448953923762193 456912364474836715442821645)
            ·
              refine ⟨171342136678063768291058117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456912364474836715442821645 171342136678063768291058117)
              ·
                refine ⟨32126650627136956554573397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171342136678063768291058117 32126650627136956554573397)
                ·
                  refine ⟨376484187036761209623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32126650627136956554573397 376484187036761209623907)
                  ·
                    rfl

theorem cell23_6598803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 8].length) (baseStart_6598803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598803 prefixEnd_6598803 := by exact prefixLift 6598803
  have htrace : WordTrace (prefixWord ++ tailWord_6598803) baseStart_6598803 baseEnd_6598803 := by
    simpa [prefixWord, tailWord_6598803, baseEnd_6598803] using wordTrace_append hprefix tailTrace_6598803
  have hstable : (prefixWord ++ tailWord_6598803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598803).length < 2 ^ (prefixWord ++ tailWord_6598803).sum := by decide
  have hdescent : baseEnd_6598803 < baseStart_6598803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598904 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_6598904 : Nat := 118140960795 + 6598904 * 2 ^ 59
def prefixEnd_6598904 : Nat := 4983230072969 + 3 ^ 40 * 6598904 * 2
def baseEnd_6598904 : Nat := 3388409544876954991452199

theorem tailTrace_6598904 : CollatzResearch.WordTrace tailWord_6598904 prefixEnd_6598904 3388409544876954991452199 := by
  unfold tailWord_6598904
  simp only [CollatzResearch.WordTrace]
  refine ⟨120340900842652642961505883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160454534456870190615341177 120340900842652642961505883)
  ·
    refine ⟨180511351263978964442258825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120340900842652642961505883 180511351263978964442258825)
    ·
      refine ⟨135383513447984223331694119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180511351263978964442258825 135383513447984223331694119)
      ·
        refine ⟨203075270171976334997541179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135383513447984223331694119 203075270171976334997541179)
        ·
          refine ⟨304612905257964502496311769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203075270171976334997541179 304612905257964502496311769)
          ·
            refine ⟨228459678943473376872233827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304612905257964502496311769 228459678943473376872233827)
            ·
              refine ⟨342689518415210065308350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228459678943473376872233827 342689518415210065308350741)
              ·
                refine ⟨16063571175712971811328941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 342689518415210065308350741 16063571175712971811328941)
                ·
                  refine ⟨6023839190892364429248353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16063571175712971811328941 6023839190892364429248353)
                  ·
                    refine ⟨4517879393169273321936265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023839190892364429248353 4517879393169273321936265)
                    ·
                      refine ⟨3388409544876954991452199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517879393169273321936265 3388409544876954991452199)
                      ·
                        rfl

theorem cell23_6598904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_6598904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598904 prefixEnd_6598904 := by exact prefixLift 6598904
  have htrace : WordTrace (prefixWord ++ tailWord_6598904) baseStart_6598904 baseEnd_6598904 := by
    simpa [prefixWord, tailWord_6598904, baseEnd_6598904] using wordTrace_append hprefix tailTrace_6598904
  have hstable : (prefixWord ++ tailWord_6598904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598904).length < 2 ^ (prefixWord ++ tailWord_6598904).sum := by decide
  have hdescent : baseEnd_6598904 < baseStart_6598904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598914 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6598914 : Nat := 118140960795 + 6598914 * 2 ^ 59
def prefixEnd_6598914 : Nat := 4983230072969 + 3 ^ 40 * 6598914 * 2
def baseEnd_6598914 : Nat := 1129471559894499984109051

theorem tailTrace_6598914 : CollatzResearch.WordTrace tailWord_6598914 prefixEnd_6598914 1129471559894499984109051 := by
  unfold tailWord_6598914
  simp only [CollatzResearch.WordTrace]
  refine ⟨60170541603817264407718949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160454777610179371753917197 60170541603817264407718949)
  ·
    refine ⟨11281976550715737076447303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60170541603817264407718949 11281976550715737076447303)
    ·
      refine ⟨16922964826073605614670955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11281976550715737076447303 16922964826073605614670955)
      ·
        refine ⟨25384447239110408422006433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922964826073605614670955 25384447239110408422006433)
        ·
          refine ⟨19038335429332806316504825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25384447239110408422006433 19038335429332806316504825)
          ·
            refine ⟨14278751571999604737378619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19038335429332806316504825 14278751571999604737378619)
            ·
              refine ⟨21418127357999407106067929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14278751571999604737378619 21418127357999407106067929)
              ·
                refine ⟨16063595518499555329550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21418127357999407106067929 16063595518499555329550947)
                ·
                  refine ⟨24095393277749332994326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16063595518499555329550947 24095393277749332994326421)
                  ·
                    refine ⟨1129471559894499984109051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24095393277749332994326421 1129471559894499984109051)
                    ·
                      rfl

theorem cell23_6598914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6598914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598914 prefixEnd_6598914 := by exact prefixLift 6598914
  have htrace : WordTrace (prefixWord ++ tailWord_6598914) baseStart_6598914 baseEnd_6598914 := by
    simpa [prefixWord, tailWord_6598914, baseEnd_6598914] using wordTrace_append hprefix tailTrace_6598914
  have hstable : (prefixWord ++ tailWord_6598914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598914).length < 2 ^ (prefixWord ++ tailWord_6598914).sum := by decide
  have hdescent : baseEnd_6598914 < baseStart_6598914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598994 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_6598994 : Nat := 118140960795 + 6598994 * 2 ^ 59
def prefixEnd_6598994 : Nat := 4983230072969 + 3 ^ 40 * 6598994 * 2
def baseEnd_6598994 : Nat := 3388455758135859639326785

theorem tailTrace_6598994 : CollatzResearch.WordTrace tailWord_6598994 prefixEnd_6598994 3388455758135859639326785 := by
  unfold tailWord_6598994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60171271063744807823447009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160456722836652820862525357 60171271063744807823447009)
  ·
    refine ⟨45128453297808605867585257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60171271063744807823447009 45128453297808605867585257)
    ·
      refine ⟨33846339973356454400688943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45128453297808605867585257 33846339973356454400688943)
      ·
        refine ⟨50769509960034681601033415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33846339973356454400688943 50769509960034681601033415)
        ·
          refine ⟨76154264940052022401550123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50769509960034681601033415 76154264940052022401550123)
          ·
            refine ⟨114231397410078033602325185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76154264940052022401550123 114231397410078033602325185)
            ·
              refine ⟨85673548057558525201743889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114231397410078033602325185 85673548057558525201743889)
              ·
                refine ⟨64255161043168893901307917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85673548057558525201743889 64255161043168893901307917)
                ·
                  refine ⟨24095685391188335212990469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64255161043168893901307917 24095685391188335212990469)
                  ·
                    refine ⟨4517941010847812852435713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24095685391188335212990469 4517941010847812852435713)
                    ·
                      refine ⟨3388455758135859639326785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517941010847812852435713 3388455758135859639326785)
                      ·
                        rfl

theorem cell23_6598994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_6598994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598994 prefixEnd_6598994 := by exact prefixLift 6598994
  have htrace : WordTrace (prefixWord ++ tailWord_6598994) baseStart_6598994 baseEnd_6598994 := by
    simpa [prefixWord, tailWord_6598994, baseEnd_6598994] using wordTrace_append hprefix tailTrace_6598994
  have hstable : (prefixWord ++ tailWord_6598994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598994).length < 2 ^ (prefixWord ++ tailWord_6598994).sum := by decide
  have hdescent : baseEnd_6598994 < baseStart_6598994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599007 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_6599007 : Nat := 118140960795 + 6599007 * 2 ^ 59
def prefixEnd_6599007 : Nat := 4983230072969 + 3 ^ 40 * 6599007 * 2
def baseEnd_6599007 : Nat := 3388462433384368088464225

theorem tailTrace_6599007 : CollatzResearch.WordTrace tailWord_6599007 prefixEnd_6599007 3388462433384368088464225 := by
  unfold tailWord_6599007
  simp only [CollatzResearch.WordTrace]
  refine ⟨240685558403932134514011275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160457038935954756342674183 240685558403932134514011275)
  ·
    refine ⟨361028337605898201771016913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240685558403932134514011275 361028337605898201771016913)
    ·
      refine ⟨270771253204423651328262685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361028337605898201771016913 270771253204423651328262685)
      ·
        refine ⟨101539219951658869248098507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270771253204423651328262685 101539219951658869248098507)
        ·
          refine ⟨152308829927488303872147761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101539219951658869248098507 152308829927488303872147761)
          ·
            refine ⟨114231622445616227904110821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152308829927488303872147761 114231622445616227904110821)
            ·
              refine ⟨21418429208553042732020779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114231622445616227904110821 21418429208553042732020779)
              ·
                refine ⟨32127643812829564098031169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21418429208553042732020779 32127643812829564098031169)
                ·
                  refine ⟨24095732859622173073523377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32127643812829564098031169 24095732859622173073523377)
                  ·
                    refine ⟨18071799644716629805142533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24095732859622173073523377 18071799644716629805142533)
                    ·
                      refine ⟨3388462433384368088464225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18071799644716629805142533 3388462433384368088464225)
                      ·
                        rfl

theorem cell23_6599007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_6599007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599007 prefixEnd_6599007 := by exact prefixLift 6599007
  have htrace : WordTrace (prefixWord ++ tailWord_6599007) baseStart_6599007 baseEnd_6599007 := by
    simpa [prefixWord, tailWord_6599007, baseEnd_6599007] using wordTrace_append hprefix tailTrace_6599007
  have hstable : (prefixWord ++ tailWord_6599007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599007).length < 2 ^ (prefixWord ++ tailWord_6599007).sum := by decide
  have hdescent : baseEnd_6599007 < baseStart_6599007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599051 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 5]
def baseStart_6599051 : Nat := 118140960795 + 6599051 * 2 ^ 59
def prefixEnd_6599051 : Nat := 4983230072969 + 3 ^ 40 * 6599051 * 2
def baseEnd_6599051 : Nat := 376498336281462879590447

theorem tailTrace_6599051 : CollatzResearch.WordTrace tailWord_6599051 prefixEnd_6599051 376498336281462879590447 := by
  unfold tailWord_6599051
  simp only [CollatzResearch.WordTrace]
  refine ⟨240687163215772730028613007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160458108810515153352408671 240687163215772730028613007)
  ·
    refine ⟨361030744823659095042919511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240687163215772730028613007 361030744823659095042919511)
    ·
      refine ⟨541546117235488642564379267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361030744823659095042919511 541546117235488642564379267)
      ·
        refine ⟨812319175853232963846568901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541546117235488642564379267 812319175853232963846568901)
        ·
          refine ⟨152309845472481180721231669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 812319175853232963846568901 152309845472481180721231669)
          ·
            refine ⟨14279048013045110692615469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152309845472481180721231669 14279048013045110692615469)
            ·
              refine ⟨5354643004891916509730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14279048013045110692615469 5354643004891916509730801)
              ·
                refine ⟨4015982253668937382298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354643004891916509730801 4015982253668937382298101)
                ·
                  refine ⟨376498336281462879590447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015982253668937382298101 376498336281462879590447)
                  ·
                    rfl

theorem cell23_6599051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 5].length) (baseStart_6599051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599051 prefixEnd_6599051 := by exact prefixLift 6599051
  have htrace : WordTrace (prefixWord ++ tailWord_6599051) baseStart_6599051 baseEnd_6599051 := by
    simpa [prefixWord, tailWord_6599051, baseEnd_6599051] using wordTrace_append hprefix tailTrace_6599051
  have hstable : (prefixWord ++ tailWord_6599051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599051).length < 2 ^ (prefixWord ++ tailWord_6599051).sum := by decide
  have hdescent : baseEnd_6599051 < baseStart_6599051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599084 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 4, 4, 2]
def baseStart_6599084 : Nat := 118140960795 + 6599084 * 2 ^ 59
def prefixEnd_6599084 : Nat := 4983230072969 + 3 ^ 40 * 6599084 * 2
def baseEnd_6599084 : Nat := 3388501971394764287201371

theorem tailTrace_6599084 : CollatzResearch.WordTrace tailWord_6599084 prefixEnd_6599084 3388501971394764287201371 := by
  unfold tailWord_6599084
  simp only [CollatzResearch.WordTrace]
  refine ⟨120344183412326588332282153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160458911216435451109709537 120344183412326588332282153)
  ·
    refine ⟨90258137559244941249211615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120344183412326588332282153 90258137559244941249211615)
    ·
      refine ⟨135387206338867411873817423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90258137559244941249211615 135387206338867411873817423)
      ·
        refine ⟨203080809508301117810726135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135387206338867411873817423 203080809508301117810726135)
        ·
          refine ⟨304621214262451676716089203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203080809508301117810726135 304621214262451676716089203)
          ·
            refine ⟨456931821393677515074133805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304621214262451676716089203 456931821393677515074133805)
            ·
              refine ⟨171349433022629068152800177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456931821393677515074133805 171349433022629068152800177)
              ·
                refine ⟨128512074766971801114600133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171349433022629068152800177 128512074766971801114600133)
                ·
                  refine ⟨24096014018807212708987525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128512074766971801114600133 24096014018807212708987525)
                  ·
                    refine ⟨4518002628526352382935161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24096014018807212708987525 4518002628526352382935161)
                    ·
                      refine ⟨3388501971394764287201371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518002628526352382935161 3388501971394764287201371)
                      ·
                        rfl

theorem cell23_6599084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_6599084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599084 prefixEnd_6599084 := by exact prefixLift 6599084
  have htrace : WordTrace (prefixWord ++ tailWord_6599084) baseStart_6599084 baseEnd_6599084 := by
    simpa [prefixWord, tailWord_6599084, baseEnd_6599084] using wordTrace_append hprefix tailTrace_6599084
  have hstable : (prefixWord ++ tailWord_6599084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599084).length < 2 ^ (prefixWord ++ tailWord_6599084).sum := by decide
  have hdescent : baseEnd_6599084 < baseStart_6599084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599161 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 2, 3, 2]
def baseStart_6599161 : Nat := 118140960795 + 6599161 * 2 ^ 59
def prefixEnd_6599161 : Nat := 4983230072969 + 3 ^ 40 * 6599161 * 2
def baseEnd_6599161 : Nat := 3388541509405160485938517

theorem tailTrace_6599161 : CollatzResearch.WordTrace tailWord_6599161 prefixEnd_6599161 3388541509405160485938517 := by
  unfold tailWord_6599161
  simp only [CollatzResearch.WordTrace]
  refine ⟨240691175245374218815117337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160460783496916145876744891 240691175245374218815117337)
  ·
    refine ⟨180518381434030664111338003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240691175245374218815117337 180518381434030664111338003)
    ·
      refine ⟨270777572151045996167007005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180518381434030664111338003 270777572151045996167007005)
      ·
        refine ⟨101541589556642248562627627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270777572151045996167007005 101541589556642248562627627)
        ·
          refine ⟨152312384334963372843941441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101541589556642248562627627 152312384334963372843941441)
          ·
            refine ⟨114234288251222529632956081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152312384334963372843941441 114234288251222529632956081)
            ·
              refine ⟨85675716188416897224717061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114234288251222529632956081 85675716188416897224717061)
              ·
                refine ⟨16064196785328168229634449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85675716188416897224717061 16064196785328168229634449)
                ·
                  refine ⟨12048147588996126172225837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16064196785328168229634449 12048147588996126172225837)
                  ·
                    refine ⟨4518055345873547314584689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12048147588996126172225837 4518055345873547314584689)
                    ·
                      refine ⟨3388541509405160485938517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518055345873547314584689 3388541509405160485938517)
                      ·
                        rfl

theorem cell23_6599161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_6599161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599161 prefixEnd_6599161 := by exact prefixLift 6599161
  have htrace : WordTrace (prefixWord ++ tailWord_6599161) baseStart_6599161 baseEnd_6599161 := by
    simpa [prefixWord, tailWord_6599161, baseEnd_6599161] using wordTrace_append hprefix tailTrace_6599161
  have hstable : (prefixWord ++ tailWord_6599161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599161).length < 2 ^ (prefixWord ++ tailWord_6599161).sum := by decide
  have hdescent : baseEnd_6599161 < baseStart_6599161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599188 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6599188 : Nat := 118140960795 + 6599188 * 2 ^ 59
def prefixEnd_6599188 : Nat := 4983230072969 + 3 ^ 40 * 6599188 * 2
def baseEnd_6599188 : Nat := 1129518457794277293433631

theorem tailTrace_6599188 : CollatzResearch.WordTrace tailWord_6599188 prefixEnd_6599188 1129518457794277293433631 := by
  unfold tailWord_6599188
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346080008138201213175109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160461440010850934950900145 120346080008138201213175109)
  ·
    refine ⟨22564890001525912727470333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120346080008138201213175109 22564890001525912727470333)
    ·
      refine ⟨8461833750572217272801375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22564890001525912727470333 8461833750572217272801375)
      ·
        refine ⟨12692750625858325909202063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8461833750572217272801375 12692750625858325909202063)
        ·
          refine ⟨19039125938787488863803095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12692750625858325909202063 19039125938787488863803095)
          ·
            refine ⟨28558688908181233295704643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039125938787488863803095 28558688908181233295704643)
            ·
              refine ⟨42838033362271849943556965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28558688908181233295704643 42838033362271849943556965)
              ·
                refine ⟨8032131255425971864416931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42838033362271849943556965 8032131255425971864416931)
                ·
                  refine ⟨12048196883138957796625397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032131255425971864416931 12048196883138957796625397)
                  ·
                    refine ⟨1129518457794277293433631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12048196883138957796625397 1129518457794277293433631)
                    ·
                      rfl

theorem cell23_6599188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6599188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599188 prefixEnd_6599188 := by exact prefixLift 6599188
  have htrace : WordTrace (prefixWord ++ tailWord_6599188) baseStart_6599188 baseEnd_6599188 := by
    simpa [prefixWord, tailWord_6599188, baseEnd_6599188] using wordTrace_append hprefix tailTrace_6599188
  have hstable : (prefixWord ++ tailWord_6599188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599188).length < 2 ^ (prefixWord ++ tailWord_6599188).sum := by decide
  have hdescent : baseEnd_6599188 < baseStart_6599188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599208 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6599208 : Nat := 118140960795 + 6599208 * 2 ^ 59
def prefixEnd_6599208 : Nat := 4983230072969 + 3 ^ 40 * 6599208 * 2
def baseEnd_6599208 : Nat := 3388565642995921802050801

theorem tailTrace_6599208 : CollatzResearch.WordTrace tailWord_6599208 prefixEnd_6599208 3388565642995921802050801 := by
  unfold tailWord_6599208
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346444738101972921039139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160461926317469297228052185 120346444738101972921039139)
  ·
    refine ⟨180519667107152959381558709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120346444738101972921039139 180519667107152959381558709)
    ·
      refine ⟨16923718791295589942021129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180519667107152959381558709 16923718791295589942021129)
      ·
        refine ⟨12692789093471692456515847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16923718791295589942021129 12692789093471692456515847)
        ·
          refine ⟨19039183640207538684773771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12692789093471692456515847 19039183640207538684773771)
          ·
            refine ⟨28558775460311308027160657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039183640207538684773771 28558775460311308027160657)
            ·
              refine ⟨21419081595233481020370493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28558775460311308027160657 21419081595233481020370493)
              ·
                refine ⟨8032155598212555382638935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21419081595233481020370493 8032155598212555382638935)
                ·
                  refine ⟨12048233397318833073958403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032155598212555382638935 12048233397318833073958403)
                  ·
                    refine ⟨18072350095978249610937605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12048233397318833073958403 18072350095978249610937605)
                    ·
                      refine ⟨3388565642995921802050801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18072350095978249610937605 3388565642995921802050801)
                      ·
                        rfl

theorem cell23_6599208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6599208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599208 prefixEnd_6599208 := by exact prefixLift 6599208
  have htrace : WordTrace (prefixWord ++ tailWord_6599208) baseStart_6599208 baseEnd_6599208 := by
    simpa [prefixWord, tailWord_6599208, baseEnd_6599208] using wordTrace_append hprefix tailTrace_6599208
  have hstable : (prefixWord ++ tailWord_6599208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599208).length < 2 ^ (prefixWord ++ tailWord_6599208).sum := by decide
  have hdescent : baseEnd_6599208 < baseStart_6599208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599238 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6599238 : Nat := 118140960795 + 6599238 * 2 ^ 59
def prefixEnd_6599238 : Nat := 4983230072969 + 3 ^ 40 * 6599238 * 2
def baseEnd_6599238 : Nat := 3388581047415556684675663

theorem tailTrace_6599238 : CollatzResearch.WordTrace tailWord_6599238 prefixEnd_6599238 3388581047415556684675663 := by
  unfold tailWord_6599238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521686989565476905177199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160462655777396840643780245 7521686989565476905177199)
  ·
    refine ⟨11282530484348215357765799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521686989565476905177199 11282530484348215357765799)
    ·
      refine ⟨16923795726522323036648699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11282530484348215357765799 16923795726522323036648699)
      ·
        refine ⟨25385693589783484554973049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16923795726522323036648699 25385693589783484554973049)
        ·
          refine ⟨19039270192337613416229787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25385693589783484554973049 19039270192337613416229787)
          ·
            refine ⟨28558905288506420124344681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039270192337613416229787 28558905288506420124344681)
            ·
              refine ⟨21419178966379815093258511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28558905288506420124344681 21419178966379815093258511)
              ·
                refine ⟨32128768449569722639887767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21419178966379815093258511 32128768449569722639887767)
                ·
                  refine ⟨48193152674354583959831651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32128768449569722639887767 48193152674354583959831651)
                  ·
                    refine ⟨72289729011531875939747477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48193152674354583959831651 72289729011531875939747477)
                    ·
                      refine ⟨3388581047415556684675663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72289729011531875939747477 3388581047415556684675663)
                      ·
                        rfl

theorem cell23_6599238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6599238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599238 prefixEnd_6599238 := by exact prefixLift 6599238
  have htrace : WordTrace (prefixWord ++ tailWord_6599238) baseStart_6599238 baseEnd_6599238 := by
    simpa [prefixWord, tailWord_6599238, baseEnd_6599238] using wordTrace_append hprefix tailTrace_6599238
  have hstable : (prefixWord ++ tailWord_6599238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599238).length < 2 ^ (prefixWord ++ tailWord_6599238).sum := by decide
  have hdescent : baseEnd_6599238 < baseStart_6599238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599245 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6599245 : Nat := 118140960795 + 6599245 * 2 ^ 59
def prefixEnd_6599245 : Nat := 4983230072969 + 3 ^ 40 * 6599245 * 2
def baseEnd_6599245 : Nat := 3388584641780138157288131

theorem tailTrace_6599245 : CollatzResearch.WordTrace tailWord_6599245 prefixEnd_6599245 3388584641780138157288131 := by
  unfold tailWord_6599245
  simp only [CollatzResearch.WordTrace]
  refine ⟨240694238977069901161175189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160462825984713267440783459 240694238977069901161175189)
  ·
    refine ⟨11282542452050151616930087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240694238977069901161175189 11282542452050151616930087)
    ·
      refine ⟨16923813678075227425395131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11282542452050151616930087 16923813678075227425395131)
      ·
        refine ⟨25385720517112841138092697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16923813678075227425395131 25385720517112841138092697)
        ·
          refine ⟨19039290387834630853569523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25385720517112841138092697 19039290387834630853569523)
          ·
            refine ⟨28558935581751946280354285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039290387834630853569523 28558935581751946280354285)
            ·
              refine ⟨10709600843156979855132857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28558935581751946280354285 10709600843156979855132857)
              ·
                refine ⟨8032200632367734891349643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10709600843156979855132857 8032200632367734891349643)
                ·
                  refine ⟨12048300948551602337024465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032200632367734891349643 12048300948551602337024465)
                  ·
                    refine ⟨9036225711413701752768349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12048300948551602337024465 9036225711413701752768349)
                    ·
                      refine ⟨3388584641780138157288131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9036225711413701752768349 3388584641780138157288131)
                      ·
                        rfl

theorem cell23_6599245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6599245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599245 prefixEnd_6599245 := by exact prefixLift 6599245
  have htrace : WordTrace (prefixWord ++ tailWord_6599245) baseStart_6599245 baseEnd_6599245 := by
    simpa [prefixWord, tailWord_6599245, baseEnd_6599245] using wordTrace_append hprefix tailTrace_6599245
  have hstable : (prefixWord ++ tailWord_6599245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599245).length < 2 ^ (prefixWord ++ tailWord_6599245).sum := by decide
  have hdescent : baseEnd_6599245 < baseStart_6599245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599344 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_6599344 : Nat := 118140960795 + 6599344 * 2 ^ 59
def prefixEnd_6599344 : Nat := 4983230072969 + 3 ^ 40 * 6599344 * 2
def baseEnd_6599344 : Nat := 3388635476364933269950175

theorem tailTrace_6599344 : CollatzResearch.WordTrace tailWord_6599344 prefixEnd_6599344 3388635476364933269950175 := by
  unfold tailWord_6599344
  simp only [CollatzResearch.WordTrace]
  refine ⟨120348924901855620534514543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160465233202474160712686057 120348924901855620534514543)
  ·
    refine ⟨180523387352783430801771815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120348924901855620534514543 180523387352783430801771815)
    ·
      refine ⟨270785081029175146202657723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180523387352783430801771815 270785081029175146202657723)
      ·
        refine ⟨406177621543762719303986585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270785081029175146202657723 406177621543762719303986585)
        ·
          refine ⟨304633216157822039477989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406177621543762719303986585 304633216157822039477989939)
          ·
            refine ⟨456949824236733059216984909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304633216157822039477989939 456949824236733059216984909)
            ·
              refine ⟨171356184088774897206369341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456949824236733059216984909 171356184088774897206369341)
              ·
                refine ⟨64258569033290586452388503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171356184088774897206369341 64258569033290586452388503)
                ·
                  refine ⟨96387853549935879678582755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64258569033290586452388503 96387853549935879678582755)
                  ·
                    refine ⟨144581780324903819517874133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96387853549935879678582755 144581780324903819517874133)
                    ·
                      refine ⟨3388635476364933269950175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144581780324903819517874133 3388635476364933269950175)
                      ·
                        rfl

theorem cell23_6599344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_6599344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599344 prefixEnd_6599344 := by exact prefixLift 6599344
  have htrace : WordTrace (prefixWord ++ tailWord_6599344) baseStart_6599344 baseEnd_6599344 := by
    simpa [prefixWord, tailWord_6599344, baseEnd_6599344] using wordTrace_append hprefix tailTrace_6599344
  have hstable : (prefixWord ++ tailWord_6599344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599344).length < 2 ^ (prefixWord ++ tailWord_6599344).sum := by decide
  have hdescent : baseEnd_6599344 < baseStart_6599344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599349 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6599349 : Nat := 118140960795 + 6599349 * 2 ^ 59
def prefixEnd_6599349 : Nat := 4983230072969 + 3 ^ 40 * 6599349 * 2
def baseEnd_6599349 : Nat := 3388638043768205750387653

theorem tailTrace_6599349 : CollatzResearch.WordTrace tailWord_6599349 prefixEnd_6599349 3388638043768205750387653 := by
  unfold tailWord_6599349
  simp only [CollatzResearch.WordTrace]
  refine ⟨240698032168693126922961101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160465354779128751281974067 240698032168693126922961101)
  ·
    refine ⟨90261762063259922596110413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240698032168693126922961101 90261762063259922596110413)
    ·
      refine ⟨33848160773722470973541405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90261762063259922596110413 33848160773722470973541405)
      ·
        refine ⟨12693060290145926615078027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33848160773722470973541405 12693060290145926615078027)
        ·
          refine ⟨19039590435218889922617041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693060290145926615078027 19039590435218889922617041)
          ·
            refine ⟨14279692826414167441962781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19039590435218889922617041 14279692826414167441962781)
            ·
              refine ⟨5354884809905312790736043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14279692826414167441962781 5354884809905312790736043)
              ·
                refine ⟨8032327214857969186104065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354884809905312790736043 8032327214857969186104065)
                ·
                  refine ⟨6024245411143476889578049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8032327214857969186104065 6024245411143476889578049)
                  ·
                    refine ⟨4518184058357607667183537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024245411143476889578049 4518184058357607667183537)
                    ·
                      refine ⟨3388638043768205750387653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518184058357607667183537 3388638043768205750387653)
                      ·
                        rfl

theorem cell23_6599349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6599349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599349 prefixEnd_6599349 := by exact prefixLift 6599349
  have htrace : WordTrace (prefixWord ++ tailWord_6599349) baseStart_6599349 baseEnd_6599349 := by
    simpa [prefixWord, tailWord_6599349, baseEnd_6599349] using wordTrace_append hprefix tailTrace_6599349
  have hstable : (prefixWord ++ tailWord_6599349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599349).length < 2 ^ (prefixWord ++ tailWord_6599349).sum := by decide
  have hdescent : baseEnd_6599349 < baseStart_6599349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599448 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6599448 : Nat := 118140960795 + 6599448 * 2 ^ 59
def prefixEnd_6599448 : Nat := 4983230072969 + 3 ^ 40 * 6599448 * 2
def baseEnd_6599448 : Nat := 3388688878353000863049697

theorem tailTrace_6599448 : CollatzResearch.WordTrace tailWord_6599448 prefixEnd_6599448 3388688878353000863049697 := by
  unfold tailWord_6599448
  simp only [CollatzResearch.WordTrace]
  refine ⟨120350821497667233415407499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160467761996889644553876665 120350821497667233415407499)
  ·
    refine ⟨180526232246500850123111249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120350821497667233415407499 180526232246500850123111249)
    ·
      refine ⟨135394674184875637592333437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180526232246500850123111249 135394674184875637592333437)
      ·
        refine ⟨50773002819328364097125039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135394674184875637592333437 50773002819328364097125039)
        ·
          refine ⟨76159504228992546145687559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50773002819328364097125039 76159504228992546145687559)
          ·
            refine ⟨114239256343488819218531339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76159504228992546145687559 114239256343488819218531339)
            ·
              refine ⟨171358884515233228827797009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114239256343488819218531339 171358884515233228827797009)
              ·
                refine ⟨128519163386424921620847757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171358884515233228827797009 128519163386424921620847757)
                ·
                  refine ⟨48194686269909345607817909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128519163386424921620847757 48194686269909345607817909)
                  ·
                    refine ⟨4518251837804001150732929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48194686269909345607817909 4518251837804001150732929)
                    ·
                      refine ⟨3388688878353000863049697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518251837804001150732929 3388688878353000863049697)
                      ·
                        rfl

theorem cell23_6599448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6599448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599448 prefixEnd_6599448 := by exact prefixLift 6599448
  have htrace : WordTrace (prefixWord ++ tailWord_6599448) baseStart_6599448 baseEnd_6599448 := by
    simpa [prefixWord, tailWord_6599448, baseEnd_6599448] using wordTrace_append hprefix tailTrace_6599448
  have hstable : (prefixWord ++ tailWord_6599448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599448).length < 2 ^ (prefixWord ++ tailWord_6599448).sum := by decide
  have hdescent : baseEnd_6599448 < baseStart_6599448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599458 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6599458 : Nat := 118140960795 + 6599458 * 2 ^ 59
def prefixEnd_6599458 : Nat := 4983230072969 + 3 ^ 40 * 6599458 * 2
def baseEnd_6599458 : Nat := 1129564671053181941308217

theorem tailTrace_6599458 : CollatzResearch.WordTrace tailWord_6599458 prefixEnd_6599458 1129564671053181941308217 := by
  unfold tailWord_6599458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60175501931324559634669757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160468005150198825692452685 60175501931324559634669757)
  ·
    refine ⟨22565813224246709863001159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60175501931324559634669757 22565813224246709863001159)
    ·
      refine ⟨33848719836370064794501739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22565813224246709863001159 33848719836370064794501739)
      ·
        refine ⟨50773079754555097191752609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33848719836370064794501739 50773079754555097191752609)
        ·
          refine ⟨38079809815916322893814457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50773079754555097191752609 38079809815916322893814457)
          ·
            refine ⟨28559857361937242170360843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38079809815916322893814457 28559857361937242170360843)
            ·
              refine ⟨42839786042905863255541265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28559857361937242170360843 42839786042905863255541265)
              ·
                refine ⟨32129839532179397441655949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42839786042905863255541265 32129839532179397441655949)
                ·
                  refine ⟨12048689824567274040620981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32129839532179397441655949 12048689824567274040620981)
                  ·
                    refine ⟨1129564671053181941308217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12048689824567274040620981 1129564671053181941308217)
                    ·
                      rfl

theorem cell23_6599458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6599458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599458 prefixEnd_6599458 := by exact prefixLift 6599458
  have htrace : WordTrace (prefixWord ++ tailWord_6599458) baseStart_6599458 baseEnd_6599458 := by
    simpa [prefixWord, tailWord_6599458, baseEnd_6599458] using wordTrace_append hprefix tailTrace_6599458
  have hstable : (prefixWord ++ tailWord_6599458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599458).length < 2 ^ (prefixWord ++ tailWord_6599458).sum := by decide
  have hdescent : baseEnd_6599458 < baseStart_6599458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599495 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_6599495 : Nat := 118140960795 + 6599495 * 2 ^ 59
def prefixEnd_6599495 : Nat := 4983230072969 + 3 ^ 40 * 6599495 * 2
def baseEnd_6599495 : Nat := 3388713011943762179161981

theorem tailTrace_6599495 : CollatzResearch.WordTrace tailWord_6599495 prefixEnd_6599495 3388713011943762179161981 := by
  unfold tailWord_6599495
  simp only [CollatzResearch.WordTrace]
  refine ⟨240703357226164193857775939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160468904817442795905183959 240703357226164193857775939)
  ·
    refine ⟨361055035839246290786663909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240703357226164193857775939 361055035839246290786663909)
    ·
      refine ⟨67697819219858679522499483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361055035839246290786663909 67697819219858679522499483)
      ·
        refine ⟨101546728829788019283749225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67697819219858679522499483 101546728829788019283749225)
        ·
          refine ⟨76160046622341014462811919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101546728829788019283749225 76160046622341014462811919)
          ·
            refine ⟨114240069933511521694217879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76160046622341014462811919 114240069933511521694217879)
            ·
              refine ⟨171360104900267282541326819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114240069933511521694217879 171360104900267282541326819)
              ·
                refine ⟨257040157350400923811990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171360104900267282541326819 257040157350400923811990229)
                ·
                  refine ⟨6024378687900021651843521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 257040157350400923811990229 6024378687900021651843521)
                  ·
                    refine ⟨4518284015925016238882641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024378687900021651843521 4518284015925016238882641)
                    ·
                      refine ⟨3388713011943762179161981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518284015925016238882641 3388713011943762179161981)
                      ·
                        rfl

theorem cell23_6599495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_6599495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599495 prefixEnd_6599495 := by exact prefixLift 6599495
  have htrace : WordTrace (prefixWord ++ tailWord_6599495) baseStart_6599495 baseEnd_6599495 := by
    simpa [prefixWord, tailWord_6599495, baseEnd_6599495] using wordTrace_append hprefix tailTrace_6599495
  have hstable : (prefixWord ++ tailWord_6599495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599495).length < 2 ^ (prefixWord ++ tailWord_6599495).sum := by decide
  have hdescent : baseEnd_6599495 < baseStart_6599495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599498 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_6599498 : Nat := 118140960795 + 6599498 * 2 ^ 59
def prefixEnd_6599498 : Nat := 4983230072969 + 3 ^ 40 * 6599498 * 2
def baseEnd_6599498 : Nat := 3388714552385725667424467

theorem tailTrace_6599498 : CollatzResearch.WordTrace tailWord_6599498 prefixEnd_6599498 3388714552385725667424467 := by
  unfold tailWord_6599498
  simp only [CollatzResearch.WordTrace]
  refine ⟨60175866661288331342533787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160468977763435550246756765 60175866661288331342533787)
  ·
    refine ⟨90263799991932497013800681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60175866661288331342533787 90263799991932497013800681)
    ·
      refine ⟨67697849993949372760350511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90263799991932497013800681 67697849993949372760350511)
      ·
        refine ⟨101546774990924059140525767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67697849993949372760350511 101546774990924059140525767)
        ·
          refine ⟨152320162486386088710788651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101546774990924059140525767 152320162486386088710788651)
          ·
            refine ⟨228480243729579133066182977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152320162486386088710788651 228480243729579133066182977)
            ·
              refine ⟨171360182797184349799637233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228480243729579133066182977 171360182797184349799637233)
              ·
                refine ⟨128520137097888262349727925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171360182797184349799637233 128520137097888262349727925)
                ·
                  refine ⟨12048762852927024595286993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128520137097888262349727925 12048762852927024595286993)
                  ·
                    refine ⟨9036572139695268446465245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12048762852927024595286993 9036572139695268446465245)
                    ·
                      refine ⟨3388714552385725667424467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9036572139695268446465245 3388714552385725667424467)
                      ·
                        rfl

theorem cell23_6599498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_6599498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599498 prefixEnd_6599498 := by exact prefixLift 6599498
  have htrace : WordTrace (prefixWord ++ tailWord_6599498) baseStart_6599498 baseEnd_6599498 := by
    simpa [prefixWord, tailWord_6599498, baseEnd_6599498] using wordTrace_append hprefix tailTrace_6599498
  have hstable : (prefixWord ++ tailWord_6599498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599498).length < 2 ^ (prefixWord ++ tailWord_6599498).sum := by decide
  have hdescent : baseEnd_6599498 < baseStart_6599498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599505 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_6599505 : Nat := 118140960795 + 6599505 * 2 ^ 59
def prefixEnd_6599505 : Nat := 4983230072969 + 3 ^ 40 * 6599505 * 2
def baseEnd_6599505 : Nat := 1129572715583435713345645

theorem tailTrace_6599505 : CollatzResearch.WordTrace tailWord_6599505 prefixEnd_6599505 1129572715583435713345645 := by
  unfold tailWord_6599505
  simp only [CollatzResearch.WordTrace]
  refine ⟨240703721956127965565639969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160469147970751977043759979 240703721956127965565639969)
  ·
    refine ⟨180527791467095974174229977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240703721956127965565639969 180527791467095974174229977)
    ·
      refine ⟨135395843600321980630672483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180527791467095974174229977 135395843600321980630672483)
      ·
        refine ⟨203093765400482970946008725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135395843600321980630672483 203093765400482970946008725)
        ·
          refine ⟨9520020253147639263094159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203093765400482970946008725 9520020253147639263094159)
          ·
            refine ⟨14280030379721458894641239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520020253147639263094159 14280030379721458894641239)
            ·
              refine ⟨21420045569582188341961859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14280030379721458894641239 21420045569582188341961859)
              ·
                refine ⟨32130068354373282512942789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420045569582188341961859 32130068354373282512942789)
                ·
                  refine ⟨6024387816444990471176773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32130068354373282512942789 6024387816444990471176773)
                  ·
                    refine ⟨1129572715583435713345645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6024387816444990471176773 1129572715583435713345645)
                    ·
                      rfl

theorem cell23_6599505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_6599505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599505 prefixEnd_6599505 := by exact prefixLift 6599505
  have htrace : WordTrace (prefixWord ++ tailWord_6599505) baseStart_6599505 baseEnd_6599505 := by
    simpa [prefixWord, tailWord_6599505, baseEnd_6599505] using wordTrace_append hprefix tailTrace_6599505
  have hstable : (prefixWord ++ tailWord_6599505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599505).length < 2 ^ (prefixWord ++ tailWord_6599505).sum := by decide
  have hdescent : baseEnd_6599505 < baseStart_6599505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599521 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6599521 : Nat := 118140960795 + 6599521 * 2 ^ 59
def prefixEnd_6599521 : Nat := 4983230072969 + 3 ^ 40 * 6599521 * 2
def baseEnd_6599521 : Nat := 3388726362440779077436861

theorem tailTrace_6599521 : CollatzResearch.WordTrace tailWord_6599521 prefixEnd_6599521 3388726362440779077436861 := by
  unfold tailWord_6599521
  simp only [CollatzResearch.WordTrace]
  refine ⟨240704305524070000298222417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160469537016046666865481611 240704305524070000298222417)
  ·
    refine ⟨180528229143052500223666813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240704305524070000298222417 180528229143052500223666813)
    ·
      refine ⟨67698085928644687583875055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180528229143052500223666813 67698085928644687583875055)
      ·
        refine ⟨101547128892967031375812583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67698085928644687583875055 101547128892967031375812583)
        ·
          refine ⟨152320693339450547063718875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101547128892967031375812583 152320693339450547063718875)
          ·
            refine ⟨228481040009175820595578313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152320693339450547063718875 228481040009175820595578313)
            ·
              refine ⟨171360780006881865446683735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228481040009175820595578313 171360780006881865446683735)
              ·
                refine ⟨257041170010322798170025603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171360780006881865446683735 257041170010322798170025603)
                ·
                  refine ⟨385561755015484197255038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257041170010322798170025603 385561755015484197255038405)
                  ·
                    refine ⟨72292829065403286985319701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 385561755015484197255038405 72292829065403286985319701)
                    ·
                      refine ⟨3388726362440779077436861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72292829065403286985319701 3388726362440779077436861)
                      ·
                        rfl

theorem cell23_6599521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6599521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599521 prefixEnd_6599521 := by exact prefixLift 6599521
  have htrace : WordTrace (prefixWord ++ tailWord_6599521) baseStart_6599521 baseEnd_6599521 := by
    simpa [prefixWord, tailWord_6599521, baseEnd_6599521] using wordTrace_append hprefix tailTrace_6599521
  have hstable : (prefixWord ++ tailWord_6599521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599521).length < 2 ^ (prefixWord ++ tailWord_6599521).sum := by decide
  have hdescent : baseEnd_6599521 < baseStart_6599521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599522 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6599522 : Nat := 118140960795 + 6599522 * 2 ^ 59
def prefixEnd_6599522 : Nat := 4983230072969 + 3 ^ 40 * 6599522 * 2
def baseEnd_6599522 : Nat := 1129575625307144524508119

theorem tailTrace_6599522 : CollatzResearch.WordTrace tailWord_6599522 prefixEnd_6599522 1129575625307144524508119 := by
  unfold tailWord_6599522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60176085499266594367252205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160469561331377584979339213 60176085499266594367252205)
  ·
    refine ⟨22566032062224972887719577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60176085499266594367252205 22566032062224972887719577)
    ·
      refine ⟨16924524046668729665789683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22566032062224972887719577 16924524046668729665789683)
      ·
        refine ⟨25386786070003094498684525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924524046668729665789683 25386786070003094498684525)
        ·
          refine ⟨9520044776251160437006697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25386786070003094498684525 9520044776251160437006697)
          ·
            refine ⟨7140033582188370327755023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9520044776251160437006697 7140033582188370327755023)
            ·
              refine ⟨10710050373282555491632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140033582188370327755023 10710050373282555491632535)
              ·
                refine ⟨16065075559923833237448803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10710050373282555491632535 16065075559923833237448803)
                ·
                  refine ⟨24097613339885749856173205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16065075559923833237448803 24097613339885749856173205)
                  ·
                    refine ⟨1129575625307144524508119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24097613339885749856173205 1129575625307144524508119)
                    ·
                      rfl

theorem cell23_6599522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6599522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599522 prefixEnd_6599522 := by exact prefixLift 6599522
  have htrace : WordTrace (prefixWord ++ tailWord_6599522) baseStart_6599522 baseEnd_6599522 := by
    simpa [prefixWord, tailWord_6599522, baseEnd_6599522] using wordTrace_append hprefix tailTrace_6599522
  have hstable : (prefixWord ++ tailWord_6599522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599522).length < 2 ^ (prefixWord ++ tailWord_6599522).sum := by decide
  have hdescent : baseEnd_6599522 < baseStart_6599522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599531 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 7]
def baseStart_6599531 : Nat := 118140960795 + 6599531 * 2 ^ 59
def prefixEnd_6599531 : Nat := 4983230072969 + 3 ^ 40 * 6599531 * 2
def baseEnd_6599531 : Nat := 1129577165749108012770605

theorem tailTrace_6599531 : CollatzResearch.WordTrace tailWord_6599531 prefixEnd_6599531 1129577165749108012770605 := by
  unfold tailWord_6599531
  simp only [CollatzResearch.WordTrace]
  refine ⟨240704670254033772006086447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160469780169355848004057631 240704670254033772006086447)
  ·
    refine ⟨361057005381050658009129671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240704670254033772006086447 361057005381050658009129671)
    ·
      refine ⟨541585508071575987013694507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361057005381050658009129671 541585508071575987013694507)
      ·
        refine ⟨812378262107363980520541761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541585508071575987013694507 812378262107363980520541761)
        ·
          refine ⟨609283696580522985390406321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812378262107363980520541761 609283696580522985390406321)
          ·
            refine ⟨456962772435392239042804741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609283696580522985390406321 456962772435392239042804741)
            ·
              refine ⟨85680519831636044820525889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 456962772435392239042804741 85680519831636044820525889)
              ·
                refine ⟨64260389873727033615394417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85680519831636044820525889 64260389873727033615394417)
                ·
                  refine ⟨48195292405295275211545813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64260389873727033615394417 48195292405295275211545813)
                  ·
                    refine ⟨1129577165749108012770605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48195292405295275211545813 1129577165749108012770605)
                    ·
                      rfl

theorem cell23_6599531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_6599531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599531 prefixEnd_6599531 := by exact prefixLift 6599531
  have htrace : WordTrace (prefixWord ++ tailWord_6599531) baseStart_6599531 baseEnd_6599531 := by
    simpa [prefixWord, tailWord_6599531, baseEnd_6599531] using wordTrace_append hprefix tailTrace_6599531
  have hstable : (prefixWord ++ tailWord_6599531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599531).length < 2 ^ (prefixWord ++ tailWord_6599531).sum := by decide
  have hdescent : baseEnd_6599531 < baseStart_6599531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599545 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_6599545 : Nat := 118140960795 + 6599545 * 2 ^ 59
def prefixEnd_6599545 : Nat := 4983230072969 + 3 ^ 40 * 6599545 * 2
def baseEnd_6599545 : Nat := 3388738685976486983536751

theorem tailTrace_6599545 : CollatzResearch.WordTrace tailWord_6599545 prefixEnd_6599545 3388738685976486983536751 := by
  unfold tailWord_6599545
  simp only [CollatzResearch.WordTrace]
  refine ⟨240705180875983052397096089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160470120583988701598064059 240705180875983052397096089)
  ·
    refine ⟨180528885656987289297822067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240705180875983052397096089 180528885656987289297822067)
    ·
      refine ⟨270793328485480933946733101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180528885656987289297822067 270793328485480933946733101)
      ·
        refine ⟨101547498182055350230024913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270793328485480933946733101 101547498182055350230024913)
        ·
          refine ⟨76160623636541512672518685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101547498182055350230024913 76160623636541512672518685)
          ·
            refine ⟨28560233863703067252194507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76160623636541512672518685 28560233863703067252194507)
            ·
              refine ⟨42840350795554600878291761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28560233863703067252194507 42840350795554600878291761)
              ·
                refine ⟨32130263096665950658718821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42840350795554600878291761 32130263096665950658718821)
                ·
                  refine ⟨6024424330624865748509779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32130263096665950658718821 6024424330624865748509779)
                  ·
                    refine ⟨9036636495937298622764669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6024424330624865748509779 9036636495937298622764669)
                    ·
                      refine ⟨3388738685976486983536751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9036636495937298622764669 3388738685976486983536751)
                      ·
                        rfl

theorem cell23_6599545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_6599545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599545 prefixEnd_6599545 := by exact prefixLift 6599545
  have htrace : WordTrace (prefixWord ++ tailWord_6599545) baseStart_6599545 baseEnd_6599545 := by
    simpa [prefixWord, tailWord_6599545, baseEnd_6599545] using wordTrace_append hprefix tailTrace_6599545
  have hstable : (prefixWord ++ tailWord_6599545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599545).length < 2 ^ (prefixWord ++ tailWord_6599545).sum := by decide
  have hdescent : baseEnd_6599545 < baseStart_6599545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599562 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_6599562 : Nat := 118140960795 + 6599562 * 2 ^ 59
def prefixEnd_6599562 : Nat := 4983230072969 + 3 ^ 40 * 6599562 * 2
def baseEnd_6599562 : Nat := 3388747415147613417024173

theorem tailTrace_6599562 : CollatzResearch.WordTrace tailWord_6599562 prefixEnd_6599562 3388747415147613417024173 := by
  unfold tailWord_6599562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60176450229230366075116235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160470533944614309533643293 60176450229230366075116235)
  ·
    refine ⟨90264675343845549112674353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60176450229230366075116235 90264675343845549112674353)
    ·
      refine ⟨67698506507884161834505765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90264675343845549112674353 67698506507884161834505765)
      ·
        refine ⟨12693469970228280343969831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67698506507884161834505765 12693469970228280343969831)
        ·
          refine ⟨19040204955342420515954747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693469970228280343969831 19040204955342420515954747)
          ·
            refine ⟨28560307433013630773932121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040204955342420515954747 28560307433013630773932121)
            ·
              refine ⟨21420230574760223080449091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28560307433013630773932121 21420230574760223080449091)
              ·
                refine ⟨32130345862140334620673637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420230574760223080449091 32130345862140334620673637)
                ·
                  refine ⟨6024439849151312741376307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32130345862140334620673637 6024439849151312741376307)
                  ·
                    refine ⟨9036659773726969112064461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6024439849151312741376307 9036659773726969112064461)
                    ·
                      refine ⟨3388747415147613417024173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9036659773726969112064461 3388747415147613417024173)
                      ·
                        rfl

theorem cell23_6599562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_6599562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599562 prefixEnd_6599562 := by exact prefixLift 6599562
  have htrace : WordTrace (prefixWord ++ tailWord_6599562) baseStart_6599562 baseEnd_6599562 := by
    simpa [prefixWord, tailWord_6599562, baseEnd_6599562] using wordTrace_append hprefix tailTrace_6599562
  have hstable : (prefixWord ++ tailWord_6599562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599562).length < 2 ^ (prefixWord ++ tailWord_6599562).sum := by decide
  have hdescent : baseEnd_6599562 < baseStart_6599562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599572 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6599572 : Nat := 118140960795 + 6599572 * 2 ^ 59
def prefixEnd_6599572 : Nat := 4983230072969 + 3 ^ 40 * 6599572 * 2
def baseEnd_6599572 : Nat := 3388752549954158377899127

theorem tailTrace_6599572 : CollatzResearch.WordTrace tailWord_6599572 prefixEnd_6599572 3388752549954158377899127 := by
  unfold tailWord_6599572
  simp only [CollatzResearch.WordTrace]
  refine ⟨120353082823442618004164485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160470777097923490672219313 120353082823442618004164485)
  ·
    refine ⟨22566203029395490875780841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120353082823442618004164485 22566203029395490875780841)
    ·
      refine ⟨16924652272046618156835631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22566203029395490875780841 16924652272046618156835631)
      ·
        refine ⟨25386978408069927235253447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924652272046618156835631 25386978408069927235253447)
        ·
          refine ⟨38080467612104890852880171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25386978408069927235253447 38080467612104890852880171)
          ·
            refine ⟨57120701418157336279320257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38080467612104890852880171 57120701418157336279320257)
            ·
              refine ⟨42840526063618002209490193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57120701418157336279320257 42840526063618002209490193)
              ·
                refine ⟨32130394547713501657117645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42840526063618002209490193 32130394547713501657117645)
                ·
                  refine ⟨12048897955392563121419117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32130394547713501657117645 12048897955392563121419117)
                  ·
                    refine ⟨4518336733272211170532169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12048897955392563121419117 4518336733272211170532169)
                    ·
                      refine ⟨3388752549954158377899127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518336733272211170532169 3388752549954158377899127)
                      ·
                        rfl

theorem cell23_6599572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6599572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599572 prefixEnd_6599572 := by exact prefixLift 6599572
  have htrace : WordTrace (prefixWord ++ tailWord_6599572) baseStart_6599572 baseEnd_6599572 := by
    simpa [prefixWord, tailWord_6599572, baseEnd_6599572] using wordTrace_append hprefix tailTrace_6599572
  have hstable : (prefixWord ++ tailWord_6599572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599572).length < 2 ^ (prefixWord ++ tailWord_6599572).sum := by decide
  have hdescent : baseEnd_6599572 < baseStart_6599572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599588 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_6599588 : Nat := 118140960795 + 6599588 * 2 ^ 59
def prefixEnd_6599588 : Nat := 4983230072969 + 3 ^ 40 * 6599588 * 2
def baseEnd_6599588 : Nat := 3388760765644630315299053

theorem tailTrace_6599588 : CollatzResearch.WordTrace tailWord_6599588 prefixEnd_6599588 3388760765644630315299053 := by
  unfold tailWord_6599588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120353374607413635370455709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160471166143218180493940945 120353374607413635370455709)
  ·
    refine ⟨45132515477780113263920891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120353374607413635370455709 45132515477780113263920891)
    ·
      refine ⟨67698773216670169895881337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45132515477780113263920891 67698773216670169895881337)
      ·
        refine ⟨50774079912502627421911003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67698773216670169895881337 50774079912502627421911003)
        ·
          refine ⟨76161119868753941132866505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50774079912502627421911003 76161119868753941132866505)
          ·
            refine ⟨57120839901565455849649879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76161119868753941132866505 57120839901565455849649879)
            ·
              refine ⟨85681259852348183774474819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57120839901565455849649879 85681259852348183774474819)
              ·
                refine ⟨128521889778522275661712229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85681259852348183774474819 128521889778522275661712229)
                ·
                  refine ⟨24097854333472926686571043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128521889778522275661712229 24097854333472926686571043)
                  ·
                    refine ⟨36146781500209390029856565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24097854333472926686571043 36146781500209390029856565)
                    ·
                      refine ⟨3388760765644630315299053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36146781500209390029856565 3388760765644630315299053)
                      ·
                        rfl

theorem cell23_6599588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_6599588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599588 prefixEnd_6599588 := by exact prefixLift 6599588
  have htrace : WordTrace (prefixWord ++ tailWord_6599588) baseStart_6599588 baseEnd_6599588 := by
    simpa [prefixWord, tailWord_6599588, baseEnd_6599588] using wordTrace_append hprefix tailTrace_6599588
  have hstable : (prefixWord ++ tailWord_6599588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599588).length < 2 ^ (prefixWord ++ tailWord_6599588).sum := by decide
  have hdescent : baseEnd_6599588 < baseStart_6599588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599655 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 7]
def baseStart_6599655 : Nat := 118140960795 + 6599655 * 2 ^ 59
def prefixEnd_6599655 : Nat := 4983230072969 + 3 ^ 40 * 6599655 * 2
def baseEnd_6599655 : Nat := 1129598389616160517720415

theorem tailTrace_6599655 : CollatzResearch.WordTrace tailWord_6599655 prefixEnd_6599655 1129598389616160517720415 := by
  unfold tailWord_6599655
  simp only [CollatzResearch.WordTrace]
  refine ⟨240709192905584541183600419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160472795270389694122400279 240709192905584541183600419)
  ·
    refine ⟨361063789358376811775400629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240709192905584541183600419 361063789358376811775400629)
    ·
      refine ⟨33849730252347826103943809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361063789358376811775400629 33849730252347826103943809)
      ·
        refine ⟨25387297689260869577957857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33849730252347826103943809 25387297689260869577957857)
        ·
          refine ⟨19040473266945652183468393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25387297689260869577957857 19040473266945652183468393)
          ·
            refine ⟨14280354950209239137601295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19040473266945652183468393 14280354950209239137601295)
            ·
              refine ⟨21420532425313858706401943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14280354950209239137601295 21420532425313858706401943)
              ·
                refine ⟨32130798637970788059602915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420532425313858706401943 32130798637970788059602915)
                ·
                  refine ⟨48196197956956182089404373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32130798637970788059602915 48196197956956182089404373)
                  ·
                    refine ⟨1129598389616160517720415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48196197956956182089404373 1129598389616160517720415)
                    ·
                      rfl

theorem cell23_6599655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_6599655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599655 prefixEnd_6599655 := by exact prefixLift 6599655
  have htrace : WordTrace (prefixWord ++ tailWord_6599655) baseStart_6599655 baseEnd_6599655 := by
    simpa [prefixWord, tailWord_6599655, baseEnd_6599655] using wordTrace_append hprefix tailTrace_6599655
  have hstable : (prefixWord ++ tailWord_6599655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599655).length < 2 ^ (prefixWord ++ tailWord_6599655).sum := by decide
  have hdescent : baseEnd_6599655 < baseStart_6599655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599692 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 2, 4, 2]
def baseStart_6599692 : Nat := 118140960795 + 6599692 * 2 ^ 59
def prefixEnd_6599692 : Nat := 4983230072969 + 3 ^ 40 * 6599692 * 2
def baseEnd_6599692 : Nat := 3388814167632697908398575

theorem tailTrace_6599692 : CollatzResearch.WordTrace tailWord_6599692 prefixEnd_6599692 3388814167632697908398575 := by
  unfold tailWord_6599692
  simp only [CollatzResearch.WordTrace]
  refine ⟨120355271203225248251348665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160473694937633664335131553 120355271203225248251348665)
  ·
    refine ⟨90266453402418936188511499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120355271203225248251348665 90266453402418936188511499)
    ·
      refine ⟨135399680103628404282767249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90266453402418936188511499 135399680103628404282767249)
      ·
        refine ⟨101549760077721303212075437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135399680103628404282767249 101549760077721303212075437)
        ·
          refine ⟨38081160029145488704528289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101549760077721303212075437 38081160029145488704528289)
          ·
            refine ⟨28560870021859116528396217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38081160029145488704528289 28560870021859116528396217)
            ·
              refine ⟨21420652516394337396297163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28560870021859116528396217 21420652516394337396297163)
              ·
                refine ⟨32130978774591506094445745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420652516394337396297163 32130978774591506094445745)
                ·
                  refine ⟨24098234080943629570834309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32130978774591506094445745 24098234080943629570834309)
                  ·
                    refine ⟨4518418890176930544531433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24098234080943629570834309 4518418890176930544531433)
                    ·
                      refine ⟨3388814167632697908398575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518418890176930544531433 3388814167632697908398575)
                      ·
                        rfl

theorem cell23_6599692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_6599692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599692 prefixEnd_6599692 := by exact prefixLift 6599692
  have htrace : WordTrace (prefixWord ++ tailWord_6599692) baseStart_6599692 baseEnd_6599692 := by
    simpa [prefixWord, tailWord_6599692, baseEnd_6599692] using wordTrace_append hprefix tailTrace_6599692
  have hstable : (prefixWord ++ tailWord_6599692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599692).length < 2 ^ (prefixWord ++ tailWord_6599692).sum := by decide
  have hdescent : baseEnd_6599692 < baseStart_6599692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599732 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 8]
def baseStart_6599732 : Nat := 118140960795 + 6599732 * 2 ^ 59
def prefixEnd_6599732 : Nat := 4983230072969 + 3 ^ 40 * 6599732 * 2
def baseEnd_6599732 : Nat := 376537189650986416877599

theorem tailTrace_6599732 : CollatzResearch.WordTrace tailWord_6599732 prefixEnd_6599732 376537189650986416877599 := by
  unfold tailWord_6599732
  simp only [CollatzResearch.WordTrace]
  refine ⟨120356000663152791667076725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160474667550870388889435633 120356000663152791667076725)
  ·
    refine ⟨11283375062170574218788443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120356000663152791667076725 11283375062170574218788443)
    ·
      refine ⟨16925062593255861328182665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11283375062170574218788443 16925062593255861328182665)
      ·
        refine ⟨12693796944941895996136999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16925062593255861328182665 12693796944941895996136999)
        ·
          refine ⟨19040695417412843994205499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693796944941895996136999 19040695417412843994205499)
          ·
            refine ⟨28561043126119265991308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040695417412843994205499 28561043126119265991308249)
            ·
              refine ⟨21420782344589449493481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28561043126119265991308249 21420782344589449493481187)
              ·
                refine ⟨32131173516884174240221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420782344589449493481187 32131173516884174240221781)
                ·
                  refine ⟨376537189650986416877599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32131173516884174240221781 376537189650986416877599)
                  ·
                    rfl

theorem cell23_6599732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_6599732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599732 prefixEnd_6599732 := by exact prefixLift 6599732
  have htrace : WordTrace (prefixWord ++ tailWord_6599732) baseStart_6599732 baseEnd_6599732 := by
    simpa [prefixWord, tailWord_6599732, baseEnd_6599732] using wordTrace_append hprefix tailTrace_6599732
  have hstable : (prefixWord ++ tailWord_6599732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599732).length < 2 ^ (prefixWord ++ tailWord_6599732).sum := by decide
  have hdescent : baseEnd_6599732 < baseStart_6599732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599736 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 1, 4]
def baseStart_6599736 : Nat := 118140960795 + 6599736 * 2 ^ 59
def prefixEnd_6599736 : Nat := 4983230072969 + 3 ^ 40 * 6599736 * 2
def baseEnd_6599736 : Nat := 1129612253593831912082791

theorem tailTrace_6599736 : CollatzResearch.WordTrace tailWord_6599736 prefixEnd_6599736 1129612253593831912082791 := by
  unfold tailWord_6599736
  simp only [CollatzResearch.WordTrace]
  refine ⟨120356073609145546008649531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160474764812194061344866041 120356073609145546008649531)
  ·
    refine ⟨180534110413718319012974297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120356073609145546008649531 180534110413718319012974297)
    ·
      refine ⟨135400582810288739259730723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180534110413718319012974297 135400582810288739259730723)
      ·
        refine ⟨203100874215433108889596085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135400582810288739259730723 203100874215433108889596085)
        ·
          refine ⟨19040706957696853958399633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203100874215433108889596085 19040706957696853958399633)
          ·
            refine ⟨14280530218272640468799725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19040706957696853958399633 14280530218272640468799725)
            ·
              refine ⟨5355198831852240175799897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14280530218272640468799725 5355198831852240175799897)
              ·
                refine ⟨4016399123889180131849923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5355198831852240175799897 4016399123889180131849923)
                ·
                  refine ⟨6024598685833770197774885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4016399123889180131849923 6024598685833770197774885)
                  ·
                    refine ⟨1129612253593831912082791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6024598685833770197774885 1129612253593831912082791)
                    ·
                      rfl

theorem cell23_6599736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_6599736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599736 prefixEnd_6599736 := by exact prefixLift 6599736
  have htrace : WordTrace (prefixWord ++ tailWord_6599736) baseStart_6599736 baseEnd_6599736 := by
    simpa [prefixWord, tailWord_6599736, baseEnd_6599736] using wordTrace_append hprefix tailTrace_6599736
  have hstable : (prefixWord ++ tailWord_6599736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599736).length < 2 ^ (prefixWord ++ tailWord_6599736).sum := by decide
  have hdescent : baseEnd_6599736 < baseStart_6599736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599752 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_6599752 : Nat := 118140960795 + 6599752 * 2 ^ 59
def prefixEnd_6599752 : Nat := 4983230072969 + 3 ^ 40 * 6599752 * 2
def baseEnd_6599752 : Nat := 3388844976471967673648299

theorem tailTrace_6599752 : CollatzResearch.WordTrace tailWord_6599752 prefixEnd_6599752 3388844976471967673648299 := by
  unfold tailWord_6599752
  simp only [CollatzResearch.WordTrace]
  refine ⟨120356365393116563374940755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160475153857488751166587673 120356365393116563374940755)
  ·
    refine ⟨180534548089674845062411133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120356365393116563374940755 180534548089674845062411133)
    ·
      refine ⟨67700455533628066898404175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180534548089674845062411133 67700455533628066898404175)
      ·
        refine ⟨101550683300442100347606263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67700455533628066898404175 101550683300442100347606263)
        ·
          refine ⟨152326024950663150521409395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101550683300442100347606263 152326024950663150521409395)
          ·
            refine ⟨228489037425994725782114093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152326024950663150521409395 228489037425994725782114093)
            ·
              refine ⟨85683389034748022168292785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228489037425994725782114093 85683389034748022168292785)
              ·
                refine ⟨64262541776061016626219589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85683389034748022168292785 64262541776061016626219589)
                ·
                  refine ⟨12049226583011440617416173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64262541776061016626219589 12049226583011440617416173)
                  ·
                    refine ⟨4518459968629290231531065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12049226583011440617416173 4518459968629290231531065)
                    ·
                      refine ⟨3388844976471967673648299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518459968629290231531065 3388844976471967673648299)
                      ·
                        rfl

theorem cell23_6599752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_6599752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599752 prefixEnd_6599752 := by exact prefixLift 6599752
  have htrace : WordTrace (prefixWord ++ tailWord_6599752) baseStart_6599752 baseEnd_6599752 := by
    simpa [prefixWord, tailWord_6599752, baseEnd_6599752] using wordTrace_append hprefix tailTrace_6599752
  have hstable : (prefixWord ++ tailWord_6599752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599752).length < 2 ^ (prefixWord ++ tailWord_6599752).sum := by decide
  have hdescent : baseEnd_6599752 < baseStart_6599752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599762 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_6599762 : Nat := 118140960795 + 6599762 * 2 ^ 59
def prefixEnd_6599762 : Nat := 4983230072969 + 3 ^ 40 * 6599762 * 2
def baseEnd_6599762 : Nat := 1129616703759504211507751

theorem tailTrace_6599762 : CollatzResearch.WordTrace tailWord_6599762 prefixEnd_6599762 1129616703759504211507751 := by
  unfold tailWord_6599762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60178273879049224614436385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160475397010797932305163693 60178273879049224614436385)
  ·
    refine ⟨45133705409286918460827289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60178273879049224614436385 45133705409286918460827289)
    ·
      refine ⟨33850279056965188845620467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45133705409286918460827289 33850279056965188845620467)
      ·
        refine ⟨50775418585447783268430701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33850279056965188845620467 50775418585447783268430701)
        ·
          refine ⟨19040781969542918725661513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50775418585447783268430701 19040781969542918725661513)
          ·
            refine ⟨14280586477157189044246135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19040781969542918725661513 14280586477157189044246135)
            ·
              refine ⟨21420879715735783566369203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14280586477157189044246135 21420879715735783566369203)
              ·
                refine ⟨32131319573603675349553805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21420879715735783566369203 32131319573603675349553805)
                ·
                  refine ⟨12049244840101378256082677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32131319573603675349553805 12049244840101378256082677)
                  ·
                    refine ⟨1129616703759504211507751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12049244840101378256082677 1129616703759504211507751)
                    ·
                      rfl

theorem cell23_6599762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_6599762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599762 prefixEnd_6599762 := by exact prefixLift 6599762
  have htrace : WordTrace (prefixWord ++ tailWord_6599762) baseStart_6599762 baseEnd_6599762 := by
    simpa [prefixWord, tailWord_6599762, baseEnd_6599762] using wordTrace_append hprefix tailTrace_6599762
  have hstable : (prefixWord ++ tailWord_6599762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599762).length < 2 ^ (prefixWord ++ tailWord_6599762).sum := by decide
  have hdescent : baseEnd_6599762 < baseStart_6599762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599775 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 6]
def baseStart_6599775 : Nat := 118140960795 + 6599775 * 2 ^ 59
def prefixEnd_6599775 : Nat := 4983230072969 + 3 ^ 40 * 6599775 * 2
def baseEnd_6599775 : Nat := 1129618928842340361220231

theorem tailTrace_6599775 : CollatzResearch.WordTrace tailWord_6599775 prefixEnd_6599775 1129618928842340361220231 := by
  unfold tailWord_6599775
  simp only [CollatzResearch.WordTrace]
  refine ⟨240713569665149801677968779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160475713110099867785312519 240713569665149801677968779)
  ·
    refine ⟨361070354497724702516953169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240713569665149801677968779 361070354497724702516953169)
    ·
      refine ⟨270802765873293526887714877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361070354497724702516953169 270802765873293526887714877)
      ·
        refine ⟨101551037202485072582893079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270802765873293526887714877 101551037202485072582893079)
        ·
          refine ⟨152326555803727608874339619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101551037202485072582893079 152326555803727608874339619)
          ·
            refine ⟨228489833705591413311509429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152326555803727608874339619 228489833705591413311509429)
            ·
              refine ⟨21420921909899194997954009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228489833705591413311509429 21420921909899194997954009)
              ·
                refine ⟨16065691432424396248465507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21420921909899194997954009 16065691432424396248465507)
                ·
                  refine ⟨24098537148636594372698261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16065691432424396248465507 24098537148636594372698261)
                  ·
                    refine ⟨1129618928842340361220231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24098537148636594372698261 1129618928842340361220231)
                    ·
                      rfl

theorem cell23_6599775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_6599775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599775 prefixEnd_6599775 := by exact prefixLift 6599775
  have htrace : WordTrace (prefixWord ++ tailWord_6599775) baseStart_6599775 baseEnd_6599775 := by
    simpa [prefixWord, tailWord_6599775, baseEnd_6599775] using wordTrace_append hprefix tailTrace_6599775
  have hstable : (prefixWord ++ tailWord_6599775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599775).length < 2 ^ (prefixWord ++ tailWord_6599775).sum := by decide
  have hdescent : baseEnd_6599775 < baseStart_6599775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599799 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_6599799 : Nat := 118140960795 + 6599799 * 2 ^ 59
def prefixEnd_6599799 : Nat := 4983230072969 + 3 ^ 40 * 6599799 * 2
def baseEnd_6599799 : Nat := 3388869110062728989760583

theorem tailTrace_6599799 : CollatzResearch.WordTrace tailWord_6599799 prefixEnd_6599799 3388869110062728989760583 := by
  unfold tailWord_6599799
  simp only [CollatzResearch.WordTrace]
  refine ⟨240714445017062853776842451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160476296678041902517894967 240714445017062853776842451)
  ·
    refine ⟨361071667525594280665263677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240714445017062853776842451 361071667525594280665263677)
    ·
      refine ⟨135401875322097855249473879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361071667525594280665263677 135401875322097855249473879)
      ·
        refine ⟨203102812983146782874210819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135401875322097855249473879 203102812983146782874210819)
        ·
          refine ⟨304654219474720174311316229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203102812983146782874210819 304654219474720174311316229)
          ·
            refine ⟨57122666151510032683371793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304654219474720174311316229 57122666151510032683371793)
            ·
              refine ⟨42841999613632524512528845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57122666151510032683371793 42841999613632524512528845)
              ·
                refine ⟨16065749855112196692198317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42841999613632524512528845 16065749855112196692198317)
                ·
                  refine ⟨6024656195667073759574369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16065749855112196692198317 6024656195667073759574369)
                  ·
                    refine ⟨4518492146750305319680777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024656195667073759574369 4518492146750305319680777)
                    ·
                      refine ⟨3388869110062728989760583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518492146750305319680777 3388869110062728989760583)
                      ·
                        rfl

theorem cell23_6599799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_6599799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599799 prefixEnd_6599799 := by exact prefixLift 6599799
  have htrace : WordTrace (prefixWord ++ tailWord_6599799) baseStart_6599799 baseEnd_6599799 := by
    simpa [prefixWord, tailWord_6599799, baseEnd_6599799] using wordTrace_append hprefix tailTrace_6599799
  have hstable : (prefixWord ++ tailWord_6599799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599799).length < 2 ^ (prefixWord ++ tailWord_6599799).sum := by decide
  have hdescent : baseEnd_6599799 < baseStart_6599799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599809 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_6599809 : Nat := 118140960795 + 6599809 * 2 ^ 59
def prefixEnd_6599809 : Nat := 4983230072969 + 3 ^ 40 * 6599809 * 2
def baseEnd_6599809 : Nat := 1129624748289757983545179

theorem tailTrace_6599809 : CollatzResearch.WordTrace tailWord_6599809 prefixEnd_6599809 1129624748289757983545179 := by
  unfold tailWord_6599809
  simp only [CollatzResearch.WordTrace]
  refine ⟨240714809747026625484706481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160476539831351083656470987 240714809747026625484706481)
  ·
    refine ⟨180536107310269969113529861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240714809747026625484706481 180536107310269969113529861)
    ·
      refine ⟨33850520120675619208786849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180536107310269969113529861 33850520120675619208786849)
      ·
        refine ⟨25387890090506714406590137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33850520120675619208786849 25387890090506714406590137)
        ·
          refine ⟨19040917567880035804942603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25387890090506714406590137 19040917567880035804942603)
          ·
            refine ⟨28561376351820053707413905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040917567880035804942603 28561376351820053707413905)
            ·
              refine ⟨21421032263865040280560429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28561376351820053707413905 21421032263865040280560429)
              ·
                refine ⟨8032887098949390105210161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21421032263865040280560429 8032887098949390105210161)
                ·
                  refine ⟨6024665324212042578907621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8032887098949390105210161 6024665324212042578907621)
                  ·
                    refine ⟨1129624748289757983545179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6024665324212042578907621 1129624748289757983545179)
                    ·
                      rfl

theorem cell23_6599809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_6599809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599809 prefixEnd_6599809 := by exact prefixLift 6599809
  have htrace : WordTrace (prefixWord ++ tailWord_6599809) baseStart_6599809 baseEnd_6599809 := by
    simpa [prefixWord, tailWord_6599809, baseEnd_6599809] using wordTrace_append hprefix tailTrace_6599809
  have hstable : (prefixWord ++ tailWord_6599809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599809).length < 2 ^ (prefixWord ++ tailWord_6599809).sum := by decide
  have hdescent : baseEnd_6599809 < baseStart_6599809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599812 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6599812 : Nat := 118140960795 + 6599812 * 2 ^ 59
def prefixEnd_6599812 : Nat := 4983230072969 + 3 ^ 40 * 6599812 * 2
def baseEnd_6599812 : Nat := 3388875785311237438898023

theorem tailTrace_6599812 : CollatzResearch.WordTrace tailWord_6599812 prefixEnd_6599812 3388875785311237438898023 := by
  unfold tailWord_6599812
  simp only [CollatzResearch.WordTrace]
  refine ⟨120357459583007878498532845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160476612777343837998043793 120357459583007878498532845)
  ·
    refine ⟨45134047343627954436949817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120357459583007878498532845 45134047343627954436949817)
    ·
      refine ⟨33850535507720965827712363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45134047343627954436949817 33850535507720965827712363)
      ·
        refine ⟨50775803261581448741568545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33850535507720965827712363 50775803261581448741568545)
        ·
          refine ⟨38081852446186086556176409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50775803261581448741568545 38081852446186086556176409)
          ·
            refine ⟨28561389334639564917132307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38081852446186086556176409 28561389334639564917132307)
            ·
              refine ⟨42842084001959347375698461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28561389334639564917132307 42842084001959347375698461)
              ·
                refine ⟨16065781500734755265886923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42842084001959347375698461 16065781500734755265886923)
                ·
                  refine ⟨24098672251102132898830385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16065781500734755265886923 24098672251102132898830385)
                  ·
                    refine ⟨18074004188326599674122789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24098672251102132898830385 18074004188326599674122789)
                    ·
                      refine ⟨3388875785311237438898023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18074004188326599674122789 3388875785311237438898023)
                      ·
                        rfl

theorem cell23_6599812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6599812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599812 prefixEnd_6599812 := by exact prefixLift 6599812
  have htrace : WordTrace (prefixWord ++ tailWord_6599812) baseStart_6599812 baseEnd_6599812 := by
    simpa [prefixWord, tailWord_6599812, baseEnd_6599812] using wordTrace_append hprefix tailTrace_6599812
  have hstable : (prefixWord ++ tailWord_6599812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599812).length < 2 ^ (prefixWord ++ tailWord_6599812).sum := by decide
  have hdescent : baseEnd_6599812 < baseStart_6599812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599836 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_6599836 : Nat := 118140960795 + 6599836 * 2 ^ 59
def prefixEnd_6599836 : Nat := 4983230072969 + 3 ^ 40 * 6599836 * 2
def baseEnd_6599836 : Nat := 3388888108846945344997913

theorem tailTrace_6599836 : CollatzResearch.WordTrace tailWord_6599836 prefixEnd_6599836 3388888108846945344997913 := by
  unfold tailWord_6599836
  simp only [CollatzResearch.WordTrace]
  refine ⟨120357897258964404547969681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160477196345285872730626241 120357897258964404547969681)
  ·
    refine ⟨90268422944223303410977261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120357897258964404547969681 90268422944223303410977261)
    ·
      refine ⟨33850658604083738779116473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90268422944223303410977261 33850658604083738779116473)
      ·
        refine ⟨25387993953062804084337355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33850658604083738779116473 25387993953062804084337355)
        ·
          refine ⟨38081990929594206126506033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25387993953062804084337355 38081990929594206126506033)
          ·
            refine ⟨28561493197195654594879525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38081990929594206126506033 28561493197195654594879525)
            ·
              refine ⟨5355279974474185236539911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28561493197195654594879525 5355279974474185236539911)
              ·
                refine ⟨8032919961711277854809867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355279974474185236539911 8032919961711277854809867)
                ·
                  refine ⟨12049379942566916782214801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032919961711277854809867 12049379942566916782214801)
                  ·
                    refine ⟨9037034956925187586661101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12049379942566916782214801 9037034956925187586661101)
                    ·
                      refine ⟨3388888108846945344997913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037034956925187586661101 3388888108846945344997913)
                      ·
                        rfl

theorem cell23_6599836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_6599836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599836 prefixEnd_6599836 := by exact prefixLift 6599836
  have htrace : WordTrace (prefixWord ++ tailWord_6599836) baseStart_6599836 baseEnd_6599836 := by
    simpa [prefixWord, tailWord_6599836, baseEnd_6599836] using wordTrace_append hprefix tailTrace_6599836
  have hstable : (prefixWord ++ tailWord_6599836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599836).length < 2 ^ (prefixWord ++ tailWord_6599836).sum := by decide
  have hdescent : baseEnd_6599836 < baseStart_6599836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599850 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6599850 : Nat := 118140960795 + 6599850 * 2 ^ 59
def prefixEnd_6599850 : Nat := 4983230072969 + 3 ^ 40 * 6599850 * 2
def baseEnd_6599850 : Nat := 3388895297576108290222849

theorem tailTrace_6599850 : CollatzResearch.WordTrace tailWord_6599850 prefixEnd_6599850 3388895297576108290222849 := by
  unfold tailWord_6599850
  simp only [CollatzResearch.WordTrace]
  refine ⟨60179076284969522371737251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160477536759918726324632669 60179076284969522371737251)
  ·
    refine ⟨90268614427454283557605877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60179076284969522371737251 90268614427454283557605877)
    ·
      refine ⟨8462682602573839083525551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90268614427454283557605877 8462682602573839083525551)
      ·
        refine ⟨12694023903860758625288327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8462682602573839083525551 12694023903860758625288327)
        ·
          refine ⟨19041035855791137937932491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12694023903860758625288327 19041035855791137937932491)
          ·
            refine ⟨28561553783686706906898737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19041035855791137937932491 28561553783686706906898737)
            ·
              refine ⟨21421165337765030180174053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28561553783686706906898737 21421165337765030180174053)
              ·
                refine ⟨4016468500830943158782635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21421165337765030180174053 4016468500830943158782635)
                ·
                  refine ⟨6024702751246414738173953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4016468500830943158782635 6024702751246414738173953)
                  ·
                    refine ⟨4518527063434811053630465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024702751246414738173953 4518527063434811053630465)
                    ·
                      refine ⟨3388895297576108290222849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518527063434811053630465 3388895297576108290222849)
                      ·
                        rfl

theorem cell23_6599850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6599850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599850 prefixEnd_6599850 := by exact prefixLift 6599850
  have htrace : WordTrace (prefixWord ++ tailWord_6599850) baseStart_6599850 baseEnd_6599850 := by
    simpa [prefixWord, tailWord_6599850, baseEnd_6599850] using wordTrace_append hprefix tailTrace_6599850
  have hstable : (prefixWord ++ tailWord_6599850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599850).length < 2 ^ (prefixWord ++ tailWord_6599850).sum := by decide
  have hdescent : baseEnd_6599850 < baseStart_6599850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599855 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_6599855 : Nat := 118140960795 + 6599855 * 2 ^ 59
def prefixEnd_6599855 : Nat := 4983230072969 + 3 ^ 40 * 6599855 * 2
def baseEnd_6599855 : Nat := 3388897864979380770660325

theorem tailTrace_6599855 : CollatzResearch.WordTrace tailWord_6599855 prefixEnd_6599855 3388897864979380770660325 := by
  unfold tailWord_6599855
  simp only [CollatzResearch.WordTrace]
  refine ⟨240716487504859975340881019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160477658336573316893920679 240716487504859975340881019)
  ·
    refine ⟨361074731257289963011321529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240716487504859975340881019 361074731257289963011321529)
    ·
      refine ⟨270806048442967472258491147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361074731257289963011321529 270806048442967472258491147)
      ·
        refine ⟨406209072664451208387736721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270806048442967472258491147 406209072664451208387736721)
        ·
          refine ⟨304656804498338406290802541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406209072664451208387736721 304656804498338406290802541)
          ·
            refine ⟨114246301686876902359050953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304656804498338406290802541 114246301686876902359050953)
            ·
              refine ⟨85684726265157676769288215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114246301686876902359050953 85684726265157676769288215)
              ·
                refine ⟨128527089397736515153932323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85684726265157676769288215 128527089397736515153932323)
                ·
                  refine ⟨192790634096604772730898485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128527089397736515153932323 192790634096604772730898485)
                  ·
                    refine ⟨18074121946556697443521733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 192790634096604772730898485 18074121946556697443521733)
                    ·
                      refine ⟨3388897864979380770660325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18074121946556697443521733 3388897864979380770660325)
                      ·
                        rfl

theorem cell23_6599855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_6599855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599855 prefixEnd_6599855 := by exact prefixLift 6599855
  have htrace : WordTrace (prefixWord ++ tailWord_6599855) baseStart_6599855 baseEnd_6599855 := by
    simpa [prefixWord, tailWord_6599855, baseEnd_6599855] using wordTrace_append hprefix tailTrace_6599855
  have hstable : (prefixWord ++ tailWord_6599855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599855).length < 2 ^ (prefixWord ++ tailWord_6599855).sum := by decide
  have hdescent : baseEnd_6599855 < baseStart_6599855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599895 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 9]
def baseStart_6599895 : Nat := 118140960795 + 6599895 * 2 ^ 59
def prefixEnd_6599895 : Nat := 4983230072969 + 3 ^ 40 * 6599895 * 2
def baseEnd_6599895 : Nat := 376546489356173401573349

theorem tailTrace_6599895 : CollatzResearch.WordTrace tailWord_6599895 prefixEnd_6599895 376546489356173401573349 := by
  unfold tailWord_6599895
  simp only [CollatzResearch.WordTrace]
  refine ⟨240717946424715062172337139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160478630949810041448224759 240717946424715062172337139)
  ·
    refine ⟨361076919637072593258505709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240717946424715062172337139 361076919637072593258505709)
    ·
      refine ⟨135403844863902222471939641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361076919637072593258505709 135403844863902222471939641)
      ·
        refine ⟨101552883647926666853954731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135403844863902222471939641 101552883647926666853954731)
        ·
          refine ⟨152329325471890000280932097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101552883647926666853954731 152329325471890000280932097)
          ·
            refine ⟨114246994103917500210699073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152329325471890000280932097 114246994103917500210699073)
            ·
              refine ⟨85685245577938125158024305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114246994103917500210699073 85685245577938125158024305)
              ·
                refine ⟨64263934183453593868518229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85685245577938125158024305 64263934183453593868518229)
                ·
                  refine ⟨376546489356173401573349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64263934183453593868518229 376546489356173401573349)
                  ·
                    rfl

theorem cell23_6599895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 9].length) (baseStart_6599895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599895 prefixEnd_6599895 := by exact prefixLift 6599895
  have htrace : WordTrace (prefixWord ++ tailWord_6599895) baseStart_6599895 baseEnd_6599895 := by
    simpa [prefixWord, tailWord_6599895, baseEnd_6599895] using wordTrace_append hprefix tailTrace_6599895
  have hstable : (prefixWord ++ tailWord_6599895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599895).length < 2 ^ (prefixWord ++ tailWord_6599895).sum := by decide
  have hdescent : baseEnd_6599895 < baseStart_6599895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599923 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 2, 2, 2]
def baseStart_6599923 : Nat := 118140960795 + 6599923 * 2 ^ 59
def prefixEnd_6599923 : Nat := 4983230072969 + 3 ^ 40 * 6599923 * 2
def baseEnd_6599923 : Nat := 3388932781663886504610013

theorem tailTrace_6599923 : CollatzResearch.WordTrace tailWord_6599923 prefixEnd_6599923 3388932781663886504610013 := by
  unfold tailWord_6599923
  simp only [CollatzResearch.WordTrace]
  refine ⟨240718967668613622954356423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160479311779075748636237615 240718967668613622954356423)
  ·
    refine ⟨361078451502920434431534635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240718967668613622954356423 361078451502920434431534635)
    ·
      refine ⟨541617677254380651647301953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361078451502920434431534635 541617677254380651647301953)
      ·
        refine ⟨406213257940785488735476465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541617677254380651647301953 406213257940785488735476465)
        ·
          refine ⟨304659943455589116551607349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406213257940785488735476465 304659943455589116551607349)
          ·
            refine ⟨28561869698961479676713189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304659943455589116551607349 28561869698961479676713189)
            ·
              refine ⟨5355350568555277439383723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28561869698961479676713189 5355350568555277439383723)
              ·
                refine ⟨8033025852832916159075585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355350568555277439383723 8033025852832916159075585)
                ·
                  refine ⟨6024769389624687119306689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8033025852832916159075585 6024769389624687119306689)
                  ·
                    refine ⟨4518577042218515339480017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024769389624687119306689 4518577042218515339480017)
                    ·
                      refine ⟨3388932781663886504610013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518577042218515339480017 3388932781663886504610013)
                      ·
                        rfl

theorem cell23_6599923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 2, 2, 2].length) (baseStart_6599923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599923 prefixEnd_6599923 := by exact prefixLift 6599923
  have htrace : WordTrace (prefixWord ++ tailWord_6599923) baseStart_6599923 baseEnd_6599923 := by
    simpa [prefixWord, tailWord_6599923, baseEnd_6599923] using wordTrace_append hprefix tailTrace_6599923
  have hstable : (prefixWord ++ tailWord_6599923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599923).length < 2 ^ (prefixWord ++ tailWord_6599923).sum := by decide
  have hdescent : baseEnd_6599923 < baseStart_6599923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599989 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6599989 : Nat := 118140960795 + 6599989 * 2 ^ 59
def prefixEnd_6599989 : Nat := 4983230072969 + 3 ^ 40 * 6599989 * 2
def baseEnd_6599989 : Nat := 1129655557129027748794903

theorem tailTrace_6599989 : CollatzResearch.WordTrace tailWord_6599989 prefixEnd_6599989 1129655557129027748794903 := by
  unfold tailWord_6599989
  simp only [CollatzResearch.WordTrace]
  refine ⟨240721374886374516226259021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160480916590916344150839347 240721374886374516226259021)
  ·
    refine ⟨90270515582390443584847133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240721374886374516226259021 90270515582390443584847133)
    ·
      refine ⟨33851443343396416344317675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90270515582390443584847133 33851443343396416344317675)
      ·
        refine ⟨50777165015094624516476513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33851443343396416344317675 50777165015094624516476513)
        ·
          refine ⟨38082873761320968387357385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50777165015094624516476513 38082873761320968387357385)
          ·
            refine ⟨28562155320990726290518039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38082873761320968387357385 28562155320990726290518039)
            ·
              refine ⟨42843232981486089435777059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28562155320990726290518039 42843232981486089435777059)
              ·
                refine ⟨64264849472229134153665589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42843232981486089435777059 64264849472229134153665589)
                ·
                  refine ⟨6024829638021481326906149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64264849472229134153665589 6024829638021481326906149)
                  ·
                    refine ⟨1129655557129027748794903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6024829638021481326906149 1129655557129027748794903)
                    ·
                      rfl

theorem cell23_6599989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6599989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599989 prefixEnd_6599989 := by exact prefixLift 6599989
  have htrace : WordTrace (prefixWord ++ tailWord_6599989) baseStart_6599989 baseEnd_6599989 := by
    simpa [prefixWord, tailWord_6599989, baseEnd_6599989] using wordTrace_append hprefix tailTrace_6599989
  have hstable : (prefixWord ++ tailWord_6599989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599989).length < 2 ^ (prefixWord ++ tailWord_6599989).sum := by decide
  have hdescent : baseEnd_6599989 < baseStart_6599989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599993 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_6599993 : Nat := 118140960795 + 6599993 * 2 ^ 59
def prefixEnd_6599993 : Nat := 4983230072969 + 3 ^ 40 * 6599993 * 2
def baseEnd_6599993 : Nat := 1129656241769900410244897

theorem tailTrace_6599993 : CollatzResearch.WordTrace tailWord_6599993 prefixEnd_6599993 1129656241769900410244897 := by
  unfold tailWord_6599993
  simp only [CollatzResearch.WordTrace]
  refine ⟨240721520778360024909404633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160481013852240016606269755 240721520778360024909404633)
  ·
    refine ⟨180541140583770018682053475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240721520778360024909404633 180541140583770018682053475)
    ·
      refine ⟨270811710875655028023080213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180541140583770018682053475 270811710875655028023080213)
      ·
        refine ⟨12694298947296329438581885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270811710875655028023080213 12694298947296329438581885)
        ·
          refine ⟨4760362105236123539468207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12694298947296329438581885 4760362105236123539468207)
          ·
            refine ⟨7140543157854185309202311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760362105236123539468207 7140543157854185309202311)
            ·
              refine ⟨10710814736781277963803467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140543157854185309202311 10710814736781277963803467)
              ·
                refine ⟨16066222105171916945705201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10710814736781277963803467 16066222105171916945705201)
                ·
                  refine ⟨12049666578878937709278901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16066222105171916945705201 12049666578878937709278901)
                  ·
                    refine ⟨1129656241769900410244897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12049666578878937709278901 1129656241769900410244897)
                    ·
                      rfl

theorem cell23_6599993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_6599993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599993 prefixEnd_6599993 := by exact prefixLift 6599993
  have htrace : WordTrace (prefixWord ++ tailWord_6599993) baseStart_6599993 baseEnd_6599993 := by
    simpa [prefixWord, tailWord_6599993, baseEnd_6599993] using wordTrace_append hprefix tailTrace_6599993
  have hstable : (prefixWord ++ tailWord_6599993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599993).length < 2 ^ (prefixWord ++ tailWord_6599993).sum := by decide
  have hdescent : baseEnd_6599993 < baseStart_6599993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599996 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_6599996 : Nat := 118140960795 + 6599996 * 2 ^ 59
def prefixEnd_6599996 : Nat := 4983230072969 + 3 ^ 40 * 6599996 * 2
def baseEnd_6599996 : Nat := 3388970265751664718997177

theorem tailTrace_6599996 : CollatzResearch.WordTrace tailWord_6599996 prefixEnd_6599996 3388970265751664718997177 := by
  unfold tailWord_6599996
  simp only [CollatzResearch.WordTrace]
  refine ⟨120360815098674578210881921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160481086798232770947842561 120360815098674578210881921)
  ·
    refine ⟨90270611324005933658161441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120360815098674578210881921 90270611324005933658161441)
    ·
      refine ⟨67702958493004450243621081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90270611324005933658161441 67702958493004450243621081)
      ·
        refine ⟨50777218869753337682715811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67702958493004450243621081 50777218869753337682715811)
        ·
          refine ⟨76165828304630006524073717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50777218869753337682715811 76165828304630006524073717)
          ·
            refine ⟨7140546403559063111631911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76165828304630006524073717 7140546403559063111631911)
            ·
              refine ⟨10710819605338594667447867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140546403559063111631911 10710819605338594667447867)
              ·
                refine ⟨16066229408007892001171801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10710819605338594667447867 16066229408007892001171801)
                ·
                  refine ⟨12049672056005919000878851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16066229408007892001171801 12049672056005919000878851)
                  ·
                    refine ⟨18074508084008878501318277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12049672056005919000878851 18074508084008878501318277)
                    ·
                      refine ⟨3388970265751664718997177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18074508084008878501318277 3388970265751664718997177)
                      ·
                        rfl

theorem cell23_6599996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_6599996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599996 prefixEnd_6599996 := by exact prefixLift 6599996
  have htrace : WordTrace (prefixWord ++ tailWord_6599996) baseStart_6599996 baseEnd_6599996 := by
    simpa [prefixWord, tailWord_6599996, baseEnd_6599996] using wordTrace_append hprefix tailTrace_6599996
  have hstable : (prefixWord ++ tailWord_6599996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599996).length < 2 ^ (prefixWord ++ tailWord_6599996).sum := by decide
  have hdescent : baseEnd_6599996 < baseStart_6599996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599999 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_6599999 : Nat := 118140960795 + 6599999 * 2 ^ 59
def prefixEnd_6599999 : Nat := 4983230072969 + 3 ^ 40 * 6599999 * 2
def baseEnd_6599999 : Nat := 3388971806193628207259663

theorem tailTrace_6599999 : CollatzResearch.WordTrace tailWord_6599999 prefixEnd_6599999 3388971806193628207259663 := by
  unfold tailWord_6599999
  simp only [CollatzResearch.WordTrace]
  refine ⟨240721739616338287934123051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160481159744225525289415367 240721739616338287934123051)
  ·
    refine ⟨361082609424507431901184577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240721739616338287934123051 361082609424507431901184577)
    ·
      refine ⟨270811957068380573925888433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361082609424507431901184577 270811957068380573925888433)
      ·
        refine ⟨203108967801285430444416325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270811957068380573925888433 203108967801285430444416325)
        ·
          refine ⟨38082931462741018208328061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203108967801285430444416325 38082931462741018208328061)
          ·
            refine ⟨14281099298527881828123023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38082931462741018208328061 14281099298527881828123023)
            ·
              refine ⟨21421648947791822742184535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14281099298527881828123023 21421648947791822742184535)
              ·
                refine ⟨32132473421687734113276803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21421648947791822742184535 32132473421687734113276803)
                ·
                  refine ⟨48198710132531601169915205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32132473421687734113276803 48198710132531601169915205)
                  ·
                    refine ⟨9037258149849675219359101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48198710132531601169915205 9037258149849675219359101)
                    ·
                      refine ⟨3388971806193628207259663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037258149849675219359101 3388971806193628207259663)
                      ·
                        rfl

theorem cell23_6599999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_6599999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6599999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6599999 prefixEnd_6599999 := by exact prefixLift 6599999
  have htrace : WordTrace (prefixWord ++ tailWord_6599999) baseStart_6599999 baseEnd_6599999 := by
    simpa [prefixWord, tailWord_6599999, baseEnd_6599999] using wordTrace_append hprefix tailTrace_6599999
  have hstable : (prefixWord ++ tailWord_6599999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599999).length < 2 ^ (prefixWord ++ tailWord_6599999).sum := by decide
  have hdescent : baseEnd_6599999 < baseStart_6599999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600036 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 6]
def baseStart_6600036 : Nat := 118140960795 + 6600036 * 2 ^ 59
def prefixEnd_6600036 : Nat := 4983230072969 + 3 ^ 40 * 6600036 * 2
def baseEnd_6600036 : Nat := 376554533886427173610777

theorem tailTrace_6600036 : CollatzResearch.WordTrace tailWord_6600036 prefixEnd_6600036 376554533886427173610777 := by
  unfold tailWord_6600036
  simp only [CollatzResearch.WordTrace]
  refine ⟨120361544558602121626609981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160482059411469495502146641 120361544558602121626609981)
  ·
    refine ⟨45135579209475795609978743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120361544558602121626609981 45135579209475795609978743)
    ·
      refine ⟨67703368814213693414968115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45135579209475795609978743 67703368814213693414968115)
      ·
        refine ⟨101555053221320540122452173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67703368814213693414968115 101555053221320540122452173)
        ·
          refine ⟨38083144957995202545919565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101555053221320540122452173 38083144957995202545919565)
          ·
            refine ⟨14281179359248200954719837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38083144957995202545919565 14281179359248200954719837)
            ·
              refine ⟨5355442259718075358019939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14281179359248200954719837 5355442259718075358019939)
              ·
                refine ⟨8033163389577113037029909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355442259718075358019939 8033163389577113037029909)
                ·
                  refine ⟨376554533886427173610777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8033163389577113037029909 376554533886427173610777)
                  ·
                    rfl

theorem cell23_6600036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_6600036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600036 prefixEnd_6600036 := by exact prefixLift 6600036
  have htrace : WordTrace (prefixWord ++ tailWord_6600036) baseStart_6600036 baseEnd_6600036 := by
    simpa [prefixWord, tailWord_6600036, baseEnd_6600036] using wordTrace_append hprefix tailTrace_6600036
  have hstable : (prefixWord ++ tailWord_6600036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600036).length < 2 ^ (prefixWord ++ tailWord_6600036).sum := by decide
  have hdescent : baseEnd_6600036 < baseStart_6600036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600049 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_6600049 : Nat := 118140960795 + 6600049 * 2 ^ 59
def prefixEnd_6600049 : Nat := 4983230072969 + 3 ^ 40 * 6600049 * 2
def baseEnd_6600049 : Nat := 1129665826742117670544811

theorem tailTrace_6600049 : CollatzResearch.WordTrace tailWord_6600049 prefixEnd_6600049 1129665826742117670544811 := by
  unfold tailWord_6600049
  simp only [CollatzResearch.WordTrace]
  refine ⟨240723563266157146473443201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160482375510771430982295467 240723563266157146473443201)
  ·
    refine ⟨180542672449617859855082401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240723563266157146473443201 180542672449617859855082401)
    ·
      refine ⟨135407004337213394891311801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180542672449617859855082401 135407004337213394891311801)
      ·
        refine ⟨101555253252910046168483851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135407004337213394891311801 101555253252910046168483851)
        ·
          refine ⟨152332879879365069252725777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101555253252910046168483851 152332879879365069252725777)
          ·
            refine ⟨114249659909523801939544333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152332879879365069252725777 114249659909523801939544333)
            ·
              refine ⟨42843622466071425727329125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114249659909523801939544333 42843622466071425727329125)
              ·
                refine ⟨8033179212388392323874211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42843622466071425727329125 8033179212388392323874211)
                ·
                  refine ⟨12049768818582588485811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8033179212388392323874211 12049768818582588485811317)
                  ·
                    refine ⟨1129665826742117670544811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12049768818582588485811317 1129665826742117670544811)
                    ·
                      rfl

theorem cell23_6600049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_6600049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600049 prefixEnd_6600049 := by exact prefixLift 6600049
  have htrace : WordTrace (prefixWord ++ tailWord_6600049) baseStart_6600049 baseEnd_6600049 := by
    simpa [prefixWord, tailWord_6600049, baseEnd_6600049] using wordTrace_append hprefix tailTrace_6600049
  have hstable : (prefixWord ++ tailWord_6600049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600049).length < 2 ^ (prefixWord ++ tailWord_6600049).sum := by decide
  have hdescent : baseEnd_6600049 < baseStart_6600049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600073 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 2, 3, 2]
def baseStart_6600073 : Nat := 118140960795 + 6600073 * 2 ^ 59
def prefixEnd_6600073 : Nat := 4983230072969 + 3 ^ 40 * 6600073 * 2
def baseEnd_6600073 : Nat := 3389009803762060917734323

theorem tailTrace_6600073 : CollatzResearch.WordTrace tailWord_6600073 prefixEnd_6600073 3389009803762060917734323 := by
  unfold tailWord_6600073
  simp only [CollatzResearch.WordTrace]
  refine ⟨240724438618070198572316873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160482959078713465714877915 240724438618070198572316873)
  ·
    refine ⟨180543328963552648929237655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240724438618070198572316873 180543328963552648929237655)
    ·
      refine ⟨270814993445328973393856483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180543328963552648929237655 270814993445328973393856483)
      ·
        refine ⟨406222490167993460090784725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270814993445328973393856483 406222490167993460090784725)
        ·
          refine ⟨9520839613312346720877767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 406222490167993460090784725 9520839613312346720877767)
          ·
            refine ⟨14281259419968520081316651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520839613312346720877767 14281259419968520081316651)
            ·
              refine ⟨21421889129952780121974977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14281259419968520081316651 21421889129952780121974977)
              ·
                refine ⟨16066416847464585091481233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21421889129952780121974977 16066416847464585091481233)
                ·
                  refine ⟨12049812635598438818610925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16066416847464585091481233 12049812635598438818610925)
                  ·
                    refine ⟨4518679738349414556979097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12049812635598438818610925 4518679738349414556979097)
                    ·
                      refine ⟨3389009803762060917734323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518679738349414556979097 3389009803762060917734323)
                      ·
                        rfl

theorem cell23_6600073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 3, 2].length) (baseStart_6600073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600073 prefixEnd_6600073 := by exact prefixLift 6600073
  have htrace : WordTrace (prefixWord ++ tailWord_6600073) baseStart_6600073 baseEnd_6600073 := by
    simpa [prefixWord, tailWord_6600073, baseEnd_6600073] using wordTrace_append hprefix tailTrace_6600073
  have hstable : (prefixWord ++ tailWord_6600073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600073).length < 2 ^ (prefixWord ++ tailWord_6600073).sum := by decide
  have hdescent : baseEnd_6600073 < baseStart_6600073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600089 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_6600089 : Nat := 118140960795 + 6600089 * 2 ^ 59
def prefixEnd_6600089 : Nat := 4983230072969 + 3 ^ 40 * 6600089 * 2
def baseEnd_6600089 : Nat := 3389018019452532855134249

theorem tailTrace_6600089 : CollatzResearch.WordTrace tailWord_6600089 prefixEnd_6600089 3389018019452532855134249 := by
  unfold tailWord_6600089
  simp only [CollatzResearch.WordTrace]
  refine ⟨240725022186012233304899321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160483348124008155536599547 240725022186012233304899321)
  ·
    refine ⟨180543766639509174978674491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240725022186012233304899321 180543766639509174978674491)
    ·
      refine ⟨270815649959263762468011737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180543766639509174978674491 270815649959263762468011737)
      ·
        refine ⟨203111737469447821851008803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270815649959263762468011737 203111737469447821851008803)
        ·
          refine ⟨304667606204171732776513205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203111737469447821851008803 304667606204171732776513205)
          ·
            refine ⟨28562588081641099947798113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304667606204171732776513205 28562588081641099947798113)
            ·
              refine ⟨21421941061230824960848585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28562588081641099947798113 21421941061230824960848585)
              ·
                refine ⟨16066455795923118720636439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21421941061230824960848585 16066455795923118720636439)
                ·
                  refine ⟨24099683693884678080954659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16066455795923118720636439 24099683693884678080954659)
                  ·
                    refine ⟨36149525540827017121431989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24099683693884678080954659 36149525540827017121431989)
                    ·
                      refine ⟨3389018019452532855134249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36149525540827017121431989 3389018019452532855134249)
                      ·
                        rfl

theorem cell23_6600089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_6600089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600089 prefixEnd_6600089 := by exact prefixLift 6600089
  have htrace : WordTrace (prefixWord ++ tailWord_6600089) baseStart_6600089 baseEnd_6600089 := by
    simpa [prefixWord, tailWord_6600089, baseEnd_6600089] using wordTrace_append hprefix tailTrace_6600089
  have hstable : (prefixWord ++ tailWord_6600089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600089).length < 2 ^ (prefixWord ++ tailWord_6600089).sum := by decide
  have hdescent : baseEnd_6600089 < baseStart_6600089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600096 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 2, 4]
def baseStart_6600096 : Nat := 118140960795 + 6600096 * 2 ^ 59
def prefixEnd_6600096 : Nat := 4983230072969 + 3 ^ 40 * 6600096 * 2
def baseEnd_6600096 : Nat := 1129673871272371442582239

theorem tailTrace_6600096 : CollatzResearch.WordTrace tailWord_6600096 prefixEnd_6600096 1129673871272371442582239 := by
  unfold tailWord_6600096
  simp only [CollatzResearch.WordTrace]
  refine ⟨120362638748493436750202071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160483518331324582333602761 120362638748493436750202071)
  ·
    refine ⟨180543958122740155125303107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120362638748493436750202071 180543958122740155125303107)
    ·
      refine ⟨270815937184110232687954661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180543958122740155125303107 270815937184110232687954661)
      ·
        refine ⟨50777988222020668628991499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270815937184110232687954661 50777988222020668628991499)
        ·
          refine ⟨76166982333031002943487249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50777988222020668628991499 76166982333031002943487249)
          ·
            refine ⟨57125236749773252207615437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76166982333031002943487249 57125236749773252207615437)
            ·
              refine ⟨21421963781164969577855789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57125236749773252207615437 21421963781164969577855789)
              ·
                refine ⟨8033236417936863591695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21421963781164969577855789 8033236417936863591695921)
                ·
                  refine ⟨6024927313452647693771941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8033236417936863591695921 6024927313452647693771941)
                  ·
                    refine ⟨1129673871272371442582239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6024927313452647693771941 1129673871272371442582239)
                    ·
                      rfl

theorem cell23_6600096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_6600096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600096 prefixEnd_6600096 := by exact prefixLift 6600096
  have htrace : WordTrace (prefixWord ++ tailWord_6600096) baseStart_6600096 baseEnd_6600096 := by
    simpa [prefixWord, tailWord_6600096, baseEnd_6600096] using wordTrace_append hprefix tailTrace_6600096
  have hstable : (prefixWord ++ tailWord_6600096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600096).length < 2 ^ (prefixWord ++ tailWord_6600096).sum := by decide
  have hdescent : baseEnd_6600096 < baseStart_6600096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600099 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_6600099 : Nat := 118140960795 + 6600099 * 2 ^ 59
def prefixEnd_6600099 : Nat := 4983230072969 + 3 ^ 40 * 6600099 * 2
def baseEnd_6600099 : Nat := 3389023154259077816009203

theorem tailTrace_6600099 : CollatzResearch.WordTrace tailWord_6600099 prefixEnd_6600099 3389023154259077816009203 := by
  unfold tailWord_6600099
  simp only [CollatzResearch.WordTrace]
  refine ⟨240725386915976005012763351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160483591277317336675175567 240725386915976005012763351)
  ·
    refine ⟨361088080373964007519145027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240725386915976005012763351 361088080373964007519145027)
    ·
      refine ⟨541632120560946011278717541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361088080373964007519145027 541632120560946011278717541)
      ·
        refine ⟨101556022605177377114759539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541632120560946011278717541 101556022605177377114759539)
        ·
          refine ⟨152334033907766065672139309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101556022605177377114759539 152334033907766065672139309)
          ·
            refine ⟨57125262715412274627052241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152334033907766065672139309 57125262715412274627052241)
            ·
              refine ⟨42843947036559205970289181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57125262715412274627052241 42843947036559205970289181)
              ·
                refine ⟨16066480138709702238858443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42843947036559205970289181 16066480138709702238858443)
                ·
                  refine ⟨24099720208064553358287665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16066480138709702238858443 24099720208064553358287665)
                  ·
                    refine ⟨18074790156048415018715749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24099720208064553358287665 18074790156048415018715749)
                    ·
                      refine ⟨3389023154259077816009203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18074790156048415018715749 3389023154259077816009203)
                      ·
                        rfl

theorem cell23_6600099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_6600099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600099 prefixEnd_6600099 := by exact prefixLift 6600099
  have htrace : WordTrace (prefixWord ++ tailWord_6600099) baseStart_6600099 baseEnd_6600099 := by
    simpa [prefixWord, tailWord_6600099, baseEnd_6600099] using wordTrace_append hprefix tailTrace_6600099
  have hstable : (prefixWord ++ tailWord_6600099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600099).length < 2 ^ (prefixWord ++ tailWord_6600099).sum := by decide
  have hdescent : baseEnd_6600099 < baseStart_6600099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600103 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6600103 : Nat := 118140960795 + 6600103 * 2 ^ 59
def prefixEnd_6600103 : Nat := 4983230072969 + 3 ^ 40 * 6600103 * 2
def baseEnd_6600103 : Nat := 3389025208181695800359185

theorem tailTrace_6600103 : CollatzResearch.WordTrace tailWord_6600103 prefixEnd_6600103 3389025208181695800359185 := by
  unfold tailWord_6600103
  simp only [CollatzResearch.WordTrace]
  refine ⟨240725532807961513695908963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160483688538641009130605975 240725532807961513695908963)
  ·
    refine ⟨361088299211942270543863445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240725532807961513695908963 361088299211942270543863445)
    ·
      refine ⟨16926014025559793931743599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 361088299211942270543863445 16926014025559793931743599)
      ·
        refine ⟨25389021038339690897615399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16926014025559793931743599 25389021038339690897615399)
        ·
          refine ⟨38083531557509536346423099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25389021038339690897615399 38083531557509536346423099)
          ·
            refine ⟨57125297336264304519634649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083531557509536346423099 57125297336264304519634649)
            ·
              refine ⟨42843973002198228389725987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57125297336264304519634649 42843973002198228389725987)
              ·
                refine ⟨64265959503297342584588981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42843973002198228389725987 64265959503297342584588981)
                ·
                  refine ⟨6024933703434125867305217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64265959503297342584588981 6024933703434125867305217)
                  ·
                    refine ⟨4518700277575594400478913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6024933703434125867305217 4518700277575594400478913)
                    ·
                      refine ⟨3389025208181695800359185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518700277575594400478913 3389025208181695800359185)
                      ·
                        rfl

theorem cell23_6600103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6600103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600103 prefixEnd_6600103 := by exact prefixLift 6600103
  have htrace : WordTrace (prefixWord ++ tailWord_6600103) baseStart_6600103 baseEnd_6600103 := by
    simpa [prefixWord, tailWord_6600103, baseEnd_6600103] using wordTrace_append hprefix tailTrace_6600103
  have hstable : (prefixWord ++ tailWord_6600103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600103).length < 2 ^ (prefixWord ++ tailWord_6600103).sum := by decide
  have hdescent : baseEnd_6600103 < baseStart_6600103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600153 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_6600153 : Nat := 118140960795 + 6600153 * 2 ^ 59
def prefixEnd_6600153 : Nat := 4983230072969 + 3 ^ 40 * 6600153 * 2
def baseEnd_6600153 : Nat := 3389050882214420604733955

theorem tailTrace_6600153 : CollatzResearch.WordTrace tailWord_6600153 prefixEnd_6600153 3389050882214420604733955 := by
  unfold tailWord_6600153
  simp only [CollatzResearch.WordTrace]
  refine ⟨240727356457780372235229113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160484904305186914823486075 240727356457780372235229113)
  ·
    refine ⟨180545517343335279176421835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240727356457780372235229113 180545517343335279176421835)
    ·
      refine ⟨270818276015002918764632753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180545517343335279176421835 270818276015002918764632753)
      ·
        refine ⟨203113707011252189073474565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270818276015002918764632753 203113707011252189073474565)
        ·
          refine ⟨38083820064609785451276481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203113707011252189073474565 38083820064609785451276481)
          ·
            refine ⟨28562865048457339088457361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38083820064609785451276481 28562865048457339088457361)
            ·
              refine ⟨21422148786343004316343021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28562865048457339088457361 21422148786343004316343021)
              ·
                refine ⟨8033305794878626618628633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21422148786343004316343021 8033305794878626618628633)
                ·
                  refine ⟨6024979346158969963971475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8033305794878626618628633 6024979346158969963971475)
                  ·
                    refine ⟨9037469019238454945957213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6024979346158969963971475 9037469019238454945957213)
                    ·
                      refine ⟨3389050882214420604733955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037469019238454945957213 3389050882214420604733955)
                      ·
                        rfl

theorem cell23_6600153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_6600153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600153 prefixEnd_6600153 := by exact prefixLift 6600153
  have htrace : WordTrace (prefixWord ++ tailWord_6600153) baseStart_6600153 baseEnd_6600153 := by
    simpa [prefixWord, tailWord_6600153, baseEnd_6600153] using wordTrace_append hprefix tailTrace_6600153
  have hstable : (prefixWord ++ tailWord_6600153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600153).length < 2 ^ (prefixWord ++ tailWord_6600153).sum := by decide
  have hdescent : baseEnd_6600153 < baseStart_6600153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600159 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_6600159 : Nat := 118140960795 + 6600159 * 2 ^ 59
def prefixEnd_6600159 : Nat := 4983230072969 + 3 ^ 40 * 6600159 * 2
def baseEnd_6600159 : Nat := 3389053963098347581258927

theorem tailTrace_6600159 : CollatzResearch.WordTrace tailWord_6600159 prefixEnd_6600159 3389053963098347581258927 := by
  unfold tailWord_6600159
  simp only [CollatzResearch.WordTrace]
  refine ⟨240727575295758635259947531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160485050197172423506631687 240727575295758635259947531)
  ·
    refine ⟨361091362943637952889921297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240727575295758635259947531 361091362943637952889921297)
    ·
      refine ⟨270818522207728464667440973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361091362943637952889921297 270818522207728464667440973)
      ·
        refine ⟨101556945827898174250290365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270818522207728464667440973 101556945827898174250290365)
        ·
          refine ⟨38083854685461815343858887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101556945827898174250290365 38083854685461815343858887)
          ·
            refine ⟨57125782028192723015788331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083854685461815343858887 57125782028192723015788331)
            ·
              refine ⟨85688673042289084523682497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57125782028192723015788331 85688673042289084523682497)
              ·
                refine ⟨64266504781716813392761873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85688673042289084523682497 64266504781716813392761873)
                ·
                  refine ⟨48199878586287610044571405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64266504781716813392761873 48199878586287610044571405)
                  ·
                    refine ⟨18074954469857853766714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48199878586287610044571405 18074954469857853766714277)
                    ·
                      refine ⟨3389053963098347581258927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18074954469857853766714277 3389053963098347581258927)
                      ·
                        rfl

theorem cell23_6600159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_6600159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600159 prefixEnd_6600159 := by exact prefixLift 6600159
  have htrace : WordTrace (prefixWord ++ tailWord_6600159) baseStart_6600159 baseEnd_6600159 := by
    simpa [prefixWord, tailWord_6600159, baseEnd_6600159] using wordTrace_append hprefix tailTrace_6600159
  have hstable : (prefixWord ++ tailWord_6600159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600159).length < 2 ^ (prefixWord ++ tailWord_6600159).sum := by decide
  have hdescent : baseEnd_6600159 < baseStart_6600159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600163 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6600163 : Nat := 118140960795 + 6600163 * 2 ^ 59
def prefixEnd_6600163 : Nat := 4983230072969 + 3 ^ 40 * 6600163 * 2
def baseEnd_6600163 : Nat := 3389056017020965565608909

theorem tailTrace_6600163 : CollatzResearch.WordTrace tailWord_6600163 prefixEnd_6600163 3389056017020965565608909 := by
  unfold tailWord_6600163
  simp only [CollatzResearch.WordTrace]
  refine ⟨240727721187744143943093143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160485147458496095962062095 240727721187744143943093143)
  ·
    refine ⟨361091581781616215914639715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240727721187744143943093143 361091581781616215914639715)
    ·
      refine ⟨541637372672424323871959573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361091581781616215914639715 541637372672424323871959573)
      ·
        refine ⟨25389251844019890181498105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 541637372672424323871959573 25389251844019890181498105)
        ·
          refine ⟨19041938883014917636123579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25389251844019890181498105 19041938883014917636123579)
          ·
            refine ⟨28562908324522376454185369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19041938883014917636123579 28562908324522376454185369)
            ·
              refine ⟨21422181243391782340639027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28562908324522376454185369 21422181243391782340639027)
              ·
                refine ⟨32133271865087673510958541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21422181243391782340639027 32133271865087673510958541)
                ·
                  refine ⟨12049976949407877566609453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32133271865087673510958541 12049976949407877566609453)
                  ·
                    refine ⟨4518741356027954087478545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12049976949407877566609453 4518741356027954087478545)
                    ·
                      refine ⟨3389056017020965565608909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518741356027954087478545 3389056017020965565608909)
                      ·
                        rfl

theorem cell23_6600163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6600163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600163 prefixEnd_6600163 := by exact prefixLift 6600163
  have htrace : WordTrace (prefixWord ++ tailWord_6600163) baseStart_6600163 baseEnd_6600163 := by
    simpa [prefixWord, tailWord_6600163, baseEnd_6600163] using wordTrace_append hprefix tailTrace_6600163
  have hstable : (prefixWord ++ tailWord_6600163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600163).length < 2 ^ (prefixWord ++ tailWord_6600163).sum := by decide
  have hdescent : baseEnd_6600163 < baseStart_6600163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600179 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3]
def baseStart_6600179 : Nat := 118140960795 + 6600179 * 2 ^ 59
def prefixEnd_6600179 : Nat := 4983230072969 + 3 ^ 40 * 6600179 * 2
def baseEnd_6600179 : Nat := 3389064232711437503008835

theorem tailTrace_6600179 : CollatzResearch.WordTrace tailWord_6600179 prefixEnd_6600179 3389064232711437503008835 := by
  unfold tailWord_6600179
  simp only [CollatzResearch.WordTrace]
  refine ⟨240728304755686178675675591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160485536503790785783783727 240728304755686178675675591)
  ·
    refine ⟨361092457133529268013513387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240728304755686178675675591 361092457133529268013513387)
    ·
      refine ⟨541638685700293902020270081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361092457133529268013513387 541638685700293902020270081)
      ·
        refine ⟨406229014275220426515202561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541638685700293902020270081 406229014275220426515202561)
        ·
          refine ⟨304671760706415319886401921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406229014275220426515202561 304671760706415319886401921)
          ·
            refine ⟨228503820529811489914801441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304671760706415319886401921 228503820529811489914801441)
            ·
              refine ⟨171377865397358617436101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228503820529811489914801441 171377865397358617436101081)
              ·
                refine ⟨128533399048018963077075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171377865397358617436101081 128533399048018963077075811)
                ·
                  refine ⟨192800098572028444615613717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128533399048018963077075811 192800098572028444615613717)
                  ·
                    refine ⟨9037504620563833341356893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192800098572028444615613717 9037504620563833341356893)
                    ·
                      refine ⟨3389064232711437503008835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037504620563833341356893 3389064232711437503008835)
                      ·
                        rfl

theorem cell23_6600179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_6600179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600179 prefixEnd_6600179 := by exact prefixLift 6600179
  have htrace : WordTrace (prefixWord ++ tailWord_6600179) baseStart_6600179 baseEnd_6600179 := by
    simpa [prefixWord, tailWord_6600179, baseEnd_6600179] using wordTrace_append hprefix tailTrace_6600179
  have hstable : (prefixWord ++ tailWord_6600179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600179).length < 2 ^ (prefixWord ++ tailWord_6600179).sum := by decide
  have hdescent : baseEnd_6600179 < baseStart_6600179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600226 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_6600226 : Nat := 118140960795 + 6600226 * 2 ^ 59
def prefixEnd_6600226 : Nat := 4983230072969 + 3 ^ 40 * 6600226 * 2
def baseEnd_6600226 : Nat := 3389088366302198819121119

theorem tailTrace_6600226 : CollatzResearch.WordTrace tailWord_6600226 prefixEnd_6600226 3389088366302198819121119 := by
  unfold tailWord_6600226
  simp only [CollatzResearch.WordTrace]
  refine ⟨60182504746628976425659133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160486679324343937135091021 60182504746628976425659133)
  ·
    refine ⟨22568439279985866159622175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60182504746628976425659133 22568439279985866159622175)
    ·
      refine ⟨33852658919978799239433263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22568439279985866159622175 33852658919978799239433263)
      ·
        refine ⟨50778988379968198859149895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33852658919978799239433263 50778988379968198859149895)
        ·
          refine ⟨76168482569952298288724843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50778988379968198859149895 76168482569952298288724843)
          ·
            refine ⟨114252723854928447433087265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76168482569952298288724843 114252723854928447433087265)
            ·
              refine ⟨85689542891196335574815449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114252723854928447433087265 85689542891196335574815449)
              ·
                refine ⟨64267157168397251681111587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85689542891196335574815449 64267157168397251681111587)
                ·
                  refine ⟨96400735752595877521667381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64267157168397251681111587 96400735752595877521667381)
                  ·
                    refine ⟨9037568976805863517656317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96400735752595877521667381 9037568976805863517656317)
                    ·
                      refine ⟨3389088366302198819121119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037568976805863517656317 3389088366302198819121119)
                      ·
                        rfl

theorem cell23_6600226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_6600226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600226 prefixEnd_6600226 := by exact prefixLift 6600226
  have htrace : WordTrace (prefixWord ++ tailWord_6600226) baseStart_6600226 baseEnd_6600226 := by
    simpa [prefixWord, tailWord_6600226, baseEnd_6600226] using wordTrace_append hprefix tailTrace_6600226
  have hstable : (prefixWord ++ tailWord_6600226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600226).length < 2 ^ (prefixWord ++ tailWord_6600226).sum := by decide
  have hdescent : baseEnd_6600226 < baseStart_6600226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600236 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 3, 7, 2]
def baseStart_6600236 : Nat := 118140960795 + 6600236 * 2 ^ 59
def prefixEnd_6600236 : Nat := 4983230072969 + 3 ^ 40 * 6600236 * 2
def baseEnd_6600236 : Nat := 3389093501108743779996073

theorem tailTrace_6600236 : CollatzResearch.WordTrace tailWord_6600236 prefixEnd_6600236 3389093501108743779996073 := by
  unfold tailWord_6600236
  simp only [CollatzResearch.WordTrace]
  refine ⟨120365191858239838705250281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160486922477653118273667041 120365191858239838705250281)
  ·
    refine ⟨90273893893679879028937711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120365191858239838705250281 90273893893679879028937711)
    ·
      refine ⟨135410840840519818543406567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90273893893679879028937711 135410840840519818543406567)
      ·
        refine ⟨203116261260779727815109851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135410840840519818543406567 203116261260779727815109851)
        ·
          refine ⟨304674391891169591722664777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203116261260779727815109851 304674391891169591722664777)
          ·
            refine ⟨228505793918377193791998583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304674391891169591722664777 228505793918377193791998583)
            ·
              refine ⟨342758690877565790687997875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228505793918377193791998583 342758690877565790687997875)
              ·
                refine ⟨514138036316348686031996813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342758690877565790687997875 514138036316348686031996813)
                ·
                  refine ⟨192801763618630757261998805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514138036316348686031996813 192801763618630757261998805)
                  ·
                    refine ⟨4518791334811658373328097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 192801763618630757261998805 4518791334811658373328097)
                    ·
                      refine ⟨3389093501108743779996073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518791334811658373328097 3389093501108743779996073)
                      ·
                        rfl

theorem cell23_6600236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_6600236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600236 prefixEnd_6600236 := by exact prefixLift 6600236
  have htrace : WordTrace (prefixWord ++ tailWord_6600236) baseStart_6600236 baseEnd_6600236 := by
    simpa [prefixWord, tailWord_6600236, baseEnd_6600236] using wordTrace_append hprefix tailTrace_6600236
  have hstable : (prefixWord ++ tailWord_6600236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600236).length < 2 ^ (prefixWord ++ tailWord_6600236).sum := by decide
  have hdescent : baseEnd_6600236 < baseStart_6600236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600266 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_6600266 : Nat := 118140960795 + 6600266 * 2 ^ 59
def prefixEnd_6600266 : Nat := 4983230072969 + 3 ^ 40 * 6600266 * 2
def baseEnd_6600266 : Nat := 3389108905528378662620935

theorem tailTrace_6600266 : CollatzResearch.WordTrace tailWord_6600266 prefixEnd_6600266 3389108905528378662620935 := by
  unfold tailWord_6600266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60182869476592748133523163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160487651937580661689395101 60182869476592748133523163)
  ·
    refine ⟨90274304214889122200284745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60182869476592748133523163 90274304214889122200284745)
    ·
      refine ⟨67705728161166841650213559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90274304214889122200284745 67705728161166841650213559)
      ·
        refine ⟨101558592241750262475320339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67705728161166841650213559 101558592241750262475320339)
        ·
          refine ⟨152337888362625393712980509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101558592241750262475320339 152337888362625393712980509)
          ·
            refine ⟨57126708135984522642367691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152337888362625393712980509 57126708135984522642367691)
            ·
              refine ⟨85690062203976783963551537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57126708135984522642367691 85690062203976783963551537)
              ·
                refine ⟨64267546652982587972663653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85690062203976783963551537 64267546652982587972663653)
                ·
                  refine ⟨12050164997434235244874435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64267546652982587972663653 12050164997434235244874435)
                  ·
                    refine ⟨18075247496151352867311653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12050164997434235244874435 18075247496151352867311653)
                    ·
                      refine ⟨3389108905528378662620935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18075247496151352867311653 3389108905528378662620935)
                      ·
                        rfl

theorem cell23_6600266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_6600266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600266 prefixEnd_6600266 := by exact prefixLift 6600266
  have htrace : WordTrace (prefixWord ++ tailWord_6600266) baseStart_6600266 baseEnd_6600266 := by
    simpa [prefixWord, tailWord_6600266, baseEnd_6600266] using wordTrace_append hprefix tailTrace_6600266
  have hstable : (prefixWord ++ tailWord_6600266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600266).length < 2 ^ (prefixWord ++ tailWord_6600266).sum := by decide
  have hdescent : baseEnd_6600266 < baseStart_6600266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600316 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_6600316 : Nat := 118140960795 + 6600316 * 2 ^ 59
def prefixEnd_6600316 : Nat := 4983230072969 + 3 ^ 40 * 6600316 * 2
def baseEnd_6600316 : Nat := 3389134579561103466995705

theorem tailTrace_6600316 : CollatzResearch.WordTrace tailWord_6600316 prefixEnd_6600316 3389134579561103466995705 := by
  unfold tailWord_6600316
  simp only [CollatzResearch.WordTrace]
  refine ⟨120366650778094925536706401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160488867704126567382275201 120366650778094925536706401)
  ·
    refine ⟨90274988083571194152529801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120366650778094925536706401 90274988083571194152529801)
    ·
      refine ⟨67706241062678395614397351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90274988083571194152529801 67706241062678395614397351)
      ·
        refine ⟨101559361594017593421596027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67706241062678395614397351 101559361594017593421596027)
        ·
          refine ⟨152339042391026390132394041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101559361594017593421596027 152339042391026390132394041)
          ·
            refine ⟨114254281793269792599295531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152339042391026390132394041 114254281793269792599295531)
            ·
              refine ⟨171381422689904688898943297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114254281793269792599295531 171381422689904688898943297)
              ·
                refine ⟨128536067017428516674207473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171381422689904688898943297 128536067017428516674207473)
                ·
                  refine ⟨96402050263071387505655605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128536067017428516674207473 96402050263071387505655605)
                  ·
                    refine ⟨9037692212162942578655213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96402050263071387505655605 9037692212162942578655213)
                    ·
                      refine ⟨3389134579561103466995705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037692212162942578655213 3389134579561103466995705)
                      ·
                        rfl

theorem cell23_6600316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_6600316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600316 prefixEnd_6600316 := by exact prefixLift 6600316
  have htrace : WordTrace (prefixWord ++ tailWord_6600316) baseStart_6600316 baseEnd_6600316 := by
    simpa [prefixWord, tailWord_6600316, baseEnd_6600316] using wordTrace_append hprefix tailTrace_6600316
  have hstable : (prefixWord ++ tailWord_6600316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600316).length < 2 ^ (prefixWord ++ tailWord_6600316).sum := by decide
  have hdescent : baseEnd_6600316 < baseStart_6600316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600410 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_6600410 : Nat := 118140960795 + 6600410 * 2 ^ 59
def prefixEnd_6600410 : Nat := 4983230072969 + 3 ^ 40 * 6600410 * 2
def baseEnd_6600410 : Nat := 3389182846742626099220273

theorem tailTrace_6600410 : CollatzResearch.WordTrace tailWord_6600410 prefixEnd_6600410 3389182846742626099220273 := by
  unfold tailWord_6600410
  simp only [CollatzResearch.WordTrace]
  refine ⟨60184182504462326281833671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160491153345232870084889789 60184182504462326281833671)
  ·
    refine ⟨90276273756693489422750507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60184182504462326281833671 90276273756693489422750507)
    ·
      refine ⟨135414410635040234134125761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90276273756693489422750507 135414410635040234134125761)
      ·
        refine ⟨101560807976280175600594321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135414410635040234134125761 101560807976280175600594321)
        ·
          refine ⟨76170605982210131700445741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101560807976280175600594321 76170605982210131700445741)
          ·
            refine ⟨28563977243328799387667153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76170605982210131700445741 28563977243328799387667153)
            ·
              refine ⟨21422982932496599540750365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28563977243328799387667153 21422982932496599540750365)
              ·
                refine ⟨8033618599686224827781387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21422982932496599540750365 8033618599686224827781387)
                ·
                  refine ⟨12050427899529337241672081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8033618599686224827781387 12050427899529337241672081)
                  ·
                    refine ⟨9037820924647002931254061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12050427899529337241672081 9037820924647002931254061)
                    ·
                      refine ⟨3389182846742626099220273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037820924647002931254061 3389182846742626099220273)
                      ·
                        rfl

theorem cell23_6600410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_6600410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600410 prefixEnd_6600410 := by exact prefixLift 6600410
  have htrace : WordTrace (prefixWord ++ tailWord_6600410) baseStart_6600410 baseEnd_6600410 := by
    simpa [prefixWord, tailWord_6600410, baseEnd_6600410] using wordTrace_append hprefix tailTrace_6600410
  have hstable : (prefixWord ++ tailWord_6600410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600410).length < 2 ^ (prefixWord ++ tailWord_6600410).sum := by decide
  have hdescent : baseEnd_6600410 < baseStart_6600410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600424 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6600424 : Nat := 118140960795 + 6600424 * 2 ^ 59
def prefixEnd_6600424 : Nat := 4983230072969 + 3 ^ 40 * 6600424 * 2
def baseEnd_6600424 : Nat := 3389190035471789044445209

theorem tailTrace_6600424 : CollatzResearch.WordTrace tailWord_6600424 prefixEnd_6600424 3389190035471789044445209 := by
  unfold tailWord_6600424
  simp only [CollatzResearch.WordTrace]
  refine ⟨120368620319899292759172163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160491493759865723678896217 120368620319899292759172163)
  ·
    refine ⟨180552930479848939138758245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120368620319899292759172163 180552930479848939138758245)
    ·
      refine ⟨33853674464971676088517171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180552930479848939138758245 33853674464971676088517171)
      ·
        refine ⟨50780511697457514132775757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33853674464971676088517171 50780511697457514132775757)
        ·
          refine ⟨19042691886546567799790909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50780511697457514132775757 19042691886546567799790909)
          ·
            refine ⟨7141009457454962924921591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19042691886546567799790909 7141009457454962924921591)
            ·
              refine ⟨10711514186182444387382387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7141009457454962924921591 10711514186182444387382387)
              ·
                refine ⟨16067271279273666581073581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10711514186182444387382387 16067271279273666581073581)
                ·
                  refine ⟨6025226729727624967902593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16067271279273666581073581 6025226729727624967902593)
                  ·
                    refine ⟨4518920047295718725926945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025226729727624967902593 4518920047295718725926945)
                    ·
                      refine ⟨3389190035471789044445209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518920047295718725926945 3389190035471789044445209)
                      ·
                        rfl

theorem cell23_6600424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6600424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600424 prefixEnd_6600424 := by exact prefixLift 6600424
  have htrace : WordTrace (prefixWord ++ tailWord_6600424) baseStart_6600424 baseEnd_6600424 := by
    simpa [prefixWord, tailWord_6600424, baseEnd_6600424] using wordTrace_append hprefix tailTrace_6600424
  have hstable : (prefixWord ++ tailWord_6600424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600424).length < 2 ^ (prefixWord ++ tailWord_6600424).sum := by decide
  have hdescent : baseEnd_6600424 < baseStart_6600424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600480 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6600480 : Nat := 118140960795 + 6600480 * 2 ^ 59
def prefixEnd_6600480 : Nat := 4983230072969 + 3 ^ 40 * 6600480 * 2
def baseEnd_6600480 : Nat := 3389218790388440825344951

theorem tailTrace_6600480 : CollatzResearch.WordTrace tailWord_6600480 prefixEnd_6600480 3389218790388440825344951 := by
  unfold tailWord_6600480
  simp only [CollatzResearch.WordTrace]
  refine ⟨120369641563797853541191447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160492855418397138054921929 120369641563797853541191447)
  ·
    refine ⟨180554462345696780311787171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120369641563797853541191447 180554462345696780311787171)
    ·
      refine ⟨270831693518545170467680757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180554462345696780311787171 270831693518545170467680757)
      ·
        refine ⟨25390471267363609731345071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270831693518545170467680757 25390471267363609731345071)
        ·
          refine ⟨38085706901045414597017607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25390471267363609731345071 38085706901045414597017607)
          ·
            refine ⟨57128560351568121895526411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38085706901045414597017607 57128560351568121895526411)
            ·
              refine ⟨85692840527352182843289617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57128560351568121895526411 85692840527352182843289617)
              ·
                refine ⟨64269630395514137132467213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85692840527352182843289617 64269630395514137132467213)
                ·
                  refine ⟨24101111398317801424675205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64269630395514137132467213 24101111398317801424675205)
                  ·
                    refine ⟨4518958387184587767126601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24101111398317801424675205 4518958387184587767126601)
                    ·
                      refine ⟨3389218790388440825344951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518958387184587767126601 3389218790388440825344951)
                      ·
                        rfl

theorem cell23_6600480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6600480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600480 prefixEnd_6600480 := by exact prefixLift 6600480
  have htrace : WordTrace (prefixWord ++ tailWord_6600480) baseStart_6600480 baseEnd_6600480 := by
    simpa [prefixWord, tailWord_6600480, baseEnd_6600480] using wordTrace_append hprefix tailTrace_6600480
  have hstable : (prefixWord ++ tailWord_6600480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600480).length < 2 ^ (prefixWord ++ tailWord_6600480).sum := by decide
  have hdescent : baseEnd_6600480 < baseStart_6600480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600483 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3]
def baseStart_6600483 : Nat := 118140960795 + 6600483 * 2 ^ 59
def prefixEnd_6600483 : Nat := 4983230072969 + 3 ^ 40 * 6600483 * 2
def baseEnd_6600483 : Nat := 3389220330830404313607437

theorem tailTrace_6600483 : CollatzResearch.WordTrace tailWord_6600483 prefixEnd_6600483 3389220330830404313607437 := by
  unfold tailWord_6600483
  simp only [CollatzResearch.WordTrace]
  refine ⟨240739392546584838594742103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160492928364389892396494735 240739392546584838594742103)
  ·
    refine ⟨361109088819877257892113155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240739392546584838594742103 361109088819877257892113155)
    ·
      refine ⟨541663633229815886838169733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361109088819877257892113155 541663633229815886838169733)
      ·
        refine ⟨101561931230590478782156825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541663633229815886838169733 101561931230590478782156825)
        ·
          refine ⟨76171448422942859086617619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101561931230590478782156825 76171448422942859086617619)
          ·
            refine ⟨114257172634414288629926429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76171448422942859086617619 114257172634414288629926429)
            ·
              refine ⟨42846439737905358236222411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114257172634414288629926429 42846439737905358236222411)
              ·
                refine ⟨64269659606858037354333617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42846439737905358236222411 64269659606858037354333617)
                ·
                  refine ⟨48202244705143528015750213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64269659606858037354333617 48202244705143528015750213)
                  ·
                    refine ⟨9037920882214411502953165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48202244705143528015750213 9037920882214411502953165)
                    ·
                      refine ⟨3389220330830404313607437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037920882214411502953165 3389220330830404313607437)
                      ·
                        rfl

theorem cell23_6600483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_6600483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600483 prefixEnd_6600483 := by exact prefixLift 6600483
  have htrace : WordTrace (prefixWord ++ tailWord_6600483) baseStart_6600483 baseEnd_6600483 := by
    simpa [prefixWord, tailWord_6600483, baseEnd_6600483] using wordTrace_append hprefix tailTrace_6600483
  have hstable : (prefixWord ++ tailWord_6600483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600483).length < 2 ^ (prefixWord ++ tailWord_6600483).sum := by decide
  have hdescent : baseEnd_6600483 < baseStart_6600483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600497 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_6600497 : Nat := 118140960795 + 6600497 * 2 ^ 59
def prefixEnd_6600497 : Nat := 4983230072969 + 3 ^ 40 * 6600497 * 2
def baseEnd_6600497 : Nat := 3389227519559567258832373

theorem tailTrace_6600497 : CollatzResearch.WordTrace tailWord_6600497 prefixEnd_6600497 3389227519559567258832373 := by
  unfold tailWord_6600497
  simp only [CollatzResearch.WordTrace]
  refine ⟨240739903168534118985751745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160493268779022745990501163 240739903168534118985751745)
  ·
    refine ⟨180554927376400589239313809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240739903168534118985751745 180554927376400589239313809)
    ·
      refine ⟨135416195532300441929485357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180554927376400589239313809 135416195532300441929485357)
      ·
        refine ⟨50781073324612665723557009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135416195532300441929485357 50781073324612665723557009)
        ·
          refine ⟨38085804993459499292667757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50781073324612665723557009 38085804993459499292667757)
          ·
            refine ⟨14282176872547312234750409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38085804993459499292667757 14282176872547312234750409)
            ·
              refine ⟨10711632654410484176062807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14282176872547312234750409 10711632654410484176062807)
              ·
                refine ⟨16067448981615726264094211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10711632654410484176062807 16067448981615726264094211)
                ·
                  refine ⟨24101173472423589396141317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16067448981615726264094211 24101173472423589396141317)
                  ·
                    refine ⟨4518970026079423011776497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24101173472423589396141317 4518970026079423011776497)
                    ·
                      refine ⟨3389227519559567258832373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518970026079423011776497 3389227519559567258832373)
                      ·
                        rfl

theorem cell23_6600497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_6600497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600497 prefixEnd_6600497 := by exact prefixLift 6600497
  have htrace : WordTrace (prefixWord ++ tailWord_6600497) baseStart_6600497 baseEnd_6600497 := by
    simpa [prefixWord, tailWord_6600497, baseEnd_6600497] using wordTrace_append hprefix tailTrace_6600497
  have hstable : (prefixWord ++ tailWord_6600497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600497).length < 2 ^ (prefixWord ++ tailWord_6600497).sum := by decide
  have hdescent : baseEnd_6600497 < baseStart_6600497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600518 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6600518 : Nat := 118140960795 + 6600518 * 2 ^ 59
def prefixEnd_6600518 : Nat := 4983230072969 + 3 ^ 40 * 6600518 * 2
def baseEnd_6600518 : Nat := 3389238302653311676669777

theorem tailTrace_6600518 : CollatzResearch.WordTrace tailWord_6600518 prefixEnd_6600518 3389238302653311676669777 := by
  unfold tailWord_6600518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523145909420563736633319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160493779400972026381510805 7523145909420563736633319)
  ·
    refine ⟨11284718864130845604949979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7523145909420563736633319 11284718864130845604949979)
    ·
      refine ⟨16927078296196268407424969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11284718864130845604949979 16927078296196268407424969)
      ·
        refine ⟨12695308722147201305568727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16927078296196268407424969 12695308722147201305568727)
        ·
          refine ⟨19042963083220801958353091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12695308722147201305568727 19042963083220801958353091)
          ·
            refine ⟨28564444624831202937529637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19042963083220801958353091 28564444624831202937529637)
            ·
              refine ⟨5355833367155850550786807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28564444624831202937529637 5355833367155850550786807)
              ·
                refine ⟨8033750050733775826180211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355833367155850550786807 8033750050733775826180211)
                ·
                  refine ⟨12050625076100663739270317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8033750050733775826180211 12050625076100663739270317)
                  ·
                    refine ⟨4518984403537748902226369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12050625076100663739270317 4518984403537748902226369)
                    ·
                      refine ⟨3389238302653311676669777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4518984403537748902226369 3389238302653311676669777)
                      ·
                        rfl

theorem cell23_6600518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6600518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600518 prefixEnd_6600518 := by exact prefixLift 6600518
  have htrace : WordTrace (prefixWord ++ tailWord_6600518) baseStart_6600518 baseEnd_6600518 := by
    simpa [prefixWord, tailWord_6600518, baseEnd_6600518] using wordTrace_append hprefix tailTrace_6600518
  have hstable : (prefixWord ++ tailWord_6600518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600518).length < 2 ^ (prefixWord ++ tailWord_6600518).sum := by decide
  have hdescent : baseEnd_6600518 < baseStart_6600518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600520 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 5]
def baseStart_6600520 : Nat := 118140960795 + 6600520 * 2 ^ 59
def prefixEnd_6600520 : Nat := 4983230072969 + 3 ^ 40 * 6600520 * 2
def baseEnd_6600520 : Nat := 376582147734957852093863

theorem tailTrace_6600520 : CollatzResearch.WordTrace tailWord_6600520 prefixEnd_6600520 376582147734957852093863 := by
  unfold tailWord_6600520
  simp only [CollatzResearch.WordTrace]
  refine ⟨120370371023725396956919507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160493828031633862609226009 120370371023725396956919507)
  ·
    refine ⟨180555556535588095435379261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120370371023725396956919507 180555556535588095435379261)
    ·
      refine ⟨67708333700845535788267223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180555556535588095435379261 67708333700845535788267223)
      ·
        refine ⟨101562500551268303682400835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67708333700845535788267223 101562500551268303682400835)
        ·
          refine ⟨152343750826902455523601253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101562500551268303682400835 152343750826902455523601253)
          ·
            refine ⟨28564453280044210410675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152343750826902455523601253 28564453280044210410675235)
            ·
              refine ⟨42846679920066315616012853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28564453280044210410675235 42846679920066315616012853)
              ·
                refine ⟨4016876242506217089001205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42846679920066315616012853 4016876242506217089001205)
                ·
                  refine ⟨376582147734957852093863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016876242506217089001205 376582147734957852093863)
                  ·
                    rfl

theorem cell23_6600520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 5].length) (baseStart_6600520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600520 prefixEnd_6600520 := by exact prefixLift 6600520
  have htrace : WordTrace (prefixWord ++ tailWord_6600520) baseStart_6600520 baseEnd_6600520 := by
    simpa [prefixWord, tailWord_6600520, baseEnd_6600520] using wordTrace_append hprefix tailTrace_6600520
  have hstable : (prefixWord ++ tailWord_6600520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600520).length < 2 ^ (prefixWord ++ tailWord_6600520).sum := by decide
  have hdescent : baseEnd_6600520 < baseStart_6600520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600530 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_6600530 : Nat := 118140960795 + 6600530 * 2 ^ 59
def prefixEnd_6600530 : Nat := 4983230072969 + 3 ^ 40 * 6600530 * 2
def baseEnd_6600530 : Nat := 3389244464421165629719721

theorem tailTrace_6600530 : CollatzResearch.WordTrace tailWord_6600530 prefixEnd_6600530 3389244464421165629719721 := by
  unfold tailWord_6600530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185276694353641405425761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160494071184943043747802029 60185276694353641405425761)
  ·
    refine ⟨45138957520765231054069321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60185276694353641405425761 45138957520765231054069321)
    ·
      refine ⟨33854218140573923290551991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45138957520765231054069321 33854218140573923290551991)
      ·
        refine ⟨50781327210860884935827987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33854218140573923290551991 50781327210860884935827987)
        ·
          refine ⟨76171990816291327403741981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50781327210860884935827987 76171990816291327403741981)
          ·
            refine ⟨28564496556109247776403243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76171990816291327403741981 28564496556109247776403243)
            ·
              refine ⟨42846744834163871664604865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28564496556109247776403243 42846744834163871664604865)
              ·
                refine ⟨32135058625622903748453649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42846744834163871664604865 32135058625622903748453649)
                ·
                  refine ⟨24101293969217177811340237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32135058625622903748453649 24101293969217177811340237)
                  ·
                    refine ⟨9037985238456441679252589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24101293969217177811340237 9037985238456441679252589)
                    ·
                      refine ⟨3389244464421165629719721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9037985238456441679252589 3389244464421165629719721)
                      ·
                        rfl

theorem cell23_6600530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_6600530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600530 prefixEnd_6600530 := by exact prefixLift 6600530
  have htrace : WordTrace (prefixWord ++ tailWord_6600530) baseStart_6600530 baseEnd_6600530 := by
    simpa [prefixWord, tailWord_6600530, baseEnd_6600530] using wordTrace_append hprefix tailTrace_6600530
  have hstable : (prefixWord ++ tailWord_6600530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600530).length < 2 ^ (prefixWord ++ tailWord_6600530).sum := by decide
  have hdescent : baseEnd_6600530 < baseStart_6600530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600570 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_6600570 : Nat := 118140960795 + 6600570 * 2 ^ 59
def prefixEnd_6600570 : Nat := 4983230072969 + 3 ^ 40 * 6600570 * 2
def baseEnd_6600570 : Nat := 3389265003647345473219537

theorem tailTrace_6600570 : CollatzResearch.WordTrace tailWord_6600570 prefixEnd_6600570 3389265003647345473219537 := by
  unfold tailWord_6600570
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185641424317413113289791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160495043798179768302106109 60185641424317413113289791)
  ·
    refine ⟨90278462136476119669934687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60185641424317413113289791 90278462136476119669934687)
    ·
      refine ⟨135417693204714179504902031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90278462136476119669934687 135417693204714179504902031)
      ·
        refine ⟨203126539807071269257353047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135417693204714179504902031 203126539807071269257353047)
        ·
          refine ⟨304689809710606903886029571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203126539807071269257353047 304689809710606903886029571)
          ·
            refine ⟨457034714565910355829044357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304689809710606903886029571 457034714565910355829044357)
            ·
              refine ⟨85694008981108191717945817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 457034714565910355829044357 85694008981108191717945817)
              ·
                refine ⟨64270506735831143788459363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85694008981108191717945817 64270506735831143788459363)
                ·
                  refine ⟨96405760103746715682689045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64270506735831143788459363 96405760103746715682689045)
                  ·
                    refine ⟨4519020004863127297626049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96405760103746715682689045 4519020004863127297626049)
                    ·
                      refine ⟨3389265003647345473219537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519020004863127297626049 3389265003647345473219537)
                      ·
                        rfl

theorem cell23_6600570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_6600570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600570 prefixEnd_6600570 := by exact prefixLift 6600570
  have htrace : WordTrace (prefixWord ++ tailWord_6600570) baseStart_6600570 baseEnd_6600570 := by
    simpa [prefixWord, tailWord_6600570, baseEnd_6600570] using wordTrace_append hprefix tailTrace_6600570
  have hstable : (prefixWord ++ tailWord_6600570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600570).length < 2 ^ (prefixWord ++ tailWord_6600570).sum := by decide
  have hdescent : baseEnd_6600570 < baseStart_6600570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600573 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6600573 : Nat := 118140960795 + 6600573 * 2 ^ 59
def prefixEnd_6600573 : Nat := 4983230072969 + 3 ^ 40 * 6600573 * 2
def baseEnd_6600573 : Nat := 3389266544089308961482023

theorem tailTrace_6600573 : CollatzResearch.WordTrace tailWord_6600573 prefixEnd_6600573 3389266544089308961482023 := by
  unfold tailWord_6600573
  simp only [CollatzResearch.WordTrace]
  refine ⟨240742675116258783965518373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160495116744172522643678915 240742675116258783965518373)
  ·
    refine ⟨45139251584298521993534695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240742675116258783965518373 45139251584298521993534695)
    ·
      refine ⟨67708877376447782990302043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45139251584298521993534695 67708877376447782990302043)
      ·
        refine ⟨101563316064671674485453065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67708877376447782990302043 101563316064671674485453065)
        ·
          refine ⟨76172487048503755864089799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101563316064671674485453065 76172487048503755864089799)
          ·
            refine ⟨114258730572755633796134699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76172487048503755864089799 114258730572755633796134699)
            ·
              refine ⟨171388095859133450694202049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114258730572755633796134699 171388095859133450694202049)
              ·
                refine ⟨128541071894350088020651537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171388095859133450694202049 128541071894350088020651537)
                ·
                  refine ⟨96405803920762566015488653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128541071894350088020651537 96405803920762566015488653)
                  ·
                    refine ⟨36152176470285962255808245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96405803920762566015488653 36152176470285962255808245)
                    ·
                      refine ⟨3389266544089308961482023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36152176470285962255808245 3389266544089308961482023)
                      ·
                        rfl

theorem cell23_6600573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6600573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600573 prefixEnd_6600573 := by exact prefixLift 6600573
  have htrace : WordTrace (prefixWord ++ tailWord_6600573) baseStart_6600573 baseEnd_6600573 := by
    simpa [prefixWord, tailWord_6600573, baseEnd_6600573] using wordTrace_append hprefix tailTrace_6600573
  have hstable : (prefixWord ++ tailWord_6600573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600573).length < 2 ^ (prefixWord ++ tailWord_6600573).sum := by decide
  have hdescent : baseEnd_6600573 < baseStart_6600573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600580 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_6600580 : Nat := 118140960795 + 6600580 * 2 ^ 59
def prefixEnd_6600580 : Nat := 4983230072969 + 3 ^ 40 * 6600580 * 2
def baseEnd_6600580 : Nat := 1129756712817963478031497

theorem tailTrace_6600580 : CollatzResearch.WordTrace tailWord_6600580 prefixEnd_6600580 1129756712817963478031497 := by
  unfold tailWord_6600580
  simp only [CollatzResearch.WordTrace]
  refine ⟨120371465213616712080511597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160495286951488949440682129 120371465213616712080511597)
  ·
    refine ⟨45139299455106267030191849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120371465213616712080511597 45139299455106267030191849)
    ·
      refine ⟨33854474591329700272643887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45139299455106267030191849 33854474591329700272643887)
      ·
        refine ⟨50781711886994550408965831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33854474591329700272643887 50781711886994550408965831)
        ·
          refine ⟨76172567830491825613448747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50781711886994550408965831 76172567830491825613448747)
          ·
            refine ⟨114258851745737738420173121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76172567830491825613448747 114258851745737738420173121)
            ·
              refine ⟨85694138809303303815129841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114258851745737738420173121 85694138809303303815129841)
              ·
                refine ⟨64270604106977477861347381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85694138809303303815129841 64270604106977477861347381)
                ·
                  refine ⟨6025369135029138549501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64270604106977477861347381 6025369135029138549501317)
                  ·
                    refine ⟨1129756712817963478031497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025369135029138549501317 1129756712817963478031497)
                    ·
                      rfl

theorem cell23_6600580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_6600580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600580 prefixEnd_6600580 := by exact prefixLift 6600580
  have htrace : WordTrace (prefixWord ++ tailWord_6600580) baseStart_6600580 baseEnd_6600580 := by
    simpa [prefixWord, tailWord_6600580, baseEnd_6600580] using wordTrace_append hprefix tailTrace_6600580
  have hstable : (prefixWord ++ tailWord_6600580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600580).length < 2 ^ (prefixWord ++ tailWord_6600580).sum := by decide
  have hdescent : baseEnd_6600580 < baseStart_6600580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600593 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 8]
def baseStart_6600593 : Nat := 118140960795 + 6600593 * 2 ^ 59
def prefixEnd_6600593 : Nat := 4983230072969 + 3 ^ 40 * 6600593 * 2
def baseEnd_6600593 : Nat := 376586312633599875914659

theorem tailTrace_6600593 : CollatzResearch.WordTrace tailWord_6600593 prefixEnd_6600593 376586312633599875914659 := by
  unfold tailWord_6600593
  simp only [CollatzResearch.WordTrace]
  refine ⟨240743404576186327381246433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160495603050790884920830955 240743404576186327381246433)
  ·
    refine ⟨180557553432139745535934825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240743404576186327381246433 180557553432139745535934825)
    ·
      refine ⟨135418165074104809151951119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180557553432139745535934825 135418165074104809151951119)
      ·
        refine ⟨203127247611157213727926679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135418165074104809151951119 203127247611157213727926679)
        ·
          refine ⟨304690871416735820591890019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203127247611157213727926679 304690871416735820591890019)
          ·
            refine ⟨457036307125103730887835029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304690871416735820591890019 457036307125103730887835029)
            ·
              refine ⟨21423576896489237385367267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 457036307125103730887835029 21423576896489237385367267)
              ·
                refine ⟨32135365344733856078050901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21423576896489237385367267 32135365344733856078050901)
                ·
                  refine ⟨376586312633599875914659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32135365344733856078050901 376586312633599875914659)
                  ·
                    rfl

theorem cell23_6600593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_6600593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600593 prefixEnd_6600593 := by exact prefixLift 6600593
  have htrace : WordTrace (prefixWord ++ tailWord_6600593) baseStart_6600593 baseEnd_6600593 := by
    simpa [prefixWord, tailWord_6600593, baseEnd_6600593] using wordTrace_append hprefix tailTrace_6600593
  have hstable : (prefixWord ++ tailWord_6600593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600593).length < 2 ^ (prefixWord ++ tailWord_6600593).sum := by decide
  have hdescent : baseEnd_6600593 < baseStart_6600593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600613 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6600613 : Nat := 118140960795 + 6600613 * 2 ^ 59
def prefixEnd_6600613 : Nat := 4983230072969 + 3 ^ 40 * 6600613 * 2
def baseEnd_6600613 : Nat := 3389287083315488804981839

theorem tailTrace_6600613 : CollatzResearch.WordTrace tailWord_6600613 prefixEnd_6600613 3389287083315488804981839 := by
  unfold tailWord_6600613
  simp only [CollatzResearch.WordTrace]
  refine ⟨240744134036113870796974493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160496089357409247197982995 240744134036113870796974493)
  ·
    refine ⟨90279050263542701548865435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240744134036113870796974493 90279050263542701548865435)
    ·
      refine ⟨135418575395314052323298153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90279050263542701548865435 135418575395314052323298153)
      ·
        refine ⟨101563931546485539242473615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135418575395314052323298153 101563931546485539242473615)
        ·
          refine ⟨152345897319728308863710423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101563931546485539242473615 152345897319728308863710423)
          ·
            refine ⟨228518845979592463295565635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152345897319728308863710423 228518845979592463295565635)
            ·
              refine ⟨342778268969388694943348453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228518845979592463295565635 342778268969388694943348453)
              ·
                refine ⟨64270925431760380301877835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342778268969388694943348453 64270925431760380301877835)
                ·
                  refine ⟨96406388147640570452816753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64270925431760380301877835 96406388147640570452816753)
                  ·
                    refine ⟨72304791110730427839612565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96406388147640570452816753 72304791110730427839612565)
                    ·
                      refine ⟨3389287083315488804981839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72304791110730427839612565 3389287083315488804981839)
                      ·
                        rfl

theorem cell23_6600613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6600613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600613 prefixEnd_6600613 := by exact prefixLift 6600613
  have htrace : WordTrace (prefixWord ++ tailWord_6600613) baseStart_6600613 baseEnd_6600613 := by
    simpa [prefixWord, tailWord_6600613, baseEnd_6600613] using wordTrace_append hprefix tailTrace_6600613
  have hstable : (prefixWord ++ tailWord_6600613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600613).length < 2 ^ (prefixWord ++ tailWord_6600613).sum := by decide
  have hdescent : baseEnd_6600613 < baseStart_6600613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600683 : List Nat := [1, 1, 1, 1, 2, 3, 1, 13]
def baseStart_6600683 : Nat := 118140960795 + 6600683 * 2 ^ 59
def prefixEnd_6600683 : Nat := 4983230072969 + 3 ^ 40 * 6600683 * 2
def baseEnd_6600683 : Nat := 125530482480048278929871

theorem tailTrace_6600683 : CollatzResearch.WordTrace tailWord_6600683 prefixEnd_6600683 125530482480048278929871 := by
  unfold tailWord_6600683
  simp only [CollatzResearch.WordTrace]
  refine ⟨240746687145860272752022703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160497791430573515168015135 240746687145860272752022703)
  ·
    refine ⟨361120030718790409128034055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240746687145860272752022703 361120030718790409128034055)
    ·
      refine ⟨541680046078185613692051083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361120030718790409128034055 541680046078185613692051083)
      ·
        refine ⟨812520069117278420538076625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541680046078185613692051083 812520069117278420538076625)
        ·
          refine ⟨609390051837958815403557469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812520069117278420538076625 609390051837958815403557469)
          ·
            refine ⟨228521269439234555776334051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609390051837958815403557469 228521269439234555776334051)
            ·
              refine ⟨342781904158851833664501077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228521269439234555776334051 342781904158851833664501077)
              ·
                refine ⟨125530482480048278929871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 342781904158851833664501077 125530482480048278929871)
                ·
                  rfl

theorem cell23_6600683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 13].length) (baseStart_6600683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600683 prefixEnd_6600683 := by exact prefixLift 6600683
  have htrace : WordTrace (prefixWord ++ tailWord_6600683) baseStart_6600683 baseEnd_6600683 := by
    simpa [prefixWord, tailWord_6600683, baseEnd_6600683] using wordTrace_append hprefix tailTrace_6600683
  have hstable : (prefixWord ++ tailWord_6600683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600683).length < 2 ^ (prefixWord ++ tailWord_6600683).sum := by decide
  have hdescent : baseEnd_6600683 < baseStart_6600683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600711 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6600711 : Nat := 118140960795 + 6600711 * 2 ^ 59
def prefixEnd_6600711 : Nat := 4983230072969 + 3 ^ 40 * 6600711 * 2
def baseEnd_6600711 : Nat := 3389337404419629421556389

theorem tailTrace_6600711 : CollatzResearch.WordTrace tailWord_6600711 prefixEnd_6600711 3389337404419629421556389 := by
  unfold tailWord_6600711
  simp only [CollatzResearch.WordTrace]
  refine ⟨240747708389758833534041987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160498472259839222356027991 240747708389758833534041987)
  ·
    refine ⟨361121562584638250301062981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240747708389758833534041987 361121562584638250301062981)
    ·
      refine ⟨67710292984619671931449309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361121562584638250301062981 67710292984619671931449309)
      ·
        refine ⟨25391359869232376974293491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67710292984619671931449309 25391359869232376974293491)
        ·
          refine ⟨38087039803848565461440237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25391359869232376974293491 38087039803848565461440237)
          ·
            refine ⟨14282639926443212048040089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38087039803848565461440237 14282639926443212048040089)
            ·
              refine ⟨10711979944832409036030067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14282639926443212048040089 10711979944832409036030067)
              ·
                refine ⟨16067969917248613554045101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10711979944832409036030067 16067969917248613554045101)
                ·
                  refine ⟨6025488718968230082766913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16067969917248613554045101 6025488718968230082766913)
                  ·
                    refine ⟨4519116539226172562075185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025488718968230082766913 4519116539226172562075185)
                    ·
                      refine ⟨3389337404419629421556389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519116539226172562075185 3389337404419629421556389)
                      ·
                        rfl

theorem cell23_6600711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6600711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600711 prefixEnd_6600711 := by exact prefixLift 6600711
  have htrace : WordTrace (prefixWord ++ tailWord_6600711) baseStart_6600711 baseEnd_6600711 := by
    simpa [prefixWord, tailWord_6600711, baseEnd_6600711] using wordTrace_append hprefix tailTrace_6600711
  have hstable : (prefixWord ++ tailWord_6600711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600711).length < 2 ^ (prefixWord ++ tailWord_6600711).sum := by decide
  have hdescent : baseEnd_6600711 < baseStart_6600711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600817 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_6600817 : Nat := 118140960795 + 6600817 * 2 ^ 59
def prefixEnd_6600817 : Nat := 4983230072969 + 3 ^ 40 * 6600817 * 2
def baseEnd_6600817 : Nat := 3389391833369006006830901

theorem tailTrace_6600817 : CollatzResearch.WordTrace tailWord_6600817 prefixEnd_6600817 3389391833369006006830901 := by
  unfold tailWord_6600817
  simp only [CollatzResearch.WordTrace]
  refine ⟨240751574527374813637400705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160501049684916542424933803 240751574527374813637400705)
  ·
    refine ⟨180563680895531110228050529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240751574527374813637400705 180563680895531110228050529)
    ·
      refine ⟨135422760671648332671037897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180563680895531110228050529 135422760671648332671037897)
      ·
        refine ⟨101567070503736249503278423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135422760671648332671037897 101567070503736249503278423)
        ·
          refine ⟨152350605755604374254917635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101567070503736249503278423 152350605755604374254917635)
          ·
            refine ⟨228525908633406561382376453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152350605755604374254917635 228525908633406561382376453)
            ·
              refine ⟨42848607868763730259195585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228525908633406561382376453 42848607868763730259195585)
              ·
                refine ⟨32136455901572797694396689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42848607868763730259195585 32136455901572797694396689)
                ·
                  refine ⟨24102341926179598270797517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32136455901572797694396689 24102341926179598270797517)
                  ·
                    refine ⟨9038378222317349351549069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24102341926179598270797517 9038378222317349351549069)
                    ·
                      refine ⟨3389391833369006006830901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038378222317349351549069 3389391833369006006830901)
                      ·
                        rfl

theorem cell23_6600817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_6600817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600817 prefixEnd_6600817 := by exact prefixLift 6600817
  have htrace : WordTrace (prefixWord ++ tailWord_6600817) baseStart_6600817 baseEnd_6600817 := by
    simpa [prefixWord, tailWord_6600817, baseEnd_6600817] using wordTrace_append hprefix tailTrace_6600817
  have hstable : (prefixWord ++ tailWord_6600817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600817).length < 2 ^ (prefixWord ++ tailWord_6600817).sum := by decide
  have hdescent : baseEnd_6600817 < baseStart_6600817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600818 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 2, 2, 2]
def baseStart_6600818 : Nat := 118140960795 + 6600818 * 2 ^ 59
def prefixEnd_6600818 : Nat := 4983230072969 + 3 ^ 40 * 6600818 * 2
def baseEnd_6600818 : Nat := 3389392346849660502918397

theorem tailTrace_6600818 : CollatzResearch.WordTrace tailWord_6600818 prefixEnd_6600818 3389392346849660502918397 := by
  unfold tailWord_6600818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60187902750092797702046777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160501074000247460538791405 60187902750092797702046777)
  ·
    refine ⟨45140927062569598276535083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60187902750092797702046777 45140927062569598276535083)
    ·
      refine ⟨67711390593854397414802625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45140927062569598276535083 67711390593854397414802625)
      ·
        refine ⟨50783542945390798061101969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67711390593854397414802625 50783542945390798061101969)
        ·
          refine ⟨38087657209043098545826477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50783542945390798061101969 38087657209043098545826477)
          ·
            refine ⟨14282871453391161954684929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38087657209043098545826477 14282871453391161954684929)
            ·
              refine ⟨10712153590043371466013697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14282871453391161954684929 10712153590043371466013697)
              ·
                refine ⟨8034115192532528599510273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10712153590043371466013697 8034115192532528599510273)
                ·
                  refine ⟨6025586394399396449632705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034115192532528599510273 6025586394399396449632705)
                  ·
                    refine ⟨4519189795799547337224529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6025586394399396449632705 4519189795799547337224529)
                    ·
                      refine ⟨3389392346849660502918397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519189795799547337224529 3389392346849660502918397)
                      ·
                        rfl

theorem cell23_6600818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_6600818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600818 prefixEnd_6600818 := by exact prefixLift 6600818
  have htrace : WordTrace (prefixWord ++ tailWord_6600818) baseStart_6600818 baseEnd_6600818 := by
    simpa [prefixWord, tailWord_6600818, baseEnd_6600818] using wordTrace_append hprefix tailTrace_6600818
  have hstable : (prefixWord ++ tailWord_6600818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600818).length < 2 ^ (prefixWord ++ tailWord_6600818).sum := by decide
  have hdescent : baseEnd_6600818 < baseStart_6600818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600907 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3]
def baseStart_6600907 : Nat := 118140960795 + 6600907 * 2 ^ 59
def prefixEnd_6600907 : Nat := 4983230072969 + 3 ^ 40 * 6600907 * 2
def baseEnd_6600907 : Nat := 3389438046627910654705487

theorem tailTrace_6600907 : CollatzResearch.WordTrace tailWord_6600907 prefixEnd_6600907 3389438046627910654705487 := by
  unfold tailWord_6600907
  simp only [CollatzResearch.WordTrace]
  refine ⟨240754857097048759008176975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160503238064699172672117983 240754857097048759008176975)
  ·
    refine ⟨361132285645573138512265463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240754857097048759008176975 361132285645573138512265463)
    ·
      refine ⟨541698428468359707768398195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361132285645573138512265463 541698428468359707768398195)
      ·
        refine ⟨812547642702539561652597293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541698428468359707768398195 812547642702539561652597293)
        ·
          refine ⟨304705366013452335619723985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812547642702539561652597293 304705366013452335619723985)
          ·
            refine ⟨228529024510089251714792989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304705366013452335619723985 228529024510089251714792989)
            ·
              refine ⟨85698384191283469393047371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228529024510089251714792989 85698384191283469393047371)
              ·
                refine ⟨128547576286925204089571057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85698384191283469393047371 128547576286925204089571057)
                ·
                  refine ⟨96410682215193903067178293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128547576286925204089571057 96410682215193903067178293)
                  ·
                    refine ⟨9038501457674428412547965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96410682215193903067178293 9038501457674428412547965)
                    ·
                      refine ⟨3389438046627910654705487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038501457674428412547965 3389438046627910654705487)
                      ·
                        rfl

theorem cell23_6600907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 3].length) (baseStart_6600907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600907 prefixEnd_6600907 := by exact prefixLift 6600907
  have htrace : WordTrace (prefixWord ++ tailWord_6600907) baseStart_6600907 baseEnd_6600907 := by
    simpa [prefixWord, tailWord_6600907, baseEnd_6600907] using wordTrace_append hprefix tailTrace_6600907
  have hstable : (prefixWord ++ tailWord_6600907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600907).length < 2 ^ (prefixWord ++ tailWord_6600907).sum := by decide
  have hdescent : baseEnd_6600907 < baseStart_6600907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600927 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 5, 5]
def baseStart_6600927 : Nat := 118140960795 + 6600927 * 2 ^ 59
def prefixEnd_6600927 : Nat := 4983230072969 + 3 ^ 40 * 6600927 * 2
def baseEnd_6600927 : Nat := 1129816105413666858818465

theorem tailTrace_6600927 : CollatzResearch.WordTrace tailWord_6600927 prefixEnd_6600927 1129816105413666858818465 := by
  unfold tailWord_6600927
  simp only [CollatzResearch.WordTrace]
  refine ⟨240755586556976302423905035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160503724371317534949270023 240755586556976302423905035)
  ·
    refine ⟨361133379835464453635857553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240755586556976302423905035 361133379835464453635857553)
    ·
      refine ⟨270850034876598340226893165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361133379835464453635857553 270850034876598340226893165)
      ·
        refine ⟨101568763078724377585084937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270850034876598340226893165 101568763078724377585084937)
        ·
          refine ⟨76176572309043283188813703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101568763078724377585084937 76176572309043283188813703)
          ·
            refine ⟨114264858463564924783220555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76176572309043283188813703 114264858463564924783220555)
            ·
              refine ⟨171397287695347387174830833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114264858463564924783220555 171397287695347387174830833)
              ·
                refine ⟨128547965771510540381123125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171397287695347387174830833 128547965771510540381123125)
                ·
                  refine ⟨12051371791079113160730293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128547965771510540381123125 12051371791079113160730293)
                  ·
                    refine ⟨1129816105413666858818465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12051371791079113160730293 1129816105413666858818465)
                    ·
                      rfl

theorem cell23_6600927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_6600927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600927 prefixEnd_6600927 := by exact prefixLift 6600927
  have htrace : WordTrace (prefixWord ++ tailWord_6600927) baseStart_6600927 baseEnd_6600927 := by
    simpa [prefixWord, tailWord_6600927, baseEnd_6600927] using wordTrace_append hprefix tailTrace_6600927
  have hstable : (prefixWord ++ tailWord_6600927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600927).length < 2 ^ (prefixWord ++ tailWord_6600927).sum := by decide
  have hdescent : baseEnd_6600927 < baseStart_6600927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600935 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 1, 4]
def baseStart_6600935 : Nat := 118140960795 + 6600935 * 2 ^ 59
def prefixEnd_6600935 : Nat := 4983230072969 + 3 ^ 40 * 6600935 * 2
def baseEnd_6600935 : Nat := 1129817474695412181718453

theorem tailTrace_6600935 : CollatzResearch.WordTrace tailWord_6600935 prefixEnd_6600935 1129817474695412181718453 := by
  unfold tailWord_6600935
  simp only [CollatzResearch.WordTrace]
  refine ⟨240755878340947319790196259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160503918893964879860130839 240755878340947319790196259)
  ·
    refine ⟨361133817511420979685294389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240755878340947319790196259 361133817511420979685294389)
    ·
      refine ⟨33856295391695716845496349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361133817511420979685294389 33856295391695716845496349)
      ·
        refine ⟨12696110771885893817061131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33856295391695716845496349 12696110771885893817061131)
        ·
          refine ⟨19044166157828840725591697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12696110771885893817061131 19044166157828840725591697)
          ·
            refine ⟨14283124618371630544193773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19044166157828840725591697 14283124618371630544193773)
            ·
              refine ⟨5356171731889361454072665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14283124618371630544193773 5356171731889361454072665)
              ·
                refine ⟨4017128798917021090554499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356171731889361454072665 4017128798917021090554499)
                ·
                  refine ⟨6025693198375531635831749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017128798917021090554499 6025693198375531635831749)
                  ·
                    refine ⟨1129817474695412181718453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025693198375531635831749 1129817474695412181718453)
                    ·
                      rfl

theorem cell23_6600935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_6600935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600935 prefixEnd_6600935 := by exact prefixLift 6600935
  have htrace : WordTrace (prefixWord ++ tailWord_6600935) baseStart_6600935 baseEnd_6600935 := by
    simpa [prefixWord, tailWord_6600935, baseEnd_6600935] using wordTrace_append hprefix tailTrace_6600935
  have hstable : (prefixWord ++ tailWord_6600935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600935).length < 2 ^ (prefixWord ++ tailWord_6600935).sum := by decide
  have hdescent : baseEnd_6600935 < baseStart_6600935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600957 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_6600957 : Nat := 118140960795 + 6600957 * 2 ^ 59
def prefixEnd_6600957 : Nat := 4983230072969 + 3 ^ 40 * 6600957 * 2
def baseEnd_6600957 : Nat := 1129821240220211819693419

theorem tailTrace_6600957 : CollatzResearch.WordTrace tailWord_6600957 prefixEnd_6600957 1129821240220211819693419 := by
  unfold tailWord_6600957
  simp only [CollatzResearch.WordTrace]
  refine ⟨240756680746867617547497125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160504453831245078364998083 240756680746867617547497125)
  ·
    refine ⟨45141877640037678290155711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240756680746867617547497125 45141877640037678290155711)
    ·
      refine ⟨67712816460056517435233567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45141877640037678290155711 67712816460056517435233567)
      ·
        refine ⟨101569224690084776152850351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67712816460056517435233567 101569224690084776152850351)
        ·
          refine ⟨152353837035127164229275527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101569224690084776152850351 152353837035127164229275527)
          ·
            refine ⟨228530755552690746343913291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152353837035127164229275527 228530755552690746343913291)
            ·
              refine ⟨342796133329036119515869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228530755552690746343913291 342796133329036119515869937)
              ·
                refine ⟨257097099996777089636902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342796133329036119515869937 257097099996777089636902453)
                ·
                  refine ⟨24102853124697852153459605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257097099996777089636902453 24102853124697852153459605)
                  ·
                    refine ⟨1129821240220211819693419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24102853124697852153459605 1129821240220211819693419)
                    ·
                      rfl

theorem cell23_6600957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_6600957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600957 prefixEnd_6600957 := by exact prefixLift 6600957
  have htrace : WordTrace (prefixWord ++ tailWord_6600957) baseStart_6600957 baseEnd_6600957 := by
    simpa [prefixWord, tailWord_6600957, baseEnd_6600957] using wordTrace_append hprefix tailTrace_6600957
  have hstable : (prefixWord ++ tailWord_6600957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600957).length < 2 ^ (prefixWord ++ tailWord_6600957).sum := by decide
  have hdescent : baseEnd_6600957 < baseStart_6600957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600968 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_6600968 : Nat := 118140960795 + 6600968 * 2 ^ 59
def prefixEnd_6600968 : Nat := 4983230072969 + 3 ^ 40 * 6600968 * 2
def baseEnd_6600968 : Nat := 3389469368947834916042707

theorem tailTrace_6600968 : CollatzResearch.WordTrace tailWord_6600968 prefixEnd_6600968 3389469368947834916042707 := by
  unfold tailWord_6600968
  simp only [CollatzResearch.WordTrace]
  refine ⟨120378540974913883213073779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160504721299885177617431705 120378540974913883213073779)
  ·
    refine ⟨180567811462370824819610669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120378540974913883213073779 180567811462370824819610669)
    ·
      refine ⟨67712929298389059307354001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180567811462370824819610669 67712929298389059307354001)
      ·
        refine ⟨50784696973791794480515501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67712929298389059307354001 50784696973791794480515501)
        ·
          refine ⟨19044261365171922930193313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50784696973791794480515501 19044261365171922930193313)
          ·
            refine ⟨14283196023878942197644985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19044261365171922930193313 14283196023878942197644985)
            ·
              refine ⟨10712397017909206648233739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14283196023878942197644985 10712397017909206648233739)
              ·
                refine ⟨16068595526863809972350609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10712397017909206648233739 16068595526863809972350609)
                ·
                  refine ⟨12051446645147857479262957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16068595526863809972350609 12051446645147857479262957)
                  ·
                    refine ⟨4519292491930446554723609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12051446645147857479262957 4519292491930446554723609)
                    ·
                      refine ⟨3389469368947834916042707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519292491930446554723609 3389469368947834916042707)
                      ·
                        rfl

theorem cell23_6600968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_6600968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600968 prefixEnd_6600968 := by exact prefixLift 6600968
  have htrace : WordTrace (prefixWord ++ tailWord_6600968) baseStart_6600968 baseEnd_6600968 := by
    simpa [prefixWord, tailWord_6600968, baseEnd_6600968] using wordTrace_append hprefix tailTrace_6600968
  have hstable : (prefixWord ++ tailWord_6600968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600968).length < 2 ^ (prefixWord ++ tailWord_6600968).sum := by decide
  have hdescent : baseEnd_6600968 < baseStart_6600968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600974 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_6600974 : Nat := 118140960795 + 6600974 * 2 ^ 59
def prefixEnd_6600974 : Nat := 4983230072969 + 3 ^ 40 * 6600974 * 2
def baseEnd_6600974 : Nat := 1129824149943920630855893

theorem tailTrace_6600974 : CollatzResearch.WordTrace tailWord_6600974 prefixEnd_6600974 1129824149943920630855893 := by
  unfold tailWord_6600974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30094662598475753681358247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160504867191870686300577317 30094662598475753681358247)
  ·
    refine ⟨45141993897713630522037371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30094662598475753681358247 45141993897713630522037371)
    ·
      refine ⟨67712990846570445783056057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45141993897713630522037371 67712990846570445783056057)
      ·
        refine ⟨50784743134927834337292043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67712990846570445783056057 50784743134927834337292043)
        ·
          refine ⟨76177114702391751505938065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50784743134927834337292043 76177114702391751505938065)
          ·
            refine ⟨57132836026793813629453549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76177114702391751505938065 57132836026793813629453549)
            ·
              refine ⟨21424813510047680111045081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57132836026793813629453549 21424813510047680111045081)
              ·
                refine ⟨16068610132535760083283811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21424813510047680111045081 16068610132535760083283811)
                ·
                  refine ⟨24102915198803640124925717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16068610132535760083283811 24102915198803640124925717)
                  ·
                    refine ⟨1129824149943920630855893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24102915198803640124925717 1129824149943920630855893)
                    ·
                      rfl

theorem cell23_6600974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_6600974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600974 prefixEnd_6600974 := by exact prefixLift 6600974
  have htrace : WordTrace (prefixWord ++ tailWord_6600974) baseStart_6600974 baseEnd_6600974 := by
    simpa [prefixWord, tailWord_6600974, baseEnd_6600974] using wordTrace_append hprefix tailTrace_6600974
  have hstable : (prefixWord ++ tailWord_6600974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600974).length < 2 ^ (prefixWord ++ tailWord_6600974).sum := by decide
  have hdescent : baseEnd_6600974 < baseStart_6600974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600991 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 2, 4]
def baseStart_6600991 : Nat := 118140960795 + 6600991 * 2 ^ 59
def prefixEnd_6600991 : Nat := 4983230072969 + 3 ^ 40 * 6600991 * 2
def baseEnd_6600991 : Nat := 1129827059667629442018367

theorem tailTrace_6600991 : CollatzResearch.WordTrace tailWord_6600991 prefixEnd_6600991 1129827059667629442018367 := by
  unfold tailWord_6600991
  simp only [CollatzResearch.WordTrace]
  refine ⟨240757920828744441354234827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160505280552496294236156551 240757920828744441354234827)
  ·
    refine ⟨361136881243116662031352241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240757920828744441354234827 361136881243116662031352241)
    ·
      refine ⟨270852660932337496523514181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361136881243116662031352241 270852660932337496523514181)
      ·
        refine ⟨50784873924813280598158909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270852660932337496523514181 50784873924813280598158909)
        ·
          refine ⟨19044327721804980224309591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50784873924813280598158909 19044327721804980224309591)
          ·
            refine ⟨28566491582707470336464387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19044327721804980224309591 28566491582707470336464387)
            ·
              refine ⟨42849737374061205504696581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28566491582707470336464387 42849737374061205504696581)
              ·
                refine ⟨8034325757636476032130609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42849737374061205504696581 8034325757636476032130609)
                ·
                  refine ⟨6025744318227357024097957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034325757636476032130609 6025744318227357024097957)
                  ·
                    refine ⟨1129827059667629442018367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025744318227357024097957 1129827059667629442018367)
                    ·
                      rfl

theorem cell23_6600991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_6600991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600991 prefixEnd_6600991 := by exact prefixLift 6600991
  have htrace : WordTrace (prefixWord ++ tailWord_6600991) baseStart_6600991 baseEnd_6600991 := by
    simpa [prefixWord, tailWord_6600991, baseEnd_6600991] using wordTrace_append hprefix tailTrace_6600991
  have hstable : (prefixWord ++ tailWord_6600991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600991).length < 2 ^ (prefixWord ++ tailWord_6600991).sum := by decide
  have hdescent : baseEnd_6600991 < baseStart_6600991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6600992 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6600992 : Nat := 118140960795 + 6600992 * 2 ^ 59
def prefixEnd_6600992 : Nat := 4983230072969 + 3 ^ 40 * 6600992 * 2
def baseEnd_6600992 : Nat := 3389481692483542822142597

theorem tailTrace_6600992 : CollatzResearch.WordTrace tailWord_6600992 prefixEnd_6600992 3389481692483542822142597 := by
  unfold tailWord_6600992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120378978650870409262510615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160505304867827212350014153 120378978650870409262510615)
  ·
    refine ⟨180568467976305613893765923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120378978650870409262510615 180568467976305613893765923)
    ·
      refine ⟨270852701964458420840648885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180568467976305613893765923 270852701964458420840648885)
      ·
        refine ⟨25392440809167976953810833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270852701964458420840648885 25392440809167976953810833)
        ·
          refine ⟨19044330606875982715358125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25392440809167976953810833 19044330606875982715358125)
          ·
            refine ⟨7141623977578493518259297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19044330606875982715358125 7141623977578493518259297)
            ·
              refine ⟨5356217983183870138694473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141623977578493518259297 5356217983183870138694473)
              ·
                refine ⟨4017163487387902604020855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356217983183870138694473 4017163487387902604020855)
                ·
                  refine ⟨6025745231081853906031283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017163487387902604020855 6025745231081853906031283)
                  ·
                    refine ⟨9038617846622780859046925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025745231081853906031283 9038617846622780859046925)
                    ·
                      refine ⟨3389481692483542822142597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038617846622780859046925 3389481692483542822142597)
                      ·
                        rfl

theorem cell23_6600992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6600992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6600992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6600992 prefixEnd_6600992 := by exact prefixLift 6600992
  have htrace : WordTrace (prefixWord ++ tailWord_6600992) baseStart_6600992 baseEnd_6600992 := by
    simpa [prefixWord, tailWord_6600992, baseEnd_6600992] using wordTrace_append hprefix tailTrace_6600992
  have hstable : (prefixWord ++ tailWord_6600992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6600992).length < 2 ^ (prefixWord ++ tailWord_6600992).sum := by decide
  have hdescent : baseEnd_6600992 < baseStart_6600992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6600992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601007 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_6601007 : Nat := 118140960795 + 6601007 * 2 ^ 59
def prefixEnd_6601007 : Nat := 4983230072969 + 3 ^ 40 * 6601007 * 2
def baseEnd_6601007 : Nat := 3389489394693360263455027

theorem tailTrace_6601007 : CollatzResearch.WordTrace tailWord_6601007 prefixEnd_6601007 3389489394693360263455027 := by
  unfold tailWord_6601007
  simp only [CollatzResearch.WordTrace]
  refine ⟨240758504396686476086817275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160505669597790984057878183 240758504396686476086817275)
  ·
    refine ⟨361137756595029714130225913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240758504396686476086817275 361137756595029714130225913)
    ·
      refine ⟨270853317446272285597669435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361137756595029714130225913 270853317446272285597669435)
      ·
        refine ⟨406279976169408428396504153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270853317446272285597669435 406279976169408428396504153)
        ·
          refine ⟨304709982127056321297378115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406279976169408428396504153 304709982127056321297378115)
          ·
            refine ⟨457064973190584481946067173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304709982127056321297378115 457064973190584481946067173)
            ·
              refine ⟨85699682473234590364887595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 457064973190584481946067173 85699682473234590364887595)
              ·
                refine ⟨128549523709851885547331393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85699682473234590364887595 128549523709851885547331393)
                ·
                  refine ⟨96412142782388914160498545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128549523709851885547331393 96412142782388914160498545)
                  ·
                    refine ⟨72309107086791685620373909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96412142782388914160498545 72309107086791685620373909)
                    ·
                      refine ⟨3389489394693360263455027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72309107086791685620373909 3389489394693360263455027)
                      ·
                        rfl

theorem cell23_6601007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_6601007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601007 prefixEnd_6601007 := by exact prefixLift 6601007
  have htrace : WordTrace (prefixWord ++ tailWord_6601007) baseStart_6601007 baseEnd_6601007 := by
    simpa [prefixWord, tailWord_6601007, baseEnd_6601007] using wordTrace_append hprefix tailTrace_6601007
  have hstable : (prefixWord ++ tailWord_6601007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601007).length < 2 ^ (prefixWord ++ tailWord_6601007).sum := by decide
  have hdescent : baseEnd_6601007 < baseStart_6601007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601031 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_6601031 : Nat := 118140960795 + 6601031 * 2 ^ 59
def prefixEnd_6601031 : Nat := 4983230072969 + 3 ^ 40 * 6601031 * 2
def baseEnd_6601031 : Nat := 3389501718229068169554917

theorem tailTrace_6601031 : CollatzResearch.WordTrace tailWord_6601031 prefixEnd_6601031 3389501718229068169554917 := by
  unfold tailWord_6601031
  simp only [CollatzResearch.WordTrace]
  refine ⟨240759379748599528185690947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160506253165733018790460631 240759379748599528185690947)
  ·
    refine ⟨361139069622899292278536421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240759379748599528185690947 361139069622899292278536421)
    ·
      refine ⟨67713575554293617302225579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361139069622899292278536421 67713575554293617302225579)
      ·
        refine ⟨101570363331440425953338369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67713575554293617302225579 101570363331440425953338369)
        ·
          refine ⟨76177772498580319465003777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101570363331440425953338369 76177772498580319465003777)
          ·
            refine ⟨57133329373935239598752833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76177772498580319465003777 57133329373935239598752833)
            ·
              refine ⟨42849997030451429699064625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57133329373935239598752833 42849997030451429699064625)
              ·
                refine ⟨32137497772838572274298469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42849997030451429699064625 32137497772838572274298469)
                ·
                  refine ⟨6025780832407232301430963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32137497772838572274298469 6025780832407232301430963)
                  ·
                    refine ⟨9038671248610848452146445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025780832407232301430963 9038671248610848452146445)
                    ·
                      refine ⟨3389501718229068169554917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038671248610848452146445 3389501718229068169554917)
                      ·
                        rfl

theorem cell23_6601031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_6601031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601031 prefixEnd_6601031 := by exact prefixLift 6601031
  have htrace : WordTrace (prefixWord ++ tailWord_6601031) baseStart_6601031 baseEnd_6601031 := by
    simpa [prefixWord, tailWord_6601031, baseEnd_6601031] using wordTrace_append hprefix tailTrace_6601031
  have hstable : (prefixWord ++ tailWord_6601031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601031).length < 2 ^ (prefixWord ++ tailWord_6601031).sum := by decide
  have hdescent : baseEnd_6601031 < baseStart_6601031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601071 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 1, 4, 2]
def baseStart_6601071 : Nat := 118140960795 + 6601071 * 2 ^ 59
def prefixEnd_6601071 : Nat := 4983230072969 + 3 ^ 40 * 6601071 * 2
def baseEnd_6601071 : Nat := 3389522257455248013054733

theorem tailTrace_6601071 : CollatzResearch.WordTrace tailWord_6601071 prefixEnd_6601071 3389522257455248013054733 := by
  unfold tailWord_6601071
  simp only [CollatzResearch.WordTrace]
  refine ⟨240760838668454615017147067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160507225778969743344764711 240760838668454615017147067)
  ·
    refine ⟨361141258002681922525720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240760838668454615017147067 361141258002681922525720601)
    ·
      refine ⟨270855943502011441894290451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361141258002681922525720601 270855943502011441894290451)
      ·
        refine ⟨406283915253017162841435677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270855943502011441894290451 406283915253017162841435677)
        ·
          refine ⟨152356468219881436065538379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406283915253017162841435677 152356468219881436065538379)
          ·
            refine ⟨228534702329822154098307569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152356468219881436065538379 228534702329822154098307569)
            ·
              refine ⟨171401026747366615573730677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228534702329822154098307569 171401026747366615573730677)
              ·
                refine ⟨16068846257565620210037251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171401026747366615573730677 16068846257565620210037251)
                ·
                  refine ⟨24103269386348430315055877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16068846257565620210037251 24103269386348430315055877)
                  ·
                    refine ⟨4519363009940330684072977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24103269386348430315055877 4519363009940330684072977)
                    ·
                      refine ⟨3389522257455248013054733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519363009940330684072977 3389522257455248013054733)
                      ·
                        rfl

theorem cell23_6601071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 4, 2].length) (baseStart_6601071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601071 prefixEnd_6601071 := by exact prefixLift 6601071
  have htrace : WordTrace (prefixWord ++ tailWord_6601071) baseStart_6601071 baseEnd_6601071 := by
    simpa [prefixWord, tailWord_6601071, baseEnd_6601071] using wordTrace_append hprefix tailTrace_6601071
  have hstable : (prefixWord ++ tailWord_6601071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601071).length < 2 ^ (prefixWord ++ tailWord_6601071).sum := by decide
  have hdescent : baseEnd_6601071 < baseStart_6601071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601084 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_6601084 : Nat := 118140960795 + 6601084 * 2 ^ 59
def prefixEnd_6601084 : Nat := 4983230072969 + 3 ^ 40 * 6601084 * 2
def baseEnd_6601084 : Nat := 3389528932703756462192173

theorem tailTrace_6601084 : CollatzResearch.WordTrace tailWord_6601084 prefixEnd_6601084 3389528932703756462192173 := by
  unfold tailWord_6601084
  simp only [CollatzResearch.WordTrace]
  refine ⟨120380656408703759118685153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160507541878271678824913537 120380656408703759118685153)
  ·
    refine ⟨90285492306527819339013865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120380656408703759118685153 90285492306527819339013865)
    ·
      refine ⟨67714119229895864504260399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90285492306527819339013865 67714119229895864504260399)
      ·
        refine ⟨101571178844843796756390599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67714119229895864504260399 101571178844843796756390599)
        ·
          refine ⟨152356768267265695134585899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101571178844843796756390599 152356768267265695134585899)
          ·
            refine ⟨228535152400898542701878849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152356768267265695134585899 228535152400898542701878849)
            ·
              refine ⟨171401364300673907026409137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228535152400898542701878849 171401364300673907026409137)
              ·
                refine ⟨128551023225505430269806853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171401364300673907026409137 128551023225505430269806853)
                ·
                  refine ⟨24103316854782268175588785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128551023225505430269806853 24103316854782268175588785)
                  ·
                    refine ⟨18077487641086701131691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24103316854782268175588785 18077487641086701131691589)
                    ·
                      refine ⟨3389528932703756462192173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18077487641086701131691589 3389528932703756462192173)
                      ·
                        rfl

theorem cell23_6601084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_6601084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601084 prefixEnd_6601084 := by exact prefixLift 6601084
  have htrace : WordTrace (prefixWord ++ tailWord_6601084) baseStart_6601084 baseEnd_6601084 := by
    simpa [prefixWord, tailWord_6601084, baseEnd_6601084] using wordTrace_append hprefix tailTrace_6601084
  have hstable : (prefixWord ++ tailWord_6601084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601084).length < 2 ^ (prefixWord ++ tailWord_6601084).sum := by decide
  have hdescent : baseEnd_6601084 < baseStart_6601084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601091 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5]
def baseStart_6601091 : Nat := 118140960795 + 6601091 * 2 ^ 59
def prefixEnd_6601091 : Nat := 4983230072969 + 3 ^ 40 * 6601091 * 2
def baseEnd_6601091 : Nat := 3389532527068337934804641

theorem tailTrace_6601091 : CollatzResearch.WordTrace tailWord_6601091 prefixEnd_6601091 3389532527068337934804641 := by
  unfold tailWord_6601091
  simp only [CollatzResearch.WordTrace]
  refine ⟨240761568128382158432875127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160507712085588105621916751 240761568128382158432875127)
  ·
    refine ⟨361142352192573237649312691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240761568128382158432875127 361142352192573237649312691)
    ·
      refine ⟨541713528288859856473969037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361142352192573237649312691 541713528288859856473969037)
      ·
        refine ⟨203142573108322446177738389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541713528288859856473969037 203142573108322446177738389)
        ·
          refine ⟨9522308114452614664581487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203142573108322446177738389 9522308114452614664581487)
          ·
            refine ⟨14283462171678921996872231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9522308114452614664581487 14283462171678921996872231)
            ·
              refine ⟨21425193257518382995308347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14283462171678921996872231 21425193257518382995308347)
              ·
                refine ⟨32137789886277574492962521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21425193257518382995308347 32137789886277574492962521)
                ·
                  refine ⟨24103342414708180869721891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32137789886277574492962521 24103342414708180869721891)
                  ·
                    refine ⟨36155013622062271304582837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24103342414708180869721891 36155013622062271304582837)
                    ·
                      refine ⟨3389532527068337934804641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36155013622062271304582837 3389532527068337934804641)
                      ·
                        rfl

theorem cell23_6601091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_6601091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601091 prefixEnd_6601091 := by exact prefixLift 6601091
  have htrace : WordTrace (prefixWord ++ tailWord_6601091) baseStart_6601091 baseEnd_6601091 := by
    simpa [prefixWord, tailWord_6601091, baseEnd_6601091] using wordTrace_append hprefix tailTrace_6601091
  have hstable : (prefixWord ++ tailWord_6601091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601091).length < 2 ^ (prefixWord ++ tailWord_6601091).sum := by decide
  have hdescent : baseEnd_6601091 < baseStart_6601091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601104 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_6601104 : Nat := 118140960795 + 6601104 * 2 ^ 59
def prefixEnd_6601104 : Nat := 4983230072969 + 3 ^ 40 * 6601104 * 2
def baseEnd_6601104 : Nat := 3389539202316846383942081

theorem tailTrace_6601104 : CollatzResearch.WordTrace tailWord_6601104 prefixEnd_6601104 3389539202316846383942081 := by
  unfold tailWord_6601104
  simp only [CollatzResearch.WordTrace]
  refine ⟨120381021138667530826549183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160508028184890041102065577 120381021138667530826549183)
  ·
    refine ⟨180571531708001296239823775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120381021138667530826549183 180571531708001296239823775)
    ·
      refine ⟨270857297562001944359735663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180571531708001296239823775 270857297562001944359735663)
      ·
        refine ⟨406285946343002916539603495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270857297562001944359735663 406285946343002916539603495)
        ·
          refine ⟨609428919514504374809405243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406285946343002916539603495 609428919514504374809405243)
          ·
            refine ⟨914143379271756562214107865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609428919514504374809405243 914143379271756562214107865)
            ·
              refine ⟨685607534453817421660580899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914143379271756562214107865 685607534453817421660580899)
              ·
                refine ⟨1028411301680726132490871349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685607534453817421660580899 1028411301680726132490871349)
                ·
                  refine ⟨96413559532568074921019189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028411301680726132490871349 96413559532568074921019189)
                  ·
                    refine ⟨9038771206178257023845549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96413559532568074921019189 9038771206178257023845549)
                    ·
                      refine ⟨3389539202316846383942081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038771206178257023845549 3389539202316846383942081)
                      ·
                        rfl

theorem cell23_6601104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_6601104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601104 prefixEnd_6601104 := by exact prefixLift 6601104
  have htrace : WordTrace (prefixWord ++ tailWord_6601104) baseStart_6601104 baseEnd_6601104 := by
    simpa [prefixWord, tailWord_6601104, baseEnd_6601104] using wordTrace_append hprefix tailTrace_6601104
  have hstable : (prefixWord ++ tailWord_6601104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601104).length < 2 ^ (prefixWord ++ tailWord_6601104).sum := by decide
  have hdescent : baseEnd_6601104 < baseStart_6601104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601111 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 5]
def baseStart_6601111 : Nat := 118140960795 + 6601111 * 2 ^ 59
def prefixEnd_6601111 : Nat := 4983230072969 + 3 ^ 40 * 6601111 * 2
def baseEnd_6601111 : Nat := 376615866297936428506061

theorem tailTrace_6601111 : CollatzResearch.WordTrace tailWord_6601111 prefixEnd_6601111 376615866297936428506061 := by
  unfold tailWord_6601111
  simp only [CollatzResearch.WordTrace]
  refine ⟨240762297588309701848603187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160508198392206467899068791 240762297588309701848603187)
  ·
    refine ⟨361143446382464552772904781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240762297588309701848603187 361143446382464552772904781)
    ·
      refine ⟨135428792393424207289839293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361143446382464552772904781 135428792393424207289839293)
      ·
        refine ⟨50785797147534077733689735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135428792393424207289839293 50785797147534077733689735)
        ·
          refine ⟨76178695721301116600534603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50785797147534077733689735 76178695721301116600534603)
          ·
            refine ⟨114268043581951674900801905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76178695721301116600534603 114268043581951674900801905)
            ·
              refine ⟨85701032686463756175601429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114268043581951674900801905 85701032686463756175601429)
              ·
                refine ⟨4017235907177988570731317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85701032686463756175601429 4017235907177988570731317)
                ·
                  refine ⟨376615866297936428506061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017235907177988570731317 376615866297936428506061)
                  ·
                    rfl

theorem cell23_6601111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 5].length) (baseStart_6601111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601111 prefixEnd_6601111 := by exact prefixLift 6601111
  have htrace : WordTrace (prefixWord ++ tailWord_6601111) baseStart_6601111 baseEnd_6601111 := by
    simpa [prefixWord, tailWord_6601111, baseEnd_6601111] using wordTrace_append hprefix tailTrace_6601111
  have hstable : (prefixWord ++ tailWord_6601111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601111).length < 2 ^ (prefixWord ++ tailWord_6601111).sum := by decide
  have hdescent : baseEnd_6601111 < baseStart_6601111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601124 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_6601124 : Nat := 118140960795 + 6601124 * 2 ^ 59
def prefixEnd_6601124 : Nat := 4983230072969 + 3 ^ 40 * 6601124 * 2
def baseEnd_6601124 : Nat := 1129849823976645435230663

theorem tailTrace_6601124 : CollatzResearch.WordTrace tailWord_6601124 prefixEnd_6601124 1129849823976645435230663 := by
  unfold tailWord_6601124
  simp only [CollatzResearch.WordTrace]
  refine ⟨120381385868631302534413213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160508514491508403379217617 120381385868631302534413213)
  ·
    refine ⟨45143019700736738450404955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120381385868631302534413213 45143019700736738450404955)
    ·
      refine ⟨67714529551105107675607433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45143019700736738450404955 67714529551105107675607433)
      ·
        refine ⟨50785897163328830756705575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67714529551105107675607433 50785897163328830756705575)
        ·
          refine ⟨76178845744993246135058363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50785897163328830756705575 76178845744993246135058363)
          ·
            refine ⟨114268268617489869202587545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76178845744993246135058363 114268268617489869202587545)
            ·
              refine ⟨85701201463117401901940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114268268617489869202587545 85701201463117401901940659)
              ·
                refine ⟨128551802194676102852910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85701201463117401901940659 128551802194676102852910989)
                ·
                  refine ⟨48206925823003538569841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128551802194676102852910989 48206925823003538569841621)
                  ·
                    refine ⟨1129849823976645435230663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48206925823003538569841621 1129849823976645435230663)
                    ·
                      rfl

theorem cell23_6601124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_6601124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601124 prefixEnd_6601124 := by exact prefixLift 6601124
  have htrace : WordTrace (prefixWord ++ tailWord_6601124) baseStart_6601124 baseEnd_6601124 := by
    simpa [prefixWord, tailWord_6601124, baseEnd_6601124] using wordTrace_append hprefix tailTrace_6601124
  have hstable : (prefixWord ++ tailWord_6601124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601124).length < 2 ^ (prefixWord ++ tailWord_6601124).sum := by decide
  have hdescent : baseEnd_6601124 < baseStart_6601124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601161 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_6601161 : Nat := 118140960795 + 6601161 * 2 ^ 59
def prefixEnd_6601161 : Nat := 4983230072969 + 3 ^ 40 * 6601161 * 2
def baseEnd_6601161 : Nat := 3389568470714152660929319

theorem tailTrace_6601161 : CollatzResearch.WordTrace tailWord_6601161 prefixEnd_6601161 3389568470714152660929319 := by
  unfold tailWord_6601161
  simp only [CollatzResearch.WordTrace]
  refine ⟨240764121238128560387923337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160509414158752373591948891 240764121238128560387923337)
  ·
    refine ⟨180573090928596420290942503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240764121238128560387923337 180573090928596420290942503)
    ·
      refine ⟨270859636392894630436413755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180573090928596420290942503 270859636392894630436413755)
      ·
        refine ⟨406289454589341945654620633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270859636392894630436413755 406289454589341945654620633)
        ·
          refine ⟨304717090942006459240965475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406289454589341945654620633 304717090942006459240965475)
          ·
            refine ⟨457075636413009688861448213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304717090942006459240965475 457075636413009688861448213)
            ·
              refine ⟨21425420456859829165380385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 457075636413009688861448213 21425420456859829165380385)
              ·
                refine ⟨16069065342644871874035289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21425420456859829165380385 16069065342644871874035289)
                ·
                  refine ⟨12051799006983653905526467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16069065342644871874035289 12051799006983653905526467)
                  ·
                    refine ⟨18077698510475480858289701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12051799006983653905526467 18077698510475480858289701)
                    ·
                      refine ⟨3389568470714152660929319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18077698510475480858289701 3389568470714152660929319)
                      ·
                        rfl

theorem cell23_6601161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_6601161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601161 prefixEnd_6601161 := by exact prefixLift 6601161
  have htrace : WordTrace (prefixWord ++ tailWord_6601161) baseStart_6601161 baseEnd_6601161 := by
    simpa [prefixWord, tailWord_6601161, baseEnd_6601161] using wordTrace_append hprefix tailTrace_6601161
  have hstable : (prefixWord ++ tailWord_6601161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601161).length < 2 ^ (prefixWord ++ tailWord_6601161).sum := by decide
  have hdescent : baseEnd_6601161 < baseStart_6601161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601178 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_6601178 : Nat := 118140960795 + 6601178 * 2 ^ 59
def prefixEnd_6601178 : Nat := 4983230072969 + 3 ^ 40 * 6601178 * 2
def baseEnd_6601178 : Nat := 3389577199885279094416741

theorem tailTrace_6601178 : CollatzResearch.WordTrace tailWord_6601178 prefixEnd_6601178 3389577199885279094416741 := by
  unfold tailWord_6601178
  simp only [CollatzResearch.WordTrace]
  refine ⟨60191185319766743072823047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160509827519377981527528125 60191185319766743072823047)
  ·
    refine ⟨90286777979650114609234571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60191185319766743072823047 90286777979650114609234571)
    ·
      refine ⟨135430166969475171913851857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90286777979650114609234571 135430166969475171913851857)
      ·
        refine ⟨101572625227106378935388893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135430166969475171913851857 101572625227106378935388893)
        ·
          refine ⟨38089734460164892100770835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101572625227106378935388893 38089734460164892100770835)
          ·
            refine ⟨57134601690247338151156253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38089734460164892100770835 57134601690247338151156253)
            ·
              refine ⟨21425475633842751806683595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57134601690247338151156253 21425475633842751806683595)
              ·
                refine ⟨32138213450764127710025393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21425475633842751806683595 32138213450764127710025393)
                ·
                  refine ⟨24103660088073095782519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32138213450764127710025393 24103660088073095782519045)
                  ·
                    refine ⟨4519436266513705459222321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24103660088073095782519045 4519436266513705459222321)
                    ·
                      refine ⟨3389577199885279094416741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519436266513705459222321 3389577199885279094416741)
                      ·
                        rfl

theorem cell23_6601178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_6601178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601178 prefixEnd_6601178 := by exact prefixLift 6601178
  have htrace : WordTrace (prefixWord ++ tailWord_6601178) baseStart_6601178 baseEnd_6601178 := by
    simpa [prefixWord, tailWord_6601178, baseEnd_6601178] using wordTrace_append hprefix tailTrace_6601178
  have hstable : (prefixWord ++ tailWord_6601178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601178).length < 2 ^ (prefixWord ++ tailWord_6601178).sum := by decide
  have hdescent : baseEnd_6601178 < baseStart_6601178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601198 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_6601198 : Nat := 118140960795 + 6601198 * 2 ^ 59
def prefixEnd_6601198 : Nat := 4983230072969 + 3 ^ 40 * 6601198 * 2
def baseEnd_6601198 : Nat := 3389587469498369016166649

theorem tailTrace_6601198 : CollatzResearch.WordTrace tailWord_6601198 prefixEnd_6601198 3389587469498369016166649 := by
  unfold tailWord_6601198
  simp only [CollatzResearch.WordTrace]
  refine ⟨30095683842374314463377531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160510313825996343804680165 30095683842374314463377531)
  ·
    refine ⟨45143525763561471695066297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30095683842374314463377531 45143525763561471695066297)
    ·
      refine ⟨33857644322671103771299723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45143525763561471695066297 33857644322671103771299723)
      ·
        refine ⟨50786466484006655656949585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33857644322671103771299723 50786466484006655656949585)
        ·
          refine ⟨38089849863004991742712189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50786466484006655656949585 38089849863004991742712189)
          ·
            refine ⟨14283693698626871903517071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38089849863004991742712189 14283693698626871903517071)
            ·
              refine ⟨21425540547940307855275607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14283693698626871903517071 21425540547940307855275607)
              ·
                refine ⟨32138310821910461782913411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21425540547940307855275607 32138310821910461782913411)
                ·
                  refine ⟨48207466232865692674370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32138310821910461782913411 48207466232865692674370117)
                  ·
                    refine ⟨9038899918662317376444397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48207466232865692674370117 9038899918662317376444397)
                    ·
                      refine ⟨3389587469498369016166649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038899918662317376444397 3389587469498369016166649)
                      ·
                        rfl

theorem cell23_6601198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_6601198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601198 prefixEnd_6601198 := by exact prefixLift 6601198
  have htrace : WordTrace (prefixWord ++ tailWord_6601198) baseStart_6601198 baseEnd_6601198 := by
    simpa [prefixWord, tailWord_6601198, baseEnd_6601198] using wordTrace_append hprefix tailTrace_6601198
  have hstable : (prefixWord ++ tailWord_6601198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601198).length < 2 ^ (prefixWord ++ tailWord_6601198).sum := by decide
  have hdescent : baseEnd_6601198 < baseStart_6601198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601245 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_6601245 : Nat := 118140960795 + 6601245 * 2 ^ 59
def prefixEnd_6601245 : Nat := 4983230072969 + 3 ^ 40 * 6601245 * 2
def baseEnd_6601245 : Nat := 3389611603089130332278933

theorem tailTrace_6601245 : CollatzResearch.WordTrace tailWord_6601245 prefixEnd_6601245 3389611603089130332278933 := by
  unfold tailWord_6601245
  simp only [CollatzResearch.WordTrace]
  refine ⟨240767184969824242733981189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160511456646549495155987459 240767184969824242733981189)
  ·
    refine ⟨45143847181842045512621473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240767184969824242733981189 45143847181842045512621473)
    ·
      refine ⟨33857885386381534134466105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45143847181842045512621473 33857885386381534134466105)
      ·
        refine ⟨25393414039786150600849579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33857885386381534134466105 25393414039786150600849579)
        ·
          refine ⟨38090121059679225901274369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393414039786150600849579 38090121059679225901274369)
          ·
            refine ⟨28567590794759419425955777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38090121059679225901274369 28567590794759419425955777)
            ·
              refine ⟨21425693096069564569466833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28567590794759419425955777 21425693096069564569466833)
              ·
                refine ⟨16069269822052173427100125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21425693096069564569466833 16069269822052173427100125)
                ·
                  refine ⟨6025976183269565035162547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16069269822052173427100125 6025976183269565035162547)
                  ·
                    refine ⟨9038964274904347552743821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025976183269565035162547 9038964274904347552743821)
                    ·
                      refine ⟨3389611603089130332278933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9038964274904347552743821 3389611603089130332278933)
                      ·
                        rfl

theorem cell23_6601245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_6601245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601245 prefixEnd_6601245 := by exact prefixLift 6601245
  have htrace : WordTrace (prefixWord ++ tailWord_6601245) baseStart_6601245 baseEnd_6601245 := by
    simpa [prefixWord, tailWord_6601245, baseEnd_6601245] using wordTrace_append hprefix tailTrace_6601245
  have hstable : (prefixWord ++ tailWord_6601245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601245).length < 2 ^ (prefixWord ++ tailWord_6601245).sum := by decide
  have hdescent : baseEnd_6601245 < baseStart_6601245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601295 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 2, 4]
def baseStart_6601295 : Nat := 118140960795 + 6601295 * 2 ^ 59
def prefixEnd_6601295 : Nat := 4983230072969 + 3 ^ 40 * 6601295 * 2
def baseEnd_6601295 : Nat := 1129879092373951712217901

theorem tailTrace_6601295 : CollatzResearch.WordTrace tailWord_6601295 prefixEnd_6601295 1129879092373951712217901 := by
  unfold tailWord_6601295
  simp only [CollatzResearch.WordTrace]
  refine ⟨240769008619643101273301339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160512672413095400848867559 240769008619643101273301339)
  ·
    refine ⟨361153512929464651909952009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240769008619643101273301339 361153512929464651909952009)
    ·
      refine ⟨270865134697098488932464007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361153512929464651909952009 270865134697098488932464007)
      ·
        refine ⟨406297702045647733398696011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270865134697098488932464007 406297702045647733398696011)
        ·
          refine ⟨609446553068471600098044017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406297702045647733398696011 609446553068471600098044017)
          ·
            refine ⟨457084914801353700073533013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609446553068471600098044017 457084914801353700073533013)
            ·
              refine ⟨5356463845328363672736715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 457084914801353700073533013 5356463845328363672736715)
              ·
                refine ⟨8034695767992545509105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356463845328363672736715 8034695767992545509105073)
                ·
                  refine ⟨6026021825994409131828805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034695767992545509105073 6026021825994409131828805)
                  ·
                    refine ⟨1129879092373951712217901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6026021825994409131828805 1129879092373951712217901)
                    ·
                      rfl

theorem cell23_6601295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_6601295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601295 prefixEnd_6601295 := by exact prefixLift 6601295
  have htrace : WordTrace (prefixWord ++ tailWord_6601295) baseStart_6601295 baseEnd_6601295 := by
    simpa [prefixWord, tailWord_6601295, baseEnd_6601295] using wordTrace_append hprefix tailTrace_6601295
  have hstable : (prefixWord ++ tailWord_6601295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601295).length < 2 ^ (prefixWord ++ tailWord_6601295).sum := by decide
  have hdescent : baseEnd_6601295 < baseStart_6601295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601298 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6601298 : Nat := 118140960795 + 6601298 * 2 ^ 59
def prefixEnd_6601298 : Nat := 4983230072969 + 3 ^ 40 * 6601298 * 2
def baseEnd_6601298 : Nat := 3389638817563818624916189

theorem tailTrace_6601298 : CollatzResearch.WordTrace tailWord_6601298 prefixEnd_6601298 3389638817563818624916189 := by
  unfold tailWord_6601298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60192279509658058196415137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160512745359088155190440365 60192279509658058196415137)
  ·
    refine ⟨45144209632243543647311353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60192279509658058196415137 45144209632243543647311353)
    ·
      refine ⟨33858157224182657735483515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45144209632243543647311353 33858157224182657735483515)
      ·
        refine ⟨50787235836273986603225273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33858157224182657735483515 50787235836273986603225273)
        ·
          refine ⟨38090426877205489952418955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50787235836273986603225273 38090426877205489952418955)
          ·
            refine ⟨57135640315808234928628433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38090426877205489952418955 57135640315808234928628433)
            ·
              refine ⟨42851730236856176196471325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57135640315808234928628433 42851730236856176196471325)
              ·
                refine ⟨16069398838821066073676747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42851730236856176196471325 16069398838821066073676747)
                ·
                  refine ⟨24104098258231599110515121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16069398838821066073676747 24104098258231599110515121)
                  ·
                    refine ⟨18078073693673699332886341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24104098258231599110515121 18078073693673699332886341)
                    ·
                      refine ⟨3389638817563818624916189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18078073693673699332886341 3389638817563818624916189)
                      ·
                        rfl

theorem cell23_6601298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6601298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601298 prefixEnd_6601298 := by exact prefixLift 6601298
  have htrace : WordTrace (prefixWord ++ tailWord_6601298) baseStart_6601298 baseEnd_6601298 := by
    simpa [prefixWord, tailWord_6601298, baseEnd_6601298] using wordTrace_append hprefix tailTrace_6601298
  have hstable : (prefixWord ++ tailWord_6601298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601298).length < 2 ^ (prefixWord ++ tailWord_6601298).sum := by decide
  have hdescent : baseEnd_6601298 < baseStart_6601298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601322 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_6601322 : Nat := 118140960795 + 6601322 * 2 ^ 59
def prefixEnd_6601322 : Nat := 4983230072969 + 3 ^ 40 * 6601322 * 2
def baseEnd_6601322 : Nat := 3389651141099526531016079

theorem tailTrace_6601322 : CollatzResearch.WordTrace tailWord_6601322 prefixEnd_6601322 3389651141099526531016079 := by
  unfold tailWord_6601322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60192498347636321221133555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160513328927030189923022813 60192498347636321221133555)
  ·
    refine ⟨90288747521454481831700333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60192498347636321221133555 90288747521454481831700333)
    ·
      refine ⟨33858280320545430686887625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90288747521454481831700333 33858280320545430686887625)
      ·
        refine ⟨25393710240409073015165719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33858280320545430686887625 25393710240409073015165719)
        ·
          refine ⟨38090565360613609522748579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393710240409073015165719 38090565360613609522748579)
          ·
            refine ⟨57135848040920414284122869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38090565360613609522748579 57135848040920414284122869)
            ·
              refine ⟨5356485753836288839136519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57135848040920414284122869 5356485753836288839136519)
              ·
                refine ⟨8034728630754433258704779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356485753836288839136519 8034728630754433258704779)
                ·
                  refine ⟨12052092946131649888057169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8034728630754433258704779 12052092946131649888057169)
                  ·
                    refine ⟨9039069709598737416042877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12052092946131649888057169 9039069709598737416042877)
                    ·
                      refine ⟨3389651141099526531016079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039069709598737416042877 3389651141099526531016079)
                      ·
                        rfl

theorem cell23_6601322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_6601322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601322 prefixEnd_6601322 := by exact prefixLift 6601322
  have htrace : WordTrace (prefixWord ++ tailWord_6601322) baseStart_6601322 baseEnd_6601322 := by
    simpa [prefixWord, tailWord_6601322, baseEnd_6601322] using wordTrace_append hprefix tailTrace_6601322
  have hstable : (prefixWord ++ tailWord_6601322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601322).length < 2 ^ (prefixWord ++ tailWord_6601322).sum := by decide
  have hdescent : baseEnd_6601322 < baseStart_6601322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601335 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_6601335 : Nat := 118140960795 + 6601335 * 2 ^ 59
def prefixEnd_6601335 : Nat := 4983230072969 + 3 ^ 40 * 6601335 * 2
def baseEnd_6601335 : Nat := 3389657816348034980153519

theorem tailTrace_6601335 : CollatzResearch.WordTrace tailWord_6601335 prefixEnd_6601335 3389657816348034980153519 := by
  unfold tailWord_6601335
  simp only [CollatzResearch.WordTrace]
  refine ⟨240770467539498188104757459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160513645026332125403171639 240770467539498188104757459)
  ·
    refine ⟨361155701309247282157136189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240770467539498188104757459 361155701309247282157136189)
    ·
      refine ⟨135433387990967730808926071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361155701309247282157136189 135433387990967730808926071)
      ·
        refine ⟨203150081986451596213389107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135433387990967730808926071 203150081986451596213389107)
        ·
          refine ⟨304725122979677394320083661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203150081986451596213389107 304725122979677394320083661)
          ·
            refine ⟨114271921117379022870031373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304725122979677394320083661 114271921117379022870031373)
            ·
              refine ⟨42851970419017133576261765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114271921117379022870031373 42851970419017133576261765)
              ·
                refine ⟨8034744453565712545549081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42851970419017133576261765 8034744453565712545549081)
                ·
                  refine ⟨6026058340174284409161811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034744453565712545549081 6026058340174284409161811)
                  ·
                    refine ⟨9039087510261426613742717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026058340174284409161811 9039087510261426613742717)
                    ·
                      refine ⟨3389657816348034980153519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039087510261426613742717 3389657816348034980153519)
                      ·
                        rfl

theorem cell23_6601335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_6601335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601335 prefixEnd_6601335 := by exact prefixLift 6601335
  have htrace : WordTrace (prefixWord ++ tailWord_6601335) baseStart_6601335 baseEnd_6601335 := by
    simpa [prefixWord, tailWord_6601335, baseEnd_6601335] using wordTrace_append hprefix tailTrace_6601335
  have hstable : (prefixWord ++ tailWord_6601335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601335).length < 2 ^ (prefixWord ++ tailWord_6601335).sum := by decide
  have hdescent : baseEnd_6601335 < baseStart_6601335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601345 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_6601345 : Nat := 118140960795 + 6601345 * 2 ^ 59
def prefixEnd_6601345 : Nat := 4983230072969 + 3 ^ 40 * 6601345 * 2
def baseEnd_6601345 : Nat := 3389662951154579941028473

theorem tailTrace_6601345 : CollatzResearch.WordTrace tailWord_6601345 prefixEnd_6601345 3389662951154579941028473 := by
  unfold tailWord_6601345
  simp only [CollatzResearch.WordTrace]
  refine ⟨240770832269461959812621489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160513888179641306541747659 240770832269461959812621489)
  ·
    refine ⟨180578124202096469859466117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240770832269461959812621489 180578124202096469859466117)
    ·
      refine ⟨33858398287893088098649897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180578124202096469859466117 33858398287893088098649897)
      ·
        refine ⟨25393798715919816073987423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33858398287893088098649897 25393798715919816073987423)
        ·
          refine ⟨38090698073879724110981135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393798715919816073987423 38090698073879724110981135)
          ·
            refine ⟨57136047110819586166471703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38090698073879724110981135 57136047110819586166471703)
            ·
              refine ⟨85704070666229379249707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57136047110819586166471703 85704070666229379249707555)
              ·
                refine ⟨128556105999344068874561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85704070666229379249707555 128556105999344068874561333)
                ·
                  refine ⟨12052134937438506456990125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128556105999344068874561333 12052134937438506456990125)
                  ·
                    refine ⟨4519550601539439921371297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12052134937438506456990125 4519550601539439921371297)
                    ·
                      refine ⟨3389662951154579941028473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519550601539439921371297 3389662951154579941028473)
                      ·
                        rfl

theorem cell23_6601345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_6601345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601345 prefixEnd_6601345 := by exact prefixLift 6601345
  have htrace : WordTrace (prefixWord ++ tailWord_6601345) baseStart_6601345 baseEnd_6601345 := by
    simpa [prefixWord, tailWord_6601345, baseEnd_6601345] using wordTrace_append hprefix tailTrace_6601345
  have hstable : (prefixWord ++ tailWord_6601345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601345).length < 2 ^ (prefixWord ++ tailWord_6601345).sum := by decide
  have hdescent : baseEnd_6601345 < baseStart_6601345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601358 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6601358 : Nat := 118140960795 + 6601358 * 2 ^ 59
def prefixEnd_6601358 : Nat := 4983230072969 + 3 ^ 40 * 6601358 * 2
def baseEnd_6601358 : Nat := 3389669626403088390165913

theorem tailTrace_6601358 : CollatzResearch.WordTrace tailWord_6601358 prefixEnd_6601358 3389669626403088390165913 := by
  unfold tailWord_6601358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096413302301857879105591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160514204278943242021896485 30096413302301857879105591)
  ·
    refine ⟨45144619953452786818658387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30096413302301857879105591 45144619953452786818658387)
    ·
      refine ⟨67716929930179180227987581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45144619953452786818658387 67716929930179180227987581)
      ·
        refine ⟨25393848723817192585495343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67716929930179180227987581 25393848723817192585495343)
        ·
          refine ⟨38090773085725788878243015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393848723817192585495343 38090773085725788878243015)
          ·
            refine ⟨57136159628588683317364523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38090773085725788878243015 57136159628588683317364523)
            ·
              refine ⟨85704239442883024976046785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57136159628588683317364523 85704239442883024976046785)
              ·
                refine ⟨64278179582162268732035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85704239442883024976046785 64278179582162268732035089)
                ·
                  refine ⟨48208634686621701549026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64278179582162268732035089 48208634686621701549026317)
                  ·
                    refine ⟨18078238007483138080884869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48208634686621701549026317 18078238007483138080884869)
                    ·
                      refine ⟨3389669626403088390165913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18078238007483138080884869 3389669626403088390165913)
                      ·
                        rfl

theorem cell23_6601358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6601358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601358 prefixEnd_6601358 := by exact prefixLift 6601358
  have htrace : WordTrace (prefixWord ++ tailWord_6601358) baseStart_6601358 baseEnd_6601358 := by
    simpa [prefixWord, tailWord_6601358, baseEnd_6601358] using wordTrace_append hprefix tailTrace_6601358
  have hstable : (prefixWord ++ tailWord_6601358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601358).length < 2 ^ (prefixWord ++ tailWord_6601358).sum := by decide
  have hdescent : baseEnd_6601358 < baseStart_6601358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601362 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6601362 : Nat := 118140960795 + 6601362 * 2 ^ 59
def prefixEnd_6601362 : Nat := 4983230072969 + 3 ^ 40 * 6601362 * 2
def baseEnd_6601362 : Nat := 3389671680325706374515895

theorem tailTrace_6601362 : CollatzResearch.WordTrace tailWord_6601362 prefixEnd_6601362 3389671680325706374515895 := by
  unfold tailWord_6601362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60192863077600092928997585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160514301540266914477326893 60192863077600092928997585)
  ·
    refine ⟨45144647308200069696748189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60192863077600092928997585 45144647308200069696748189)
    ·
      refine ⟨16929242740575026136280571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45144647308200069696748189 16929242740575026136280571)
      ·
        refine ⟨25393864110862539204420857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16929242740575026136280571 25393864110862539204420857)
        ·
          refine ⟨19045398083146904403315643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25393864110862539204420857 19045398083146904403315643)
          ·
            refine ⟨28568097124720356604973465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19045398083146904403315643 28568097124720356604973465)
            ·
              refine ⟨21426072843540267453730099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28568097124720356604973465 21426072843540267453730099)
              ·
                refine ⟨32139109265310401180595149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21426072843540267453730099 32139109265310401180595149)
                ·
                  refine ⟨12052165974491400442723181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32139109265310401180595149 12052165974491400442723181)
                  ·
                    refine ⟨4519562240434275166021193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12052165974491400442723181 4519562240434275166021193)
                    ·
                      refine ⟨3389671680325706374515895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519562240434275166021193 3389671680325706374515895)
                      ·
                        rfl

theorem cell23_6601362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6601362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601362 prefixEnd_6601362 := by exact prefixLift 6601362
  have htrace : WordTrace (prefixWord ++ tailWord_6601362) baseStart_6601362 baseEnd_6601362 := by
    simpa [prefixWord, tailWord_6601362, baseEnd_6601362] using wordTrace_append hprefix tailTrace_6601362
  have hstable : (prefixWord ++ tailWord_6601362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601362).length < 2 ^ (prefixWord ++ tailWord_6601362).sum := by decide
  have hdescent : baseEnd_6601362 < baseStart_6601362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601381 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 11]
def baseStart_6601381 : Nat := 118140960795 + 6601381 * 2 ^ 59
def prefixEnd_6601381 : Nat := 4983230072969 + 3 ^ 40 * 6601381 * 2
def baseEnd_6601381 : Nat := 376631270717571311130923

theorem tailTrace_6601381 : CollatzResearch.WordTrace tailWord_6601381 prefixEnd_6601381 376631270717571311130923 := by
  unfold tailWord_6601381
  simp only [CollatzResearch.WordTrace]
  refine ⟨240772145297331537960931997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160514763531554358640621331 240772145297331537960931997)
  ·
    refine ⟨90289554486499326735349499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240772145297331537960931997 90289554486499326735349499)
    ·
      refine ⟨135434331729748990103024249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90289554486499326735349499 135434331729748990103024249)
      ·
        refine ⟨101575748797311742577268187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135434331729748990103024249 101575748797311742577268187)
        ·
          refine ⟨152363623195967613865902281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101575748797311742577268187 152363623195967613865902281)
          ·
            refine ⟨114272717396975710399426711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152363623195967613865902281 114272717396975710399426711)
            ·
              refine ⟨171409076095463565599140067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114272717396975710399426711 171409076095463565599140067)
              ·
                refine ⟨257113614143195348398710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171409076095463565599140067 257113614143195348398710101)
                ·
                  refine ⟨376631270717571311130923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 257113614143195348398710101 376631270717571311130923)
                  ·
                    rfl

theorem cell23_6601381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_6601381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601381 prefixEnd_6601381 := by exact prefixLift 6601381
  have htrace : WordTrace (prefixWord ++ tailWord_6601381) baseStart_6601381 baseEnd_6601381 := by
    simpa [prefixWord, tailWord_6601381, baseEnd_6601381] using wordTrace_append hprefix tailTrace_6601381
  have hstable : (prefixWord ++ tailWord_6601381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601381).length < 2 ^ (prefixWord ++ tailWord_6601381).sum := by decide
  have hdescent : baseEnd_6601381 < baseStart_6601381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601432 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 5]
def baseStart_6601432 : Nat := 118140960795 + 6601432 * 2 ^ 59
def prefixEnd_6601432 : Nat := 4983230072969 + 3 ^ 40 * 6601432 * 2
def baseEnd_6601432 : Nat := 376634180441280122293397

theorem tailTrace_6601432 : CollatzResearch.WordTrace tailWord_6601432 prefixEnd_6601432 376634180441280122293397 := by
  unfold tailWord_6601432
  simp only [CollatzResearch.WordTrace]
  refine ⟨120387002710073386835519275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160516003613431182447359033 120387002710073386835519275)
  ·
    refine ⟨180580504065110080253278913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120387002710073386835519275 180580504065110080253278913)
    ·
      refine ⟨135435378048832560189959185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180580504065110080253278913 135435378048832560189959185)
      ·
        refine ⟨101576533536624420142469389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135435378048832560189959185 101576533536624420142469389)
        ·
          refine ⟨38091200076234157553426021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101576533536624420142469389 38091200076234157553426021)
          ·
            refine ⟨7142100014293904541267379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38091200076234157553426021 7142100014293904541267379)
            ·
              refine ⟨10713150021440856811901069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142100014293904541267379 10713150021440856811901069)
              ·
                refine ⟨4017431258040321304462901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10713150021440856811901069 4017431258040321304462901)
                ·
                  refine ⟨376634180441280122293397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017431258040321304462901 376634180441280122293397)
                  ·
                    rfl

theorem cell23_6601432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 5].length) (baseStart_6601432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601432 prefixEnd_6601432 := by exact prefixLift 6601432
  have htrace : WordTrace (prefixWord ++ tailWord_6601432) baseStart_6601432 baseEnd_6601432 := by
    simpa [prefixWord, tailWord_6601432, baseEnd_6601432] using wordTrace_append hprefix tailTrace_6601432
  have hstable : (prefixWord ++ tailWord_6601432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601432).length < 2 ^ (prefixWord ++ tailWord_6601432).sum := by decide
  have hdescent : baseEnd_6601432 < baseStart_6601432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601445 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_6601445 : Nat := 118140960795 + 6601445 * 2 ^ 59
def prefixEnd_6601445 : Nat := 4983230072969 + 3 ^ 40 * 6601445 * 2
def baseEnd_6601445 : Nat := 1129904766406676516592671

theorem tailTrace_6601445 : CollatzResearch.WordTrace tailWord_6601445 prefixEnd_6601445 1129904766406676516592671 := by
  unfold tailWord_6601445
  simp only [CollatzResearch.WordTrace]
  refine ⟨240774479569099676891261789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160516319712733117927507859 240774479569099676891261789)
  ·
    refine ⟨90290429838412378834223171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240774479569099676891261789 90290429838412378834223171)
    ·
      refine ⟨135435644757618568251334757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90290429838412378834223171 135435644757618568251334757)
      ·
        refine ⟨25394183392053481547125267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135435644757618568251334757 25394183392053481547125267)
        ·
          refine ⟨38091275088080222320687901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25394183392053481547125267 38091275088080222320687901)
          ·
            refine ⟨14284228158030083370257963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38091275088080222320687901 14284228158030083370257963)
            ·
              refine ⟨21426342237045125055386945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284228158030083370257963 21426342237045125055386945)
              ·
                refine ⟨16069756677783843791540209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21426342237045125055386945 16069756677783843791540209)
                ·
                  refine ⟨12052317508337882843655157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16069756677783843791540209 12052317508337882843655157)
                  ·
                    refine ⟨1129904766406676516592671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12052317508337882843655157 1129904766406676516592671)
                    ·
                      rfl

theorem cell23_6601445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_6601445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601445 prefixEnd_6601445 := by exact prefixLift 6601445
  have htrace : WordTrace (prefixWord ++ tailWord_6601445) baseStart_6601445 baseEnd_6601445 := by
    simpa [prefixWord, tailWord_6601445, baseEnd_6601445] using wordTrace_append hprefix tailTrace_6601445
  have hstable : (prefixWord ++ tailWord_6601445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601445).length < 2 ^ (prefixWord ++ tailWord_6601445).sum := by decide
  have hdescent : baseEnd_6601445 < baseStart_6601445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601465 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 2, 4, 2]
def baseStart_6601465 : Nat := 118140960795 + 6601465 * 2 ^ 59
def prefixEnd_6601465 : Nat := 4983230072969 + 3 ^ 40 * 6601465 * 2
def baseEnd_6601465 : Nat := 3389724568833119471527921

theorem tailTrace_6601465 : CollatzResearch.WordTrace tailWord_6601465 prefixEnd_6601465 3389724568833119471527921 := by
  unfold tailWord_6601465
  simp only [CollatzResearch.WordTrace]
  refine ⟨240775209029027220306989849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160516806019351480204659899 240775209029027220306989849)
  ·
    refine ⟨180581406771770415230242387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240775209029027220306989849 180581406771770415230242387)
    ·
      refine ⟨270872110157655622845363581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180581406771770415230242387 270872110157655622845363581)
      ·
        refine ⟨101577041309120858567011343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270872110157655622845363581 101577041309120858567011343)
        ·
          refine ⟨152365561963681287850517015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101577041309120858567011343 152365561963681287850517015)
          ·
            refine ⟨228548342945521931775775523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152365561963681287850517015 228548342945521931775775523)
            ·
              refine ⟨342822514418282897663663285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228548342945521931775775523 342822514418282897663663285)
              ·
                refine ⟨32139610726714021655968433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342822514418282897663663285 32139610726714021655968433)
                ·
                  refine ⟨24104708045035516241976325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32139610726714021655968433 24104708045035516241976325)
                  ·
                    refine ⟨4519632758444159295370561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24104708045035516241976325 4519632758444159295370561)
                    ·
                      refine ⟨3389724568833119471527921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519632758444159295370561 3389724568833119471527921)
                      ·
                        rfl

theorem cell23_6601465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_6601465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601465 prefixEnd_6601465 := by exact prefixLift 6601465
  have htrace : WordTrace (prefixWord ++ tailWord_6601465) baseStart_6601465 baseEnd_6601465 := by
    simpa [prefixWord, tailWord_6601465, baseEnd_6601465] using wordTrace_append hprefix tailTrace_6601465
  have hstable : (prefixWord ++ tailWord_6601465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601465).length < 2 ^ (prefixWord ++ tailWord_6601465).sum := by decide
  have hdescent : baseEnd_6601465 < baseStart_6601465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601505 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 6]
def baseStart_6601505 : Nat := 118140960795 + 6601505 * 2 ^ 59
def prefixEnd_6601505 : Nat := 4983230072969 + 3 ^ 40 * 6601505 * 2
def baseEnd_6601505 : Nat := 376638345339922146114193

theorem tailTrace_6601505 : CollatzResearch.WordTrace tailWord_6601505 prefixEnd_6601505 376638345339922146114193 := by
  unfold tailWord_6601505
  simp only [CollatzResearch.WordTrace]
  refine ⟨240776667948882307138445969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160517778632588204758963979 240776667948882307138445969)
  ·
    refine ⟨180582500961661730353834477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240776667948882307138445969 180582500961661730353834477)
    ·
      refine ⟨67718437860623148882687929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180582500961661730353834477 67718437860623148882687929)
      ·
        refine ⟨50788828395467361662015947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67718437860623148882687929 50788828395467361662015947)
        ·
          refine ⟨76183242593201042493023921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50788828395467361662015947 76183242593201042493023921)
          ·
            refine ⟨57137431944900781869767941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76183242593201042493023921 57137431944900781869767941)
            ·
              refine ⟨10713268489668896600581489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57137431944900781869767941 10713268489668896600581489)
              ·
                refine ⟨8034951367251672450436117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10713268489668896600581489 8034951367251672450436117)
                ·
                  refine ⟨376638345339922146114193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8034951367251672450436117 376638345339922146114193)
                  ·
                    rfl

theorem cell23_6601505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_6601505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601505 prefixEnd_6601505 := by exact prefixLift 6601505
  have htrace : WordTrace (prefixWord ++ tailWord_6601505) baseStart_6601505 baseEnd_6601505 := by
    simpa [prefixWord, tailWord_6601505, baseEnd_6601505] using wordTrace_append hprefix tailTrace_6601505
  have hstable : (prefixWord ++ tailWord_6601505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601505).length < 2 ^ (prefixWord ++ tailWord_6601505).sum := by decide
  have hdescent : baseEnd_6601505 < baseStart_6601505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601528 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6601528 : Nat := 118140960795 + 6601528 * 2 ^ 59
def prefixEnd_6601528 : Nat := 4983230072969 + 3 ^ 40 * 6601528 * 2
def baseEnd_6601528 : Nat := 3389756918114352725040131

theorem tailTrace_6601528 : CollatzResearch.WordTrace tailWord_6601528 prefixEnd_6601528 3389756918114352725040131 := by
  unfold tailWord_6601528
  simp only [CollatzResearch.WordTrace]
  refine ⟨120388753413899491033266619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160518337885199321377688825 120388753413899491033266619)
  ·
    refine ⟨180583130120849236549899929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120388753413899491033266619 180583130120849236549899929)
    ·
      refine ⟨135437347590636927412424947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180583130120849236549899929 135437347590636927412424947)
      ·
        refine ⟨203156021385955391118637421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135437347590636927412424947 203156021385955391118637421)
        ·
          refine ⟨76183508019733271669489033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203156021385955391118637421 76183508019733271669489033)
          ·
            refine ⟨57137631014799953752116775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76183508019733271669489033 57137631014799953752116775)
            ·
              refine ⟨85706446522199930628175163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57137631014799953752116775 85706446522199930628175163)
              ·
                refine ⟨128559669783299895942262745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85706446522199930628175163 128559669783299895942262745)
                ·
                  refine ⟨96419752337474921956697059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128559669783299895942262745 96419752337474921956697059)
                  ·
                    refine ⟨144629628506212382935045589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96419752337474921956697059 144629628506212382935045589)
                    ·
                      refine ⟨3389756918114352725040131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144629628506212382935045589 3389756918114352725040131)
                      ·
                        rfl

theorem cell23_6601528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6601528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601528 prefixEnd_6601528 := by exact prefixLift 6601528
  have htrace : WordTrace (prefixWord ++ tailWord_6601528) baseStart_6601528 baseEnd_6601528 := by
    simpa [prefixWord, tailWord_6601528, baseEnd_6601528] using wordTrace_append hprefix tailTrace_6601528
  have hstable : (prefixWord ++ tailWord_6601528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601528).length < 2 ^ (prefixWord ++ tailWord_6601528).sum := by decide
  have hdescent : baseEnd_6601528 < baseStart_6601528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601535 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 3, 5]
def baseStart_6601535 : Nat := 118140960795 + 6601535 * 2 ^ 59
def prefixEnd_6601535 : Nat := 4983230072969 + 3 ^ 40 * 6601535 * 2
def baseEnd_6601535 : Nat := 1129920170826311399217533

theorem tailTrace_6601535 : CollatzResearch.WordTrace tailWord_6601535 prefixEnd_6601535 1129920170826311399217533 := by
  unfold tailWord_6601535
  simp only [CollatzResearch.WordTrace]
  refine ⟨240777762138773622262038059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160518508092515748174692039 240777762138773622262038059)
  ·
    refine ⟨361166643208160433393057089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240777762138773622262038059 361166643208160433393057089)
    ·
      refine ⟨270874982406120325044792817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361166643208160433393057089 270874982406120325044792817)
      ·
        refine ⟨203156236804590243783594613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270874982406120325044792817 203156236804590243783594613)
        ·
          refine ⟨19045897200430335354711995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203156236804590243783594613 19045897200430335354711995)
          ·
            refine ⟨28568845800645503032067993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19045897200430335354711995 28568845800645503032067993)
            ·
              refine ⟨21426634350484127274050995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28568845800645503032067993 21426634350484127274050995)
              ·
                refine ⟨32139951525726190911076493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21426634350484127274050995 32139951525726190911076493)
                ·
                  refine ⟨12052481822147321591653685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32139951525726190911076493 12052481822147321591653685)
                  ·
                    refine ⟨1129920170826311399217533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12052481822147321591653685 1129920170826311399217533)
                    ·
                      rfl

theorem cell23_6601535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_6601535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601535 prefixEnd_6601535 := by exact prefixLift 6601535
  have htrace : WordTrace (prefixWord ++ tailWord_6601535) baseStart_6601535 baseEnd_6601535 := by
    simpa [prefixWord, tailWord_6601535, baseEnd_6601535] using wordTrace_append hprefix tailTrace_6601535
  have hstable : (prefixWord ++ tailWord_6601535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601535).length < 2 ^ (prefixWord ++ tailWord_6601535).sum := by decide
  have hdescent : baseEnd_6601535 < baseStart_6601535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601552 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_6601552 : Nat := 118140960795 + 6601552 * 2 ^ 59
def prefixEnd_6601552 : Nat := 4983230072969 + 3 ^ 40 * 6601552 * 2
def baseEnd_6601552 : Nat := 1129923080550020210380007

theorem tailTrace_6601552 : CollatzResearch.WordTrace tailWord_6601552 prefixEnd_6601552 1129923080550020210380007 := by
  unfold tailWord_6601552
  simp only [CollatzResearch.WordTrace]
  refine ⟨120389191089856017082703455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160518921453141356110271273 120389191089856017082703455)
  ·
    refine ⟨180583786634784025624055183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120389191089856017082703455 180583786634784025624055183)
    ·
      refine ⟨270875679952176038436082775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180583786634784025624055183 270875679952176038436082775)
      ·
        refine ⟨406313519928264057654124163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270875679952176038436082775 406313519928264057654124163)
        ·
          refine ⟨609470279892396086481186245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406313519928264057654124163 609470279892396086481186245)
          ·
            refine ⟨114275677479824266215222421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609470279892396086481186245 114275677479824266215222421)
            ·
              refine ⟨5356672381866762478838551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114275677479824266215222421 5356672381866762478838551)
              ·
                refine ⟨8035008572800143718257827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356672381866762478838551 8035008572800143718257827)
                ·
                  refine ⟨12052512859200215577386741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035008572800143718257827 12052512859200215577386741)
                  ·
                    refine ⟨1129923080550020210380007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12052512859200215577386741 1129923080550020210380007)
                    ·
                      rfl

theorem cell23_6601552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_6601552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601552 prefixEnd_6601552 := by exact prefixLift 6601552
  have htrace : WordTrace (prefixWord ++ tailWord_6601552) baseStart_6601552 baseEnd_6601552 := by
    simpa [prefixWord, tailWord_6601552, baseEnd_6601552] using wordTrace_append hprefix tailTrace_6601552
  have hstable : (prefixWord ++ tailWord_6601552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601552).length < 2 ^ (prefixWord ++ tailWord_6601552).sum := by decide
  have hdescent : baseEnd_6601552 < baseStart_6601552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601555 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 1, 8, 2]
def baseStart_6601555 : Nat := 118140960795 + 6601555 * 2 ^ 59
def prefixEnd_6601555 : Nat := 4983230072969 + 3 ^ 40 * 6601555 * 2
def baseEnd_6601555 : Nat := 3389770782092024119402507

theorem tailTrace_6601555 : CollatzResearch.WordTrace tailWord_6601555 prefixEnd_6601555 3389770782092024119402507 := by
  unfold tailWord_6601555
  simp only [CollatzResearch.WordTrace]
  refine ⟨240778491598701165677766119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160518994399134110451844079 240778491598701165677766119)
  ·
    refine ⟨361167737398051748516649179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240778491598701165677766119 361167737398051748516649179)
    ·
      refine ⟨541751606097077622774973769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361167737398051748516649179 541751606097077622774973769)
      ·
        refine ⟨406313704572808217081230327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541751606097077622774973769 406313704572808217081230327)
        ·
          refine ⟨609470556859212325621845491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406313704572808217081230327 609470556859212325621845491)
          ·
            refine ⟨914205835288818488432768237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609470556859212325621845491 914205835288818488432768237)
            ·
              refine ⟨342827188233306933162288089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914205835288818488432768237 342827188233306933162288089)
              ·
                refine ⟨257120391174980199871716067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342827188233306933162288089 257120391174980199871716067)
                ·
                  refine ⟨385680586762470299807574101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257120391174980199871716067 385680586762470299807574101)
                  ·
                    refine ⟨4519694376122698825870009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 385680586762470299807574101 4519694376122698825870009)
                    ·
                      refine ⟨3389770782092024119402507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519694376122698825870009 3389770782092024119402507)
                      ·
                        rfl

theorem cell23_6601555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 8, 2].length) (baseStart_6601555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601555 prefixEnd_6601555 := by exact prefixLift 6601555
  have htrace : WordTrace (prefixWord ++ tailWord_6601555) baseStart_6601555 baseEnd_6601555 := by
    simpa [prefixWord, tailWord_6601555, baseEnd_6601555] using wordTrace_append hprefix tailTrace_6601555
  have hstable : (prefixWord ++ tailWord_6601555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601555).length < 2 ^ (prefixWord ++ tailWord_6601555).sum := by decide
  have hdescent : baseEnd_6601555 < baseStart_6601555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601575 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6601575 : Nat := 118140960795 + 6601575 * 2 ^ 59
def prefixEnd_6601575 : Nat := 4983230072969 + 3 ^ 40 * 6601575 * 2
def baseEnd_6601575 : Nat := 3389781051705114041152415

theorem tailTrace_6601575 : CollatzResearch.WordTrace tailWord_6601575 prefixEnd_6601575 3389781051705114041152415 := by
  unfold tailWord_6601575
  simp only [CollatzResearch.WordTrace]
  refine ⟨240779221058628709093494179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160519480705752472728996119 240779221058628709093494179)
  ·
    refine ⟨361168831587943063640241269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240779221058628709093494179 361168831587943063640241269)
    ·
      refine ⟨33859577961369662216272619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361168831587943063640241269 33859577961369662216272619)
      ·
        refine ⟨50789366942054493324408929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33859577961369662216272619 50789366942054493324408929)
        ·
          refine ⟨38092025206540869993306697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50789366942054493324408929 38092025206540869993306697)
          ·
            refine ⟨28569018904905652494980023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38092025206540869993306697 28569018904905652494980023)
            ·
              refine ⟨42853528357358478742470035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28569018904905652494980023 42853528357358478742470035)
              ·
                refine ⟨64280292536037718113705053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42853528357358478742470035 64280292536037718113705053)
                ·
                  refine ⟨24105109701014144292639395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64280292536037718113705053 24105109701014144292639395)
                  ·
                    refine ⟨36157664551521216438959093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24105109701014144292639395 36157664551521216438959093)
                    ·
                      refine ⟨3389781051705114041152415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36157664551521216438959093 3389781051705114041152415)
                      ·
                        rfl

theorem cell23_6601575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6601575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601575 prefixEnd_6601575 := by exact prefixLift 6601575
  have htrace : WordTrace (prefixWord ++ tailWord_6601575) baseStart_6601575 baseEnd_6601575 := by
    simpa [prefixWord, tailWord_6601575, baseEnd_6601575] using wordTrace_append hprefix tailTrace_6601575
  have hstable : (prefixWord ++ tailWord_6601575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601575).length < 2 ^ (prefixWord ++ tailWord_6601575).sum := by decide
  have hdescent : baseEnd_6601575 < baseStart_6601575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601585 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_6601585 : Nat := 118140960795 + 6601585 * 2 ^ 59
def prefixEnd_6601585 : Nat := 4983230072969 + 3 ^ 40 * 6601585 * 2
def baseEnd_6601585 : Nat := 3389786186511659002027369

theorem tailTrace_6601585 : CollatzResearch.WordTrace tailWord_6601585 prefixEnd_6601585 3389786186511659002027369 := by
  unfold tailWord_6601585
  simp only [CollatzResearch.WordTrace]
  refine ⟨240779585788592480801358209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160519723859061653867572139 240779585788592480801358209)
  ·
    refine ⟨180584689341444360601018657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240779585788592480801358209 180584689341444360601018657)
    ·
      refine ⟨135438517006083270450763993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180584689341444360601018657 135438517006083270450763993)
      ·
        refine ⟨101578887754562452838072995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135438517006083270450763993 101578887754562452838072995)
        ·
          refine ⟨152368331631843679257109493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101578887754562452838072995 152368331631843679257109493)
          ·
            refine ⟨14284531090485344930354015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152368331631843679257109493 14284531090485344930354015)
            ·
              refine ⟨21426796635728017395531023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284531090485344930354015 21426796635728017395531023)
              ·
                refine ⟨32140194953592026093296535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21426796635728017395531023 32140194953592026093296535)
                ·
                  refine ⟨48210292430388039139944803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32140194953592026093296535 48210292430388039139944803)
                  ·
                    refine ⟨72315438645582058709917205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48210292430388039139944803 72315438645582058709917205)
                    ·
                      refine ⟨3389786186511659002027369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72315438645582058709917205 3389786186511659002027369)
                      ·
                        rfl

theorem cell23_6601585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_6601585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601585 prefixEnd_6601585 := by exact prefixLift 6601585
  have htrace : WordTrace (prefixWord ++ tailWord_6601585) baseStart_6601585 baseEnd_6601585 := by
    simpa [prefixWord, tailWord_6601585, baseEnd_6601585] using wordTrace_append hprefix tailTrace_6601585
  have hstable : (prefixWord ++ tailWord_6601585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601585).length < 2 ^ (prefixWord ++ tailWord_6601585).sum := by decide
  have hdescent : baseEnd_6601585 < baseStart_6601585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601589 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6601589 : Nat := 118140960795 + 6601589 * 2 ^ 59
def prefixEnd_6601589 : Nat := 4983230072969 + 3 ^ 40 * 6601589 * 2
def baseEnd_6601589 : Nat := 3389788240434276986377351

theorem tailTrace_6601589 : CollatzResearch.WordTrace tailWord_6601589 prefixEnd_6601589 3389788240434276986377351 := by
  unfold tailWord_6601589
  simp only [CollatzResearch.WordTrace]
  refine ⟨240779731680577989484503821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160519821120385326323002547 240779731680577989484503821)
  ·
    refine ⟨90292399380216746056688933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240779731680577989484503821 90292399380216746056688933)
    ·
      refine ⟨16929824883790639885629175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90292399380216746056688933 16929824883790639885629175)
      ·
        refine ⟨25394737325685959828443763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16929824883790639885629175 25394737325685959828443763)
        ·
          refine ⟨38092105988528939742665645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25394737325685959828443763 38092105988528939742665645)
          ·
            refine ⟨14284539745698352403499617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38092105988528939742665645 14284539745698352403499617)
            ·
              refine ⟨10713404809273764302624713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14284539745698352403499617 10713404809273764302624713)
              ·
                refine ⟨8035053606955323226968535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10713404809273764302624713 8035053606955323226968535)
                ·
                  refine ⟨12052580410432984840452803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035053606955323226968535 12052580410432984840452803)
                  ·
                    refine ⟨18078870615649477260679205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12052580410432984840452803 18078870615649477260679205)
                    ·
                      refine ⟨3389788240434276986377351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18078870615649477260679205 3389788240434276986377351)
                      ·
                        rfl

theorem cell23_6601589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6601589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601589 prefixEnd_6601589 := by exact prefixLift 6601589
  have htrace : WordTrace (prefixWord ++ tailWord_6601589) baseStart_6601589 baseEnd_6601589 := by
    simpa [prefixWord, tailWord_6601589, baseEnd_6601589] using wordTrace_append hprefix tailTrace_6601589
  have hstable : (prefixWord ++ tailWord_6601589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601589).length < 2 ^ (prefixWord ++ tailWord_6601589).sum := by decide
  have hdescent : baseEnd_6601589 < baseStart_6601589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601595 : List Nat := [1, 1, 1, 1, 1, 5, 6, 7]
def baseStart_6601595 : Nat := 118140960795 + 6601595 * 2 ^ 59
def prefixEnd_6601595 : Nat := 4983230072969 + 3 ^ 40 * 6601595 * 2
def baseEnd_6601595 : Nat := 125547826715489035663049

theorem tailTrace_6601595 : CollatzResearch.WordTrace tailWord_6601595 prefixEnd_6601595 125547826715489035663049 := by
  unfold tailWord_6601595
  simp only [CollatzResearch.WordTrace]
  refine ⟨240779950518556252509222239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160519967012370835006148159 240779950518556252509222239)
  ·
    refine ⟨361169925777834378763833359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240779950518556252509222239 361169925777834378763833359)
    ·
      refine ⟨541754888666751568145750039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361169925777834378763833359 541754888666751568145750039)
      ·
        refine ⟨812632333000127352218625059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541754888666751568145750039 812632333000127352218625059)
        ·
          refine ⟨1218948499500191028327937589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812632333000127352218625059 1218948499500191028327937589)
          ·
            refine ⟨114276421828142908905744149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1218948499500191028327937589 114276421828142908905744149)
            ·
              refine ⟨5356707273194198854956757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114276421828142908905744149 5356707273194198854956757)
              ·
                refine ⟨125547826715489035663049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5356707273194198854956757 125547826715489035663049)
                ·
                  rfl

theorem cell23_6601595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 7].length) (baseStart_6601595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601595 prefixEnd_6601595 := by exact prefixLift 6601595
  have htrace : WordTrace (prefixWord ++ tailWord_6601595) baseStart_6601595 baseEnd_6601595 := by
    simpa [prefixWord, tailWord_6601595, baseEnd_6601595] using wordTrace_append hprefix tailTrace_6601595
  have hstable : (prefixWord ++ tailWord_6601595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601595).length < 2 ^ (prefixWord ++ tailWord_6601595).sum := by decide
  have hdescent : baseEnd_6601595 < baseStart_6601595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601623 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_6601623 : Nat := 118140960795 + 6601623 * 2 ^ 59
def prefixEnd_6601623 : Nat := 4983230072969 + 3 ^ 40 * 6601623 * 2
def baseEnd_6601623 : Nat := 3389805698776529853352195

theorem tailTrace_6601623 : CollatzResearch.WordTrace tailWord_6601623 prefixEnd_6601623 3389805698776529853352195 := by
  unfold tailWord_6601623
  simp only [CollatzResearch.WordTrace]
  refine ⟨240780971762454813291241523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160520647841636542194161015 240780971762454813291241523)
  ·
    refine ⟨361171457643682219936862285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240780971762454813291241523 361171457643682219936862285)
    ·
      refine ⟨135439296616380832476323357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361171457643682219936862285 135439296616380832476323357)
      ·
        refine ⟨50789736231142812178621259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135439296616380832476323357 50789736231142812178621259)
        ·
          refine ⟨76184604346714218267931889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50789736231142812178621259 76184604346714218267931889)
          ·
            refine ⟨57138453260035663700948917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76184604346714218267931889 57138453260035663700948917)
            ·
              refine ⟨5356729993128343471963961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57138453260035663700948917 5356729993128343471963961)
              ·
                refine ⟨4017547494846257603972971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356729993128343471963961 4017547494846257603972971)
                ·
                  refine ⟨6026321242269386405959457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017547494846257603972971 6026321242269386405959457)
                  ·
                    refine ⟨4519740931702039804469593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6026321242269386405959457 4519740931702039804469593)
                    ·
                      refine ⟨3389805698776529853352195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519740931702039804469593 3389805698776529853352195)
                      ·
                        rfl

theorem cell23_6601623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_6601623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601623 prefixEnd_6601623 := by exact prefixLift 6601623
  have htrace : WordTrace (prefixWord ++ tailWord_6601623) baseStart_6601623 baseEnd_6601623 := by
    simpa [prefixWord, tailWord_6601623, baseEnd_6601623] using wordTrace_append hprefix tailTrace_6601623
  have hstable : (prefixWord ++ tailWord_6601623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601623).length < 2 ^ (prefixWord ++ tailWord_6601623).sum := by decide
  have hdescent : baseEnd_6601623 < baseStart_6601623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601717 : List Nat := [1, 3, 5, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6601717 : Nat := 118140960795 + 6601717 * 2 ^ 59
def prefixEnd_6601717 : Nat := 4983230072969 + 3 ^ 40 * 6601717 * 2
def baseEnd_6601717 : Nat := 3389853965958052485576763

theorem tailTrace_6601717 : CollatzResearch.WordTrace tailWord_6601717 prefixEnd_6601717 3389853965958052485576763 := by
  unfold tailWord_6601717
  simp only [CollatzResearch.WordTrace]
  refine ⟨240784400224114267345163405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160522933482742844896775603 240784400224114267345163405)
  ·
    refine ⟨90294150084042850254436277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240784400224114267345163405 90294150084042850254436277)
    ·
      refine ⟨8465076570379017211353401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90294150084042850254436277 8465076570379017211353401)
      ·
        refine ⟨6348807427784262908515051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8465076570379017211353401 6348807427784262908515051)
        ·
          refine ⟨9523211141676394362772577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348807427784262908515051 9523211141676394362772577)
          ·
            refine ⟨7142408356257295772079433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9523211141676394362772577 7142408356257295772079433)
            ·
              refine ⟨5356806267192971829059575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142408356257295772079433 5356806267192971829059575)
              ·
                refine ⟨8035209400789457743589363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356806267192971829059575 8035209400789457743589363)
                ·
                  refine ⟨12052814101184186615384045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035209400789457743589363 12052814101184186615384045)
                  ·
                    refine ⟨4519805287944069980769017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12052814101184186615384045 4519805287944069980769017)
                    ·
                      refine ⟨3389853965958052485576763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519805287944069980769017 3389853965958052485576763)
                      ·
                        rfl

theorem cell23_6601717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6601717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601717 prefixEnd_6601717 := by exact prefixLift 6601717
  have htrace : WordTrace (prefixWord ++ tailWord_6601717) baseStart_6601717 baseEnd_6601717 := by
    simpa [prefixWord, tailWord_6601717, baseEnd_6601717] using wordTrace_append hprefix tailTrace_6601717
  have hstable : (prefixWord ++ tailWord_6601717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601717).length < 2 ^ (prefixWord ++ tailWord_6601717).sum := by decide
  have hdescent : baseEnd_6601717 < baseStart_6601717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601730 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6601730 : Nat := 118140960795 + 6601730 * 2 ^ 59
def prefixEnd_6601730 : Nat := 4983230072969 + 3 ^ 40 * 6601730 * 2
def baseEnd_6601730 : Nat := 3389860641206560934714203

theorem tailTrace_6601730 : CollatzResearch.WordTrace tailWord_6601730 prefixEnd_6601730 3389860641206560934714203 := by
  unfold tailWord_6601730
  simp only [CollatzResearch.WordTrace]
  refine ⟨60196218593266792641346661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160523249582044780376924429 60196218593266792641346661)
  ·
    refine ⟨11286790986237523620252499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60196218593266792641346661 11286790986237523620252499)
    ·
      refine ⟨16930186479356285430378749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286790986237523620252499 16930186479356285430378749)
      ·
        refine ⟨6348819929758607036392031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16930186479356285430378749 6348819929758607036392031)
        ·
          refine ⟨9523229894637910554588047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348819929758607036392031 9523229894637910554588047)
          ·
            refine ⟨14284844841956865831882071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9523229894637910554588047 14284844841956865831882071)
            ·
              refine ⟨21427267262935298747823107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14284844841956865831882071 21427267262935298747823107)
              ·
                refine ⟨32140900894402948121734661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21427267262935298747823107 32140900894402948121734661)
                ·
                  refine ⟨6026418917700552772825249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32140900894402948121734661 6026418917700552772825249)
                  ·
                    refine ⟨4519814188275414579618937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6026418917700552772825249 4519814188275414579618937)
                    ·
                      refine ⟨3389860641206560934714203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519814188275414579618937 3389860641206560934714203)
                      ·
                        rfl

theorem cell23_6601730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6601730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601730 prefixEnd_6601730 := by exact prefixLift 6601730
  have htrace : WordTrace (prefixWord ++ tailWord_6601730) baseStart_6601730 baseEnd_6601730 := by
    simpa [prefixWord, tailWord_6601730, baseEnd_6601730] using wordTrace_append hprefix tailTrace_6601730
  have hstable : (prefixWord ++ tailWord_6601730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601730).length < 2 ^ (prefixWord ++ tailWord_6601730).sum := by decide
  have hdescent : baseEnd_6601730 < baseStart_6601730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601752 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6601752 : Nat := 118140960795 + 6601752 * 2 ^ 59
def prefixEnd_6601752 : Nat := 4983230072969 + 3 ^ 40 * 6601752 * 2
def baseEnd_6601752 : Nat := 3389871937780959848639101

theorem tailTrace_6601752 : CollatzResearch.WordTrace tailWord_6601752 prefixEnd_6601752 3389871937780959848639101 := by
  unfold tailWord_6601752
  simp only [CollatzResearch.WordTrace]
  refine ⟨120392838389493734161343755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160523784519324978881791673 120392838389493734161343755)
  ·
    refine ⟨180589257584240601242015633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120392838389493734161343755 180589257584240601242015633)
    ·
      refine ⟨135441943188180450931511725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180589257584240601242015633 135441943188180450931511725)
      ·
        refine ⟨50790728695567669099316897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135441943188180450931511725 50790728695567669099316897)
        ·
          refine ⟨38093046521675751824487673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50790728695567669099316897 38093046521675751824487673)
          ·
            refine ⟨28569784891256813868365755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38093046521675751824487673 28569784891256813868365755)
            ·
              refine ⟨42854677336885220802548633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28569784891256813868365755 42854677336885220802548633)
              ·
                refine ⟨32141008002663915601911475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42854677336885220802548633 32141008002663915601911475)
                ·
                  refine ⟨48211512003995873402867213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32141008002663915601911475 48211512003995873402867213)
                  ·
                    refine ⟨18079317001498452526075205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48211512003995873402867213 18079317001498452526075205)
                    ·
                      refine ⟨3389871937780959848639101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18079317001498452526075205 3389871937780959848639101)
                      ·
                        rfl

theorem cell23_6601752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6601752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601752 prefixEnd_6601752 := by exact prefixLift 6601752
  have htrace : WordTrace (prefixWord ++ tailWord_6601752) baseStart_6601752 baseEnd_6601752 := by
    simpa [prefixWord, tailWord_6601752, baseEnd_6601752] using wordTrace_append hprefix tailTrace_6601752
  have hstable : (prefixWord ++ tailWord_6601752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601752).length < 2 ^ (prefixWord ++ tailWord_6601752).sum := by decide
  have hdescent : baseEnd_6601752 < baseStart_6601752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601755 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_6601755 : Nat := 118140960795 + 6601755 * 2 ^ 59
def prefixEnd_6601755 : Nat := 4983230072969 + 3 ^ 40 * 6601755 * 2
def baseEnd_6601755 : Nat := 3389873478222923336901587

theorem tailTrace_6601755 : CollatzResearch.WordTrace tailWord_6601755 prefixEnd_6601755 3389873478222923336901587 := by
  unfold tailWord_6601755
  simp only [CollatzResearch.WordTrace]
  refine ⟨240785786197976599835046719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160523857465317733223364479 240785786197976599835046719)
  ·
    refine ⟨361178679296964899752570079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240785786197976599835046719 361178679296964899752570079)
    ·
      refine ⟨541768018945447349628855119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361178679296964899752570079 541768018945447349628855119)
      ·
        refine ⟨812652028418171024443282679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541768018945447349628855119 812652028418171024443282679)
        ·
          refine ⟨1218978042627256536664924019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812652028418171024443282679 1218978042627256536664924019)
          ·
            refine ⟨1828467063940884804997386029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218978042627256536664924019 1828467063940884804997386029)
            ·
              refine ⟨685675148977831801874019761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828467063940884804997386029 685675148977831801874019761)
              ·
                refine ⟨514256361733373851405514821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685675148977831801874019761 514256361733373851405514821)
                ·
                  refine ⟨96423067825007597138534029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 514256361733373851405514821 96423067825007597138534029)
                  ·
                    refine ⟨36158650434377848926950261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96423067825007597138534029 36158650434377848926950261)
                    ·
                      refine ⟨3389873478222923336901587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36158650434377848926950261 3389873478222923336901587)
                      ·
                        rfl

theorem cell23_6601755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_6601755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601755 prefixEnd_6601755 := by exact prefixLift 6601755
  have htrace : WordTrace (prefixWord ++ tailWord_6601755) baseStart_6601755 baseEnd_6601755 := by
    simpa [prefixWord, tailWord_6601755, baseEnd_6601755] using wordTrace_append hprefix tailTrace_6601755
  have hstable : (prefixWord ++ tailWord_6601755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601755).length < 2 ^ (prefixWord ++ tailWord_6601755).sum := by decide
  have hdescent : baseEnd_6601755 < baseStart_6601755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601772 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_6601772 : Nat := 118140960795 + 6601772 * 2 ^ 59
def prefixEnd_6601772 : Nat := 4983230072969 + 3 ^ 40 * 6601772 * 2
def baseEnd_6601772 : Nat := 3389882207394049770389009

theorem tailTrace_6601772 : CollatzResearch.WordTrace tailWord_6601772 prefixEnd_6601772 3389882207394049770389009 := by
  unfold tailWord_6601772
  simp only [CollatzResearch.WordTrace]
  refine ⟨120393203119457505869207785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160524270825943341158943713 120393203119457505869207785)
  ·
    refine ⟨90294902339593129401905839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120393203119457505869207785 90294902339593129401905839)
    ·
      refine ⟨135442353509389694102858759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90294902339593129401905839 135442353509389694102858759)
      ·
        refine ⟨203163530264084541154288139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135442353509389694102858759 203163530264084541154288139)
        ·
          refine ⟨304745295396126811731432209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203163530264084541154288139 304745295396126811731432209)
          ·
            refine ⟨228558971547095108798574157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304745295396126811731432209 228558971547095108798574157)
            ·
              refine ⟨85709614330160665799465309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228558971547095108798574157 85709614330160665799465309)
              ·
                refine ⟨32141105373810249674799491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85709614330160665799465309 32141105373810249674799491)
                ·
                  refine ⟨48211658060715374512199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32141105373810249674799491 48211658060715374512199237)
                  ·
                    refine ⟨9039685886384132721037357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48211658060715374512199237 9039685886384132721037357)
                    ·
                      refine ⟨3389882207394049770389009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039685886384132721037357 3389882207394049770389009)
                      ·
                        rfl

theorem cell23_6601772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_6601772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601772 prefixEnd_6601772 := by exact prefixLift 6601772
  have htrace : WordTrace (prefixWord ++ tailWord_6601772) baseStart_6601772 baseEnd_6601772 := by
    simpa [prefixWord, tailWord_6601772, baseEnd_6601772] using wordTrace_append hprefix tailTrace_6601772
  have hstable : (prefixWord ++ tailWord_6601772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601772).length < 2 ^ (prefixWord ++ tailWord_6601772).sum := by decide
  have hdescent : baseEnd_6601772 < baseStart_6601772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601789 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6601789 : Nat := 118140960795 + 6601789 * 2 ^ 59
def prefixEnd_6601789 : Nat := 4983230072969 + 3 ^ 40 * 6601789 * 2
def baseEnd_6601789 : Nat := 3389890936565176203876431

theorem tailTrace_6601789 : CollatzResearch.WordTrace tailWord_6601789 prefixEnd_6601789 3389890936565176203876431 := by
  unfold tailWord_6601789
  simp only [CollatzResearch.WordTrace]
  refine ⟨240787026279853423641784421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160524684186568949094522947 240787026279853423641784421)
  ·
    refine ⟨45147567427472516932834579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240787026279853423641784421 45147567427472516932834579)
    ·
      refine ⟨67721351141208775399251869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45147567427472516932834579 67721351141208775399251869)
      ·
        refine ⟨25395506677953290774719451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67721351141208775399251869 25395506677953290774719451)
        ·
          refine ⟨38093260016929936162079177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25395506677953290774719451 38093260016929936162079177)
          ·
            refine ⟨28569945012697452121559383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38093260016929936162079177 28569945012697452121559383)
            ·
              refine ⟨42854917519046178182339075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28569945012697452121559383 42854917519046178182339075)
              ·
                refine ⟨64282376278569267273508613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42854917519046178182339075 64282376278569267273508613)
                ·
                  refine ⟨12052945552231737613782865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64282376278569267273508613 12052945552231737613782865)
                  ·
                    refine ⟨9039709164173803210337149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12052945552231737613782865 9039709164173803210337149)
                    ·
                      refine ⟨3389890936565176203876431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039709164173803210337149 3389890936565176203876431)
                      ·
                        rfl

theorem cell23_6601789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6601789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601789 prefixEnd_6601789 := by exact prefixLift 6601789
  have htrace : WordTrace (prefixWord ++ tailWord_6601789) baseStart_6601789 baseEnd_6601789 := by
    simpa [prefixWord, tailWord_6601789, baseEnd_6601789] using wordTrace_append hprefix tailTrace_6601789
  have hstable : (prefixWord ++ tailWord_6601789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601789).length < 2 ^ (prefixWord ++ tailWord_6601789).sum := by decide
  have hdescent : baseEnd_6601789 < baseStart_6601789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601792 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 6]
def baseStart_6601792 : Nat := 118140960795 + 6601792 * 2 ^ 59
def prefixEnd_6601792 : Nat := 4983230072969 + 3 ^ 40 * 6601792 * 2
def baseEnd_6601792 : Nat := 376654719667459965793213

theorem tailTrace_6601792 : CollatzResearch.WordTrace tailWord_6601792 prefixEnd_6601792 376654719667459965793213 := by
  unfold tailWord_6601792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120393567849421277577071815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160524757132561703436095753 120393567849421277577071815)
  ·
    refine ⟨180590351774131916365607723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120393567849421277577071815 180590351774131916365607723)
    ·
      refine ⟨270885527661197874548411585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180590351774131916365607723 270885527661197874548411585)
      ·
        refine ⟨203164145745898405911308689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270885527661197874548411585 203164145745898405911308689)
        ·
          refine ⟨152373109309423804433481517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203164145745898405911308689 152373109309423804433481517)
          ·
            refine ⟨57139915991033926662555569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152373109309423804433481517 57139915991033926662555569)
            ·
              refine ⟨42854936993275444996916677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57139915991033926662555569 42854936993275444996916677)
              ·
                refine ⟨8035300686239145936921877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42854936993275444996916677 8035300686239145936921877)
                ·
                  refine ⟨376654719667459965793213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8035300686239145936921877 376654719667459965793213)
                  ·
                    rfl

theorem cell23_6601792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_6601792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601792 prefixEnd_6601792 := by exact prefixLift 6601792
  have htrace : WordTrace (prefixWord ++ tailWord_6601792) baseStart_6601792 baseEnd_6601792 := by
    simpa [prefixWord, tailWord_6601792, baseEnd_6601792] using wordTrace_append hprefix tailTrace_6601792
  have hstable : (prefixWord ++ tailWord_6601792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601792).length < 2 ^ (prefixWord ++ tailWord_6601792).sum := by decide
  have hdescent : baseEnd_6601792 < baseStart_6601792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601809 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 6]
def baseStart_6601809 : Nat := 118140960795 + 6601809 * 2 ^ 59
def prefixEnd_6601809 : Nat := 4983230072969 + 3 ^ 40 * 6601809 * 2
def baseEnd_6601809 : Nat := 376655689575362902847371

theorem tailTrace_6601809 : CollatzResearch.WordTrace tailWord_6601809 prefixEnd_6601809 376655689575362902847371 := by
  unfold tailWord_6601809
  simp only [CollatzResearch.WordTrace]
  refine ⟨240787755739780967057512481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160525170493187311371674987 240787755739780967057512481)
  ·
    refine ⟨180590816804835725293134361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240787755739780967057512481 180590816804835725293134361)
    ·
      refine ⟨135443112603626793969850771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180590816804835725293134361 135443112603626793969850771)
      ·
        refine ⟨203164668905440190954776157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135443112603626793969850771 203164668905440190954776157)
        ·
          refine ⟨76186750839540071608041059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203164668905440190954776157 76186750839540071608041059)
          ·
            refine ⟨114280126259310107412061589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76186750839540071608041059 114280126259310107412061589)
            ·
              refine ⟨5356880918405161284940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114280126259310107412061589 5356880918405161284940387)
              ·
                refine ⟨8035321377607741927410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356880918405161284940387 8035321377607741927410581)
                ·
                  refine ⟨376655689575362902847371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8035321377607741927410581 376655689575362902847371)
                  ·
                    rfl

theorem cell23_6601809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_6601809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601809 prefixEnd_6601809 := by exact prefixLift 6601809
  have htrace : WordTrace (prefixWord ++ tailWord_6601809) baseStart_6601809 baseEnd_6601809 := by
    simpa [prefixWord, tailWord_6601809, baseEnd_6601809] using wordTrace_append hprefix tailTrace_6601809
  have hstable : (prefixWord ++ tailWord_6601809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601809).length < 2 ^ (prefixWord ++ tailWord_6601809).sum := by decide
  have hdescent : baseEnd_6601809 < baseStart_6601809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601812 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6601812 : Nat := 118140960795 + 6601812 * 2 ^ 59
def prefixEnd_6601812 : Nat := 4983230072969 + 3 ^ 40 * 6601812 * 2
def baseEnd_6601812 : Nat := 3389902746620229613888825

theorem tailTrace_6601812 : CollatzResearch.WordTrace tailWord_6601812 prefixEnd_6601812 3389902746620229613888825 := by
  unfold tailWord_6601812
  simp only [CollatzResearch.WordTrace]
  refine ⟨120393932579385049284935845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160525243439180065713247793 120393932579385049284935845)
  ·
    refine ⟨22573862358634696740925471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120393932579385049284935845 22573862358634696740925471)
    ·
      refine ⟨33860793537952045111388207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22573862358634696740925471 33860793537952045111388207)
      ·
        refine ⟨50791190306928067667082311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33860793537952045111388207 50791190306928067667082311)
        ·
          refine ⟨76186785460392101500623467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50791190306928067667082311 76186785460392101500623467)
          ·
            refine ⟨114280178190588152250935201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76186785460392101500623467 114280178190588152250935201)
            ·
              refine ⟨85710133642941114188201401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114280178190588152250935201 85710133642941114188201401)
              ·
                refine ⟨64282600232205835641151051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85710133642941114188201401 64282600232205835641151051)
                ·
                  refine ⟨96423900348308753461726577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64282600232205835641151051 96423900348308753461726577)
                  ·
                    refine ⟨72317925261231565096294933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96423900348308753461726577 72317925261231565096294933)
                    ·
                      refine ⟨3389902746620229613888825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72317925261231565096294933 3389902746620229613888825)
                      ·
                        rfl

theorem cell23_6601812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6601812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601812 prefixEnd_6601812 := by exact prefixLift 6601812
  have htrace : WordTrace (prefixWord ++ tailWord_6601812) baseStart_6601812 baseEnd_6601812 := by
    simpa [prefixWord, tailWord_6601812, baseEnd_6601812] using wordTrace_append hprefix tailTrace_6601812
  have hstable : (prefixWord ++ tailWord_6601812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601812).length < 2 ^ (prefixWord ++ tailWord_6601812).sum := by decide
  have hdescent : baseEnd_6601812 < baseStart_6601812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601852 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6601852 : Nat := 118140960795 + 6601852 * 2 ^ 59
def prefixEnd_6601852 : Nat := 4983230072969 + 3 ^ 40 * 6601852 * 2
def baseEnd_6601852 : Nat := 1129974428615469819129547

theorem tailTrace_6601852 : CollatzResearch.WordTrace tailWord_6601852 prefixEnd_6601852 1129974428615469819129547 := by
  unfold tailWord_6601852
  simp only [CollatzResearch.WordTrace]
  refine ⟨120394662039312592700663905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160526216052416790267551873 120394662039312592700663905)
  ·
    refine ⟨90295996529484444525497929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120394662039312592700663905 90295996529484444525497929)
    ·
      refine ⟨67721997397113333394123447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90295996529484444525497929 67721997397113333394123447)
      ·
        refine ⟨101582996095670000091185171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67721997397113333394123447 101582996095670000091185171)
        ·
          refine ⟨152374494143505000136777757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101582996095670000091185171 152374494143505000136777757)
          ·
            refine ⟨57140435303814375051291659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152374494143505000136777757 57140435303814375051291659)
            ·
              refine ⟨85710652955721562576937489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57140435303814375051291659 85710652955721562576937489)
              ·
                refine ⟨64282989716791171932703117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85710652955721562576937489 64282989716791171932703117)
                ·
                  refine ⟨24106121143796689474763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64282989716791171932703117 24106121143796689474763669)
                  ·
                    refine ⟨1129974428615469819129547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24106121143796689474763669 1129974428615469819129547)
                    ·
                      rfl

theorem cell23_6601852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6601852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601852 prefixEnd_6601852 := by exact prefixLift 6601852
  have htrace : WordTrace (prefixWord ++ tailWord_6601852) baseStart_6601852 baseEnd_6601852 := by
    simpa [prefixWord, tailWord_6601852, baseEnd_6601852] using wordTrace_append hprefix tailTrace_6601852
  have hstable : (prefixWord ++ tailWord_6601852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601852).length < 2 ^ (prefixWord ++ tailWord_6601852).sum := by decide
  have hdescent : baseEnd_6601852 < baseStart_6601852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601853 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_6601853 : Nat := 118140960795 + 6601853 * 2 ^ 59
def prefixEnd_6601853 : Nat := 4983230072969 + 3 ^ 40 * 6601853 * 2
def baseEnd_6601853 : Nat := 3389923799327063953476137

theorem tailTrace_6601853 : CollatzResearch.WordTrace tailWord_6601853 prefixEnd_6601853 3389923799327063953476137 := by
  unfold tailWord_6601853
  simp only [CollatzResearch.WordTrace]
  refine ⟨240789360551621562572114213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160526240367747708381409475 240789360551621562572114213)
  ·
    refine ⟨45148005103429042982271415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240789360551621562572114213 45148005103429042982271415)
    ·
      refine ⟨67722007655143564473407123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45148005103429042982271415 67722007655143564473407123)
      ·
        refine ⟨101583011482715346710110685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67722007655143564473407123 101583011482715346710110685)
        ·
          refine ⟨38093629306018255016291507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101583011482715346710110685 38093629306018255016291507)
          ·
            refine ⟨57140443959027382524437261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38093629306018255016291507 57140443959027382524437261)
            ·
              refine ⟨21427666484635268446663973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57140443959027382524437261 21427666484635268446663973)
              ·
                refine ⟨4017687465869112833749495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21427666484635268446663973 4017687465869112833749495)
                ·
                  refine ⟨6026531198803669250624243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017687465869112833749495 6026531198803669250624243)
                  ·
                    refine ⟨9039796798205503875936365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026531198803669250624243 9039796798205503875936365)
                    ·
                      refine ⟨3389923799327063953476137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039796798205503875936365 3389923799327063953476137)
                      ·
                        rfl

theorem cell23_6601853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_6601853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601853 prefixEnd_6601853 := by exact prefixLift 6601853
  have htrace : WordTrace (prefixWord ++ tailWord_6601853) baseStart_6601853 baseEnd_6601853 := by
    simpa [prefixWord, tailWord_6601853, baseEnd_6601853] using wordTrace_append hprefix tailTrace_6601853
  have hstable : (prefixWord ++ tailWord_6601853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601853).length < 2 ^ (prefixWord ++ tailWord_6601853).sum := by decide
  have hdescent : baseEnd_6601853 < baseStart_6601853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601886 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6601886 : Nat := 118140960795 + 6601886 * 2 ^ 59
def prefixEnd_6601886 : Nat := 4983230072969 + 3 ^ 40 * 6601886 * 2
def baseEnd_6601886 : Nat := 1129980248062887441454495

theorem tailTrace_6601886 : CollatzResearch.WordTrace tailWord_6601886 prefixEnd_6601886 1129980248062887441454495 := by
  unfold tailWord_6601886
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098820520062751151008189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160527042773668006138710341 30098820520062751151008189)
  ·
    refine ⟨11287057695023531681628071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30098820520062751151008189 11287057695023531681628071)
    ·
      refine ⟨16930586542535297522442107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287057695023531681628071 16930586542535297522442107)
      ·
        refine ⟨25395879813802946283663161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930586542535297522442107 25395879813802946283663161)
        ·
          refine ⟨19046909860352209712747371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25395879813802946283663161 19046909860352209712747371)
          ·
            refine ⟨28570364790528314569121057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19046909860352209712747371 28570364790528314569121057)
            ·
              refine ⟨21427773592896235926840793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28570364790528314569121057 21427773592896235926840793)
              ·
                refine ⟨16070830194672176945130595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21427773592896235926840793 16070830194672176945130595)
                ·
                  refine ⟨24106245292008265417695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16070830194672176945130595 24106245292008265417695893)
                  ·
                    refine ⟨1129980248062887441454495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24106245292008265417695893 1129980248062887441454495)
                    ·
                      rfl

theorem cell23_6601886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6601886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601886 prefixEnd_6601886 := by exact prefixLift 6601886
  have htrace : WordTrace (prefixWord ++ tailWord_6601886) baseStart_6601886 baseEnd_6601886 := by
    simpa [prefixWord, tailWord_6601886, baseEnd_6601886] using wordTrace_append hprefix tailTrace_6601886
  have hstable : (prefixWord ++ tailWord_6601886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601886).length < 2 ^ (prefixWord ++ tailWord_6601886).sum := by decide
  have hdescent : baseEnd_6601886 < baseStart_6601886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601889 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6601889 : Nat := 118140960795 + 6601889 * 2 ^ 59
def prefixEnd_6601889 : Nat := 4983230072969 + 3 ^ 40 * 6601889 * 2
def baseEnd_6601889 : Nat := 3389942284630625812625971

theorem tailTrace_6601889 : CollatzResearch.WordTrace tailWord_6601889 prefixEnd_6601889 3389942284630625812625971 := by
  unfold tailWord_6601889
  simp only [CollatzResearch.WordTrace]
  refine ⟨240790673579491140720424721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160527115719660760480283147 240790673579491140720424721)
  ·
    refine ⟨180593005184618355540318541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240790673579491140720424721 180593005184618355540318541)
    ·
      refine ⟨67722376944231883327619453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180593005184618355540318541 67722376944231883327619453)
      ·
        refine ⟨25395891354086956247857295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67722376944231883327619453 25395891354086956247857295)
        ·
          refine ⟨38093837031130434371785943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25395891354086956247857295 38093837031130434371785943)
          ·
            refine ⟨57140755546695651557678915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38093837031130434371785943 57140755546695651557678915)
            ·
              refine ⟨85711133320043477336518373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57140755546695651557678915 85711133320043477336518373)
              ·
                refine ⟨16070837497508152000597195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85711133320043477336518373 16070837497508152000597195)
                ·
                  refine ⟨24106256246262228000895793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16070837497508152000597195 24106256246262228000895793)
                  ·
                    refine ⟨18079692184696671000671845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24106256246262228000895793 18079692184696671000671845)
                    ·
                      refine ⟨3389942284630625812625971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18079692184696671000671845 3389942284630625812625971)
                      ·
                        rfl

theorem cell23_6601889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6601889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601889 prefixEnd_6601889 := by exact prefixLift 6601889
  have htrace : WordTrace (prefixWord ++ tailWord_6601889) baseStart_6601889 baseEnd_6601889 := by
    simpa [prefixWord, tailWord_6601889, baseEnd_6601889] using wordTrace_append hprefix tailTrace_6601889
  have hstable : (prefixWord ++ tailWord_6601889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601889).length < 2 ^ (prefixWord ++ tailWord_6601889).sum := by decide
  have hdescent : baseEnd_6601889 < baseStart_6601889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601890 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_6601890 : Nat := 118140960795 + 6601890 * 2 ^ 59
def prefixEnd_6601890 : Nat := 4983230072969 + 3 ^ 40 * 6601890 * 2
def baseEnd_6601890 : Nat := 1129980932703760102904489

theorem tailTrace_6601890 : CollatzResearch.WordTrace tailWord_6601890 prefixEnd_6601890 1129980932703760102904489 := by
  unfold tailWord_6601890
  simp only [CollatzResearch.WordTrace]
  refine ⟨60197677513121879472802781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160527140034991678594140749 60197677513121879472802781)
  ·
    refine ⟨22574129067420704802301043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60197677513121879472802781 22574129067420704802301043)
    ·
      refine ⟨33861193601131057203451565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22574129067420704802301043 33861193601131057203451565)
      ·
        refine ⟨12697947600424146451294337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33861193601131057203451565 12697947600424146451294337)
        ·
          refine ⟨9523460700318109838470753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12697947600424146451294337 9523460700318109838470753)
          ·
            refine ⟨7142595525238582378853065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9523460700318109838470753 7142595525238582378853065)
            ·
              refine ⟨5356946643928936784139799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142595525238582378853065 5356946643928936784139799)
              ·
                refine ⟨8035419965893405176209699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356946643928936784139799 8035419965893405176209699)
                ·
                  refine ⟨12053129948840107764314549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035419965893405176209699 12053129948840107764314549)
                  ·
                    refine ⟨1129980932703760102904489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053129948840107764314549 1129980932703760102904489)
                    ·
                      rfl

theorem cell23_6601890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_6601890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601890 prefixEnd_6601890 := by exact prefixLift 6601890
  have htrace : WordTrace (prefixWord ++ tailWord_6601890) baseStart_6601890 baseEnd_6601890 := by
    simpa [prefixWord, tailWord_6601890, baseEnd_6601890] using wordTrace_append hprefix tailTrace_6601890
  have hstable : (prefixWord ++ tailWord_6601890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601890).length < 2 ^ (prefixWord ++ tailWord_6601890).sum := by decide
  have hdescent : baseEnd_6601890 < baseStart_6601890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601893 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 1, 1, 4]
def baseStart_6601893 : Nat := 118140960795 + 6601893 * 2 ^ 59
def prefixEnd_6601893 : Nat := 4983230072969 + 3 ^ 40 * 6601893 * 2
def baseEnd_6601893 : Nat := 3389944338553243796975953

theorem tailTrace_6601893 : CollatzResearch.WordTrace tailWord_6601893 prefixEnd_6601893 3389944338553243796975953 := by
  unfold tailWord_6601893
  simp only [CollatzResearch.WordTrace]
  refine ⟨240790819471476649403570333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160527212980984432935713555 240790819471476649403570333)
  ·
    refine ⟨90296557301803743526338875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240790819471476649403570333 90296557301803743526338875)
    ·
      refine ⟨135444835952705615289508313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90296557301803743526338875 135444835952705615289508313)
      ·
        refine ⟨101583626964529211467131235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135444835952705615289508313 101583626964529211467131235)
        ·
          refine ⟨152375440446793817200696853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101583626964529211467131235 152375440446793817200696853)
          ·
            refine ⟨7142598770943460181282665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152375440446793817200696853 7142598770943460181282665)
            ·
              refine ⟨5356949078207595135961999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142598770943460181282665 5356949078207595135961999)
              ·
                refine ⟨8035423617311392703942999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356949078207595135961999 8035423617311392703942999)
                ·
                  refine ⟨12053135425967089055914499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035423617311392703942999 12053135425967089055914499)
                  ·
                    refine ⟨18079703138950633583871749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12053135425967089055914499 18079703138950633583871749)
                    ·
                      refine ⟨3389944338553243796975953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18079703138950633583871749 3389944338553243796975953)
                      ·
                        rfl

theorem cell23_6601893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_6601893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601893 prefixEnd_6601893 := by exact prefixLift 6601893
  have htrace : WordTrace (prefixWord ++ tailWord_6601893) baseStart_6601893 baseEnd_6601893 := by
    simpa [prefixWord, tailWord_6601893, baseEnd_6601893] using wordTrace_append hprefix tailTrace_6601893
  have hstable : (prefixWord ++ tailWord_6601893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601893).length < 2 ^ (prefixWord ++ tailWord_6601893).sum := by decide
  have hdescent : baseEnd_6601893 < baseStart_6601893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601912 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_6601912 : Nat := 118140960795 + 6601912 * 2 ^ 59
def prefixEnd_6601912 : Nat := 4983230072969 + 3 ^ 40 * 6601912 * 2
def baseEnd_6601912 : Nat := 1129984698228559740879455

theorem tailTrace_6601912 : CollatzResearch.WordTrace tailWord_6601912 prefixEnd_6601912 1129984698228559740879455 := by
  unfold tailWord_6601912
  simp only [CollatzResearch.WordTrace]
  refine ⟨120395756229203907824255995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160527674972271877099007993 120395756229203907824255995)
  ·
    refine ⟨180593634343805861736383993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120395756229203907824255995 180593634343805861736383993)
    ·
      refine ⟨135445225757854396302287995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180593634343805861736383993 135445225757854396302287995)
      ·
        refine ⟨203167838636781594453431993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135445225757854396302287995 203167838636781594453431993)
        ·
          refine ⟨152375878977586195840073995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203167838636781594453431993 152375878977586195840073995)
          ·
            refine ⟨228563818466379293760110993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152375878977586195840073995 228563818466379293760110993)
            ·
              refine ⟨171422863849784470320083245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228563818466379293760110993 171422863849784470320083245)
              ·
                refine ⟨64283573943669176370031217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171422863849784470320083245 64283573943669176370031217)
                ·
                  refine ⟨48212680457751882277523413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64283573943669176370031217 48212680457751882277523413)
                  ·
                    refine ⟨1129984698228559740879455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48212680457751882277523413 1129984698228559740879455)
                    ·
                      rfl

theorem cell23_6601912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_6601912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601912 prefixEnd_6601912 := by exact prefixLift 6601912
  have htrace : WordTrace (prefixWord ++ tailWord_6601912) baseStart_6601912 baseEnd_6601912 := by
    simpa [prefixWord, tailWord_6601912, baseEnd_6601912] using wordTrace_append hprefix tailTrace_6601912
  have hstable : (prefixWord ++ tailWord_6601912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601912).length < 2 ^ (prefixWord ++ tailWord_6601912).sum := by decide
  have hdescent : baseEnd_6601912 < baseStart_6601912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601933 : List Nat := [1, 6, 2, 2, 1, 1, 1, 9]
def baseStart_6601933 : Nat := 118140960795 + 6601933 * 2 ^ 59
def prefixEnd_6601933 : Nat := 4983230072969 + 3 ^ 40 * 6601933 * 2
def baseEnd_6601933 : Nat := 125554254732571245943547

theorem tailTrace_6601933 : CollatzResearch.WordTrace tailWord_6601933 prefixEnd_6601933 125554254732571245943547 := by
  unfold tailWord_6601933
  simp only [CollatzResearch.WordTrace]
  refine ⟨240792278391331736235026453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160528185594221157490017635 240792278391331736235026453)
  ·
    refine ⟨11287138049593675136016865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240792278391331736235026453 11287138049593675136016865)
    ·
      refine ⟨8465353537195256352012649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11287138049593675136016865 8465353537195256352012649)
      ·
        refine ⟨6349015152896442264009487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8465353537195256352012649 6349015152896442264009487)
        ·
          refine ⟨9523522729344663396014231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349015152896442264009487 9523522729344663396014231)
          ·
            refine ⟨14285284094016995094021347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9523522729344663396014231 14285284094016995094021347)
            ·
              refine ⟨21427926141025492641032021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14285284094016995094021347 21427926141025492641032021)
              ·
                refine ⟨125554254732571245943547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21427926141025492641032021 125554254732571245943547)
                ·
                  rfl

theorem cell23_6601933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 9].length) (baseStart_6601933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601933 prefixEnd_6601933 := by exact prefixLift 6601933
  have htrace : WordTrace (prefixWord ++ tailWord_6601933) baseStart_6601933 baseEnd_6601933 := by
    simpa [prefixWord, tailWord_6601933, baseEnd_6601933] using wordTrace_append hprefix tailTrace_6601933
  have hstable : (prefixWord ++ tailWord_6601933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601933).length < 2 ^ (prefixWord ++ tailWord_6601933).sum := by decide
  have hdescent : baseEnd_6601933 < baseStart_6601933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601944 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_6601944 : Nat := 118140960795 + 6601944 * 2 ^ 59
def prefixEnd_6601944 : Nat := 4983230072969 + 3 ^ 40 * 6601944 * 2
def baseEnd_6601944 : Nat := 3389970526066623097438219

theorem tailTrace_6601944 : CollatzResearch.WordTrace tailWord_6601944 prefixEnd_6601944 3389970526066623097438219 := by
  unfold tailWord_6601944
  simp only [CollatzResearch.WordTrace]
  refine ⟨120396339797145942556838443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160528453062861256742451257 120396339797145942556838443)
  ·
    refine ⟨180594509695718913835257665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120396339797145942556838443 180594509695718913835257665)
    ·
      refine ⟨135445882271789185376443249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180594509695718913835257665 135445882271789185376443249)
      ·
        refine ⟨101584411703841889032332437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135445882271789185376443249 101584411703841889032332437)
        ·
          refine ⟨4761769298617588548390583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101584411703841889032332437 4761769298617588548390583)
          ·
            refine ⟨7142653947926382822585875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761769298617588548390583 7142653947926382822585875)
            ·
              refine ⟨10713980921889574233878813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142653947926382822585875 10713980921889574233878813)
              ·
                refine ⟨4017742845708590337704555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10713980921889574233878813 4017742845708590337704555)
                ·
                  refine ⟨6026614268562885506556833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017742845708590337704555 6026614268562885506556833)
                  ·
                    refine ⟨4519960701422164129917625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6026614268562885506556833 4519960701422164129917625)
                    ·
                      refine ⟨3389970526066623097438219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519960701422164129917625 3389970526066623097438219)
                      ·
                        rfl

theorem cell23_6601944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_6601944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601944 prefixEnd_6601944 := by exact prefixLift 6601944
  have htrace : WordTrace (prefixWord ++ tailWord_6601944) baseStart_6601944 baseEnd_6601944 := by
    simpa [prefixWord, tailWord_6601944, baseEnd_6601944] using wordTrace_append hprefix tailTrace_6601944
  have hstable : (prefixWord ++ tailWord_6601944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601944).length < 2 ^ (prefixWord ++ tailWord_6601944).sum := by decide
  have hdescent : baseEnd_6601944 < baseStart_6601944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601953 : List Nat := [1, 2, 3, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_6601953 : Nat := 118140960795 + 6601953 * 2 ^ 59
def prefixEnd_6601953 : Nat := 4983230072969 + 3 ^ 40 * 6601953 * 2
def baseEnd_6601953 : Nat := 3389975147392513562225677

theorem tailTrace_6601953 : CollatzResearch.WordTrace tailWord_6601953 prefixEnd_6601953 3389975147392513562225677 := by
  unfold tailWord_6601953
  simp only [CollatzResearch.WordTrace]
  refine ⟨240793007851259279650754513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160528671900839519767169675 240793007851259279650754513)
  ·
    refine ⟨180594755888444459738065885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240793007851259279650754513 180594755888444459738065885)
    ·
      refine ⟨67723033458166672401774707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180594755888444459738065885 67723033458166672401774707)
      ·
        refine ⟨101584550187250008602662061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67723033458166672401774707 101584550187250008602662061)
        ·
          refine ⟨38094206320218753225998273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101584550187250008602662061 38094206320218753225998273)
          ·
            refine ⟨28570654740164064919498705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38094206320218753225998273 28570654740164064919498705)
            ·
              refine ⟨21427991055123048689624029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28570654740164064919498705 21427991055123048689624029)
              ·
                refine ⟨8035496645671143258609011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21427991055123048689624029 8035496645671143258609011)
                ·
                  refine ⟨12053244968506714887913517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035496645671143258609011 12053244968506714887913517)
                  ·
                    refine ⟨4519966863190018082967569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12053244968506714887913517 4519966863190018082967569)
                    ·
                      refine ⟨3389975147392513562225677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4519966863190018082967569 3389975147392513562225677)
                      ·
                        rfl

theorem cell23_6601953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_6601953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601953 prefixEnd_6601953 := by exact prefixLift 6601953
  have htrace : WordTrace (prefixWord ++ tailWord_6601953) baseStart_6601953 baseEnd_6601953 := by
    simpa [prefixWord, tailWord_6601953, baseEnd_6601953] using wordTrace_append hprefix tailTrace_6601953
  have hstable : (prefixWord ++ tailWord_6601953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601953).length < 2 ^ (prefixWord ++ tailWord_6601953).sum := by decide
  have hdescent : baseEnd_6601953 < baseStart_6601953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601969 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_6601969 : Nat := 118140960795 + 6601969 * 2 ^ 59
def prefixEnd_6601969 : Nat := 4983230072969 + 3 ^ 40 * 6601969 * 2
def baseEnd_6601969 : Nat := 3389983363082985499625603

theorem tailTrace_6601969 : CollatzResearch.WordTrace tailWord_6601969 prefixEnd_6601969 3389983363082985499625603 := by
  unfold tailWord_6601969
  simp only [CollatzResearch.WordTrace]
  refine ⟨240793591419201314383336961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160529060946134209588891307 240793591419201314383336961)
  ·
    refine ⟨180595193564400985787502721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240793591419201314383336961 180595193564400985787502721)
    ·
      refine ⟨135446395173300739340627041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180595193564400985787502721 135446395173300739340627041)
      ·
        refine ⟨101584796379975554505470281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135446395173300739340627041 101584796379975554505470281)
        ·
          refine ⟨76188597284981665879102711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101584796379975554505470281 76188597284981665879102711)
          ·
            refine ⟨114282895927472498818654067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76188597284981665879102711 114282895927472498818654067)
            ·
              refine ⟨171424343891208748227981101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114282895927472498818654067 171424343891208748227981101)
              ·
                refine ⟨64284128959203280585492913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171424343891208748227981101 64284128959203280585492913)
                ·
                  refine ⟨48213096719402460439119685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64284128959203280585492913 48213096719402460439119685)
                  ·
                    refine ⟨9039955634887961332334941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48213096719402460439119685 9039955634887961332334941)
                    ·
                      refine ⟨3389983363082985499625603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039955634887961332334941 3389983363082985499625603)
                      ·
                        rfl

theorem cell23_6601969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_6601969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601969 prefixEnd_6601969 := by exact prefixLift 6601969
  have htrace : WordTrace (prefixWord ++ tailWord_6601969) baseStart_6601969 baseEnd_6601969 := by
    simpa [prefixWord, tailWord_6601969, baseEnd_6601969] using wordTrace_append hprefix tailTrace_6601969
  have hstable : (prefixWord ++ tailWord_6601969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601969).length < 2 ^ (prefixWord ++ tailWord_6601969).sum := by decide
  have hdescent : baseEnd_6601969 < baseStart_6601969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6601999 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_6601999 : Nat := 118140960795 + 6601999 * 2 ^ 59
def prefixEnd_6601999 : Nat := 4983230072969 + 3 ^ 40 * 6601999 * 2
def baseEnd_6601999 : Nat := 3389998767502620382250465

theorem tailTrace_6601999 : CollatzResearch.WordTrace tailWord_6601999 prefixEnd_6601999 3389998767502620382250465 := by
  unfold tailWord_6601999
  simp only [CollatzResearch.WordTrace]
  refine ⟨240794685609092629506929051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160529790406061753004619367 240794685609092629506929051)
  ·
    refine ⟨361192028413638944260393577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240794685609092629506929051 361192028413638944260393577)
    ·
      refine ⟨270894021310229208195295183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361192028413638944260393577 270894021310229208195295183)
      ·
        refine ⟨406341031965343812292942775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270894021310229208195295183 406341031965343812292942775)
        ·
          refine ⟨609511547948015718439414163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406341031965343812292942775 609511547948015718439414163)
          ·
            refine ⟨914267321922023577659121245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609511547948015718439414163 914267321922023577659121245)
            ·
              refine ⟨342850245720758841622170467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914267321922023577659121245 342850245720758841622170467)
              ·
                refine ⟨514275368581138262433255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342850245720758841622170467 514275368581138262433255701)
                ·
                  refine ⟨24106657902240856051558861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 514275368581138262433255701 24106657902240856051558861)
                  ·
                    refine ⟨9039996713340321019334573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24106657902240856051558861 9039996713340321019334573)
                    ·
                      refine ⟨3389998767502620382250465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9039996713340321019334573 3389998767502620382250465)
                      ·
                        rfl

theorem cell23_6601999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_6601999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6601999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6601999 prefixEnd_6601999 := by exact prefixLift 6601999
  have htrace : WordTrace (prefixWord ++ tailWord_6601999) baseStart_6601999 baseEnd_6601999 := by
    simpa [prefixWord, tailWord_6601999, baseEnd_6601999] using wordTrace_append hprefix tailTrace_6601999
  have hstable : (prefixWord ++ tailWord_6601999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6601999).length < 2 ^ (prefixWord ++ tailWord_6601999).sum := by decide
  have hdescent : baseEnd_6601999 < baseStart_6601999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6601999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602036 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6602036 : Nat := 118140960795 + 6602036 * 2 ^ 59
def prefixEnd_6602036 : Nat := 4983230072969 + 3 ^ 40 * 6602036 * 2
def baseEnd_6602036 : Nat := 1130005922095612245829265

theorem tailTrace_6602036 : CollatzResearch.WordTrace tailWord_6602036 prefixEnd_6602036 1130005922095612245829265 := by
  unfold tailWord_6602036
  simp only [CollatzResearch.WordTrace]
  refine ⟨120398017554979292413012981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160530690073305723217350641 120398017554979292413012981)
  ·
    refine ⟨11287314145779308663719967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120398017554979292413012981 11287314145779308663719967)
    ·
      refine ⟨16930971218668962995579951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287314145779308663719967 16930971218668962995579951)
      ·
        refine ⟨25396456828003444493369927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930971218668962995579951 25396456828003444493369927)
        ·
          refine ⟨38094685242005166740054891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25396456828003444493369927 38094685242005166740054891)
          ·
            refine ⟨57142027863007750110082337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38094685242005166740054891 57142027863007750110082337)
            ·
              refine ⟨42856520897255812582561753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57142027863007750110082337 42856520897255812582561753)
              ·
                refine ⟨32142390672941859436921315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42856520897255812582561753 32142390672941859436921315)
                ·
                  refine ⟨48213586009412789155381973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32142390672941859436921315 48213586009412789155381973)
                  ·
                    refine ⟨1130005922095612245829265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48213586009412789155381973 1130005922095612245829265)
                    ·
                      rfl

theorem cell23_6602036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6602036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602036 prefixEnd_6602036 := by exact prefixLift 6602036
  have htrace : WordTrace (prefixWord ++ tailWord_6602036) baseStart_6602036 baseEnd_6602036 := by
    simpa [prefixWord, tailWord_6602036, baseEnd_6602036] using wordTrace_append hprefix tailTrace_6602036
  have hstable : (prefixWord ++ tailWord_6602036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602036).length < 2 ^ (prefixWord ++ tailWord_6602036).sum := by decide
  have hdescent : baseEnd_6602036 < baseStart_6602036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602056 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_6602056 : Nat := 118140960795 + 6602056 * 2 ^ 59
def prefixEnd_6602056 : Nat := 4983230072969 + 3 ^ 40 * 6602056 * 2
def baseEnd_6602056 : Nat := 3390028035899926659237703

theorem tailTrace_6602056 : CollatzResearch.WordTrace tailWord_6602056 prefixEnd_6602056 3390028035899926659237703 := by
  unfold tailWord_6602056
  simp only [CollatzResearch.WordTrace]
  refine ⟨120398382284943064120877011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160531176379924085494502681 120398382284943064120877011)
  ·
    refine ⟨180597573427414596181315517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120398382284943064120877011 180597573427414596181315517)
    ·
      refine ⟨67724090035280473567993319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180597573427414596181315517 67724090035280473567993319)
      ·
        refine ⟨101586135052920710351989979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67724090035280473567993319 101586135052920710351989979)
        ·
          refine ⟨152379202579381065527984969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101586135052920710351989979 152379202579381065527984969)
          ·
            refine ⟨114284401934535799145988727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152379202579381065527984969 114284401934535799145988727)
            ·
              refine ⟨171426602901803698718983091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114284401934535799145988727 171426602901803698718983091)
              ·
                refine ⟨257139904352705548078474637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171426602901803698718983091 257139904352705548078474637)
                ·
                  refine ⟨96427464132264580529427989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257139904352705548078474637 96427464132264580529427989)
                  ·
                    refine ⟨4520037381199902212316937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96427464132264580529427989 4520037381199902212316937)
                    ·
                      refine ⟨3390028035899926659237703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520037381199902212316937 3390028035899926659237703)
                      ·
                        rfl

theorem cell23_6602056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_6602056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602056 prefixEnd_6602056 := by exact prefixLift 6602056
  have htrace : WordTrace (prefixWord ++ tailWord_6602056) baseStart_6602056 baseEnd_6602056 := by
    simpa [prefixWord, tailWord_6602056, baseEnd_6602056] using wordTrace_append hprefix tailTrace_6602056
  have hstable : (prefixWord ++ tailWord_6602056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602056).length < 2 ^ (prefixWord ++ tailWord_6602056).sum := by decide
  have hdescent : baseEnd_6602056 < baseStart_6602056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602066 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_6602066 : Nat := 118140960795 + 6602066 * 2 ^ 59
def prefixEnd_6602066 : Nat := 4983230072969 + 3 ^ 40 * 6602066 * 2
def baseEnd_6602066 : Nat := 1130011056902157206704219

theorem tailTrace_6602066 : CollatzResearch.WordTrace tailWord_6602066 prefixEnd_6602066 1130011056902157206704219 := by
  unfold tailWord_6602066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199282324962474987404513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160531419533233266633078701 60199282324962474987404513)
  ·
    refine ⟨45149461743721856240553385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60199282324962474987404513 45149461743721856240553385)
    ·
      refine ⟨33862096307791392180415039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45149461743721856240553385 33862096307791392180415039)
      ·
        refine ⟨50793144461687088270622559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33862096307791392180415039 50793144461687088270622559)
        ·
          refine ⟨76189716692530632405933839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50793144461687088270622559 76189716692530632405933839)
          ·
            refine ⟨114284575038795948608900759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76189716692530632405933839 114284575038795948608900759)
            ·
              refine ⟨171426862558193922913351139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114284575038795948608900759 171426862558193922913351139)
              ·
                refine ⟨257140293837290884370026709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171426862558193922913351139 257140293837290884370026709)
                ·
                  refine ⟨6026725636811505102422501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 257140293837290884370026709 6026725636811505102422501)
                  ·
                    refine ⟨1130011056902157206704219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6026725636811505102422501 1130011056902157206704219)
                    ·
                      rfl

theorem cell23_6602066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_6602066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602066 prefixEnd_6602066 := by exact prefixLift 6602066
  have htrace : WordTrace (prefixWord ++ tailWord_6602066) baseStart_6602066 baseEnd_6602066 := by
    simpa [prefixWord, tailWord_6602066, baseEnd_6602066] using wordTrace_append hprefix tailTrace_6602066
  have hstable : (prefixWord ++ tailWord_6602066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602066).length < 2 ^ (prefixWord ++ tailWord_6602066).sum := by decide
  have hdescent : baseEnd_6602066 < baseStart_6602066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602083 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 3, 4]
def baseStart_6602083 : Nat := 118140960795 + 6602083 * 2 ^ 59
def prefixEnd_6602083 : Nat := 4983230072969 + 3 ^ 40 * 6602083 * 2
def baseEnd_6602083 : Nat := 1130013966625866017866693

theorem tailTrace_6602083 : CollatzResearch.WordTrace tailWord_6602083 prefixEnd_6602083 1130013966625866017866693 := by
  unfold tailWord_6602083
  simp only [CollatzResearch.WordTrace]
  refine ⟨240797749340788311852986903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160531832893858874568657935 240797749340788311852986903)
  ·
    refine ⟨361196624011182467779480355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240797749340788311852986903 361196624011182467779480355)
    ·
      refine ⟨541794936016773701669220533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361196624011182467779480355 541794936016773701669220533)
      ·
        refine ⟨50793275251572534531489425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 541794936016773701669220533 50793275251572534531489425)
        ·
          refine ⟨38094956438679400898617069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50793275251572534531489425 38094956438679400898617069)
          ·
            refine ⟨14285608664504775336981401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38094956438679400898617069 14285608664504775336981401)
            ·
              refine ⟨10714206498378581502736051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14285608664504775336981401 10714206498378581502736051)
              ·
                refine ⟨16071309747567872254104077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10714206498378581502736051 16071309747567872254104077)
                ·
                  refine ⟨6026741155337952095289029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16071309747567872254104077 6026741155337952095289029)
                  ·
                    refine ⟨1130013966625866017866693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6026741155337952095289029 1130013966625866017866693)
                    ·
                      rfl

theorem cell23_6602083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 4].length) (baseStart_6602083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602083 prefixEnd_6602083 := by exact prefixLift 6602083
  have htrace : WordTrace (prefixWord ++ tailWord_6602083) baseStart_6602083 baseEnd_6602083 := by
    simpa [prefixWord, tailWord_6602083, baseEnd_6602083] using wordTrace_append hprefix tailTrace_6602083
  have hstable : (prefixWord ++ tailWord_6602083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602083).length < 2 ^ (prefixWord ++ tailWord_6602083).sum := by decide
  have hdescent : baseEnd_6602083 < baseStart_6602083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602133 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_6602133 : Nat := 118140960795 + 6602133 * 2 ^ 59
def prefixEnd_6602133 : Nat := 4983230072969 + 3 ^ 40 * 6602133 * 2
def baseEnd_6602133 : Nat := 3390067573910322857974849

theorem tailTrace_6602133 : CollatzResearch.WordTrace tailWord_6602133 prefixEnd_6602133 3390067573910322857974849 := by
  unfold tailWord_6602133
  simp only [CollatzResearch.WordTrace]
  refine ⟨240799572990607170392307053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160533048660404780261538035 240799572990607170392307053)
  ·
    refine ⟨90299839871477688897115145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240799572990607170392307053 90299839871477688897115145)
    ·
      refine ⟨67724879903608266672836359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90299839871477688897115145 67724879903608266672836359)
      ·
        refine ⟨101587319855412400009254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67724879903608266672836359 101587319855412400009254539)
        ·
          refine ⟨152380979783118600013881809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101587319855412400009254539 152380979783118600013881809)
          ·
            refine ⟨114285734837338950010411357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152380979783118600013881809 114285734837338950010411357)
            ·
              refine ⟨42857150564002106253904259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114285734837338950010411357 42857150564002106253904259)
              ·
                refine ⟨64285725846003159380856389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42857150564002106253904259 64285725846003159380856389)
                ·
                  refine ⟨12053573596125592383910573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64285725846003159380856389 12053573596125592383910573)
                  ·
                    refine ⟨4520090098547097143966465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12053573596125592383910573 4520090098547097143966465)
                    ·
                      refine ⟨3390067573910322857974849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520090098547097143966465 3390067573910322857974849)
                      ·
                        rfl

theorem cell23_6602133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_6602133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602133 prefixEnd_6602133 := by exact prefixLift 6602133
  have htrace : WordTrace (prefixWord ++ tailWord_6602133) baseStart_6602133 baseEnd_6602133 := by
    simpa [prefixWord, tailWord_6602133, baseEnd_6602133] using wordTrace_append hprefix tailTrace_6602133
  have hstable : (prefixWord ++ tailWord_6602133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602133).length < 2 ^ (prefixWord ++ tailWord_6602133).sum := by decide
  have hdescent : baseEnd_6602133 < baseStart_6602133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602176 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_6602176 : Nat := 118140960795 + 6602176 * 2 ^ 59
def prefixEnd_6602176 : Nat := 4983230072969 + 3 ^ 40 * 6602176 * 2
def baseEnd_6602176 : Nat := 3390089653578466189737151

theorem tailTrace_6602176 : CollatzResearch.WordTrace tailWord_6602176 prefixEnd_6602176 3390089653578466189737151 := by
  unfold tailWord_6602176
  simp only [CollatzResearch.WordTrace]
  refine ⟨120400570664725694368061191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160534094219634259157414921 120400570664725694368061191)
  ·
    refine ⟨180600855997088541552091787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120400570664725694368061191 180600855997088541552091787)
    ·
      refine ⟨270901283995632812328137681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180600855997088541552091787 270901283995632812328137681)
      ·
        refine ⟨203175962996724609246103261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270901283995632812328137681 203175962996724609246103261)
        ·
          refine ⟨76190986123771728467288723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203175962996724609246103261 76190986123771728467288723)
          ·
            refine ⟨114286479185657592700933085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76190986123771728467288723 114286479185657592700933085)
            ·
              refine ⟨42857429694621597262849907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114286479185657592700933085 42857429694621597262849907)
              ·
                refine ⟨64286144541932395894274861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42857429694621597262849907 64286144541932395894274861)
                ·
                  refine ⟨24107304203224648460353073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64286144541932395894274861 24107304203224648460353073)
                  ·
                    refine ⟨18080478152418486345264805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24107304203224648460353073 18080478152418486345264805)
                    ·
                      refine ⟨3390089653578466189737151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18080478152418486345264805 3390089653578466189737151)
                      ·
                        rfl

theorem cell23_6602176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_6602176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602176 prefixEnd_6602176 := by exact prefixLift 6602176
  have htrace : WordTrace (prefixWord ++ tailWord_6602176) baseStart_6602176 baseEnd_6602176 := by
    simpa [prefixWord, tailWord_6602176, baseEnd_6602176] using wordTrace_append hprefix tailTrace_6602176
  have hstable : (prefixWord ++ tailWord_6602176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602176).length < 2 ^ (prefixWord ++ tailWord_6602176).sum := by decide
  have hdescent : baseEnd_6602176 < baseStart_6602176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602216 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6602216 : Nat := 118140960795 + 6602216 * 2 ^ 59
def prefixEnd_6602216 : Nat := 4983230072969 + 3 ^ 40 * 6602216 * 2
def baseEnd_6602216 : Nat := 1130036730934882011078989

theorem tailTrace_6602216 : CollatzResearch.WordTrace tailWord_6602216 prefixEnd_6602216 1130036730934882011078989 := by
  unfold tailWord_6602216
  simp only [CollatzResearch.WordTrace]
  refine ⟨120401300124653237783789251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160535066832870983711719001 120401300124653237783789251)
  ·
    refine ⟨180601950186979856675683877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120401300124653237783789251 180601950186979856675683877)
    ·
      refine ⟨33862865660058723126690727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180601950186979856675683877 33862865660058723126690727)
      ·
        refine ⟨50794298490088084690036091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33862865660058723126690727 50794298490088084690036091)
        ·
          refine ⟨76191447735132127035054137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50794298490088084690036091 76191447735132127035054137)
          ·
            refine ⟨57143585801349095276290603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76191447735132127035054137 57143585801349095276290603)
            ·
              refine ⟨85715378702023642914435905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57143585801349095276290603 85715378702023642914435905)
              ·
                refine ⟨64286534026517732185826929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85715378702023642914435905 64286534026517732185826929)
                ·
                  refine ⟨48214900519888299139370197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64286534026517732185826929 48214900519888299139370197)
                  ·
                    refine ⟨1130036730934882011078989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48214900519888299139370197 1130036730934882011078989)
                    ·
                      rfl

theorem cell23_6602216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6602216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602216 prefixEnd_6602216 := by exact prefixLift 6602216
  have htrace : WordTrace (prefixWord ++ tailWord_6602216) baseStart_6602216 baseEnd_6602216 := by
    simpa [prefixWord, tailWord_6602216, baseEnd_6602216] using wordTrace_append hprefix tailTrace_6602216
  have hstable : (prefixWord ++ tailWord_6602216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602216).length < 2 ^ (prefixWord ++ tailWord_6602216).sum := by decide
  have hdescent : baseEnd_6602216 < baseStart_6602216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602230 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6602230 : Nat := 118140960795 + 6602230 * 2 ^ 59
def prefixEnd_6602230 : Nat := 4983230072969 + 3 ^ 40 * 6602230 * 2
def baseEnd_6602230 : Nat := 3390117381533808978461903

theorem tailTrace_6602230 : CollatzResearch.WordTrace tailWord_6602230 prefixEnd_6602230 3390117381533808978461903 := by
  unfold tailWord_6602230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050194429453484747411759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160535407247503837305725429 15050194429453484747411759)
  ·
    refine ⟨22575291644180227121117639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15050194429453484747411759 22575291644180227121117639)
    ·
      refine ⟨33862937466270340681676459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22575291644180227121117639 33862937466270340681676459)
      ·
        refine ⟨50794406199405511022514689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33862937466270340681676459 50794406199405511022514689)
        ·
          refine ⟨38095804649554133266886017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50794406199405511022514689 38095804649554133266886017)
          ·
            refine ⟨28571853487165599950164513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38095804649554133266886017 28571853487165599950164513)
            ·
              refine ⟨21428890115374199962623385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28571853487165599950164513 21428890115374199962623385)
              ·
                refine ⟨16071667586530649971967539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21428890115374199962623385 16071667586530649971967539)
                ·
                  refine ⟨24107501379795974957951309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16071667586530649971967539 24107501379795974957951309)
                  ·
                    refine ⟨9040313017423490609231741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24107501379795974957951309 9040313017423490609231741)
                    ·
                      refine ⟨3390117381533808978461903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9040313017423490609231741 3390117381533808978461903)
                      ·
                        rfl

theorem cell23_6602230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6602230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602230 prefixEnd_6602230 := by exact prefixLift 6602230
  have htrace : WordTrace (prefixWord ++ tailWord_6602230) baseStart_6602230 baseEnd_6602230 := by
    simpa [prefixWord, tailWord_6602230, baseEnd_6602230] using wordTrace_append hprefix tailTrace_6602230
  have hstable : (prefixWord ++ tailWord_6602230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602230).length < 2 ^ (prefixWord ++ tailWord_6602230).sum := by decide
  have hdescent : baseEnd_6602230 < baseStart_6602230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602247 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6602247 : Nat := 118140960795 + 6602247 * 2 ^ 59
def prefixEnd_6602247 : Nat := 4983230072969 + 3 ^ 40 * 6602247 * 2
def baseEnd_6602247 : Nat := 3390126110704935411949325

theorem tailTrace_6602247 : CollatzResearch.WordTrace tailWord_6602247 prefixEnd_6602247 3390126110704935411949325 := by
  unfold tailWord_6602247
  simp only [CollatzResearch.WordTrace]
  refine ⟨240803730912194167861956995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160535820608129445241304663 240803730912194167861956995)
  ·
    refine ⟨361205596368291251792935493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240803730912194167861956995 361205596368291251792935493)
    ·
      refine ⟨67726049319054609711175405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361205596368291251792935493 67726049319054609711175405)
      ·
        refine ⟨25397268494645478641690777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67726049319054609711175405 25397268494645478641690777)
        ·
          refine ⟨19047951370984108981268083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25397268494645478641690777 19047951370984108981268083)
          ·
            refine ⟨28571927056476163471902125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19047951370984108981268083 28571927056476163471902125)
            ·
              refine ⟨10714472646178561301963297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28571927056476163471902125 10714472646178561301963297)
              ·
                refine ⟨8035854484633920976472473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10714472646178561301963297 8035854484633920976472473)
                ·
                  refine ⟨6026890863475440732354355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8035854484633920976472473 6026890863475440732354355)
                  ·
                    refine ⟨9040336295213161098531533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026890863475440732354355 9040336295213161098531533)
                    ·
                      refine ⟨3390126110704935411949325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9040336295213161098531533 3390126110704935411949325)
                      ·
                        rfl

theorem cell23_6602247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6602247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602247 prefixEnd_6602247 := by exact prefixLift 6602247
  have htrace : WordTrace (prefixWord ++ tailWord_6602247) baseStart_6602247 baseEnd_6602247 := by
    simpa [prefixWord, tailWord_6602247, baseEnd_6602247] using wordTrace_append hprefix tailTrace_6602247
  have hstable : (prefixWord ++ tailWord_6602247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602247).length < 2 ^ (prefixWord ++ tailWord_6602247).sum := by decide
  have hdescent : baseEnd_6602247 < baseStart_6602247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602264 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6602264 : Nat := 118140960795 + 6602264 * 2 ^ 59
def prefixEnd_6602264 : Nat := 4983230072969 + 3 ^ 40 * 6602264 * 2
def baseEnd_6602264 : Nat := 3390134839876061845436747

theorem tailTrace_6602264 : CollatzResearch.WordTrace tailWord_6602264 prefixEnd_6602264 3390134839876061845436747 := by
  unfold tailWord_6602264
  simp only [CollatzResearch.WordTrace]
  refine ⟨120402175476566289882662923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160536233968755053176883897 120402175476566289882662923)
  ·
    refine ⟨180603263214849434823994385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120402175476566289882662923 180603263214849434823994385)
    ·
      refine ⟨135452447411137076117995789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180603263214849434823994385 135452447411137076117995789)
      ·
        refine ⟨50794667779176403544248421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135452447411137076117995789 50794667779176403544248421)
        ·
          refine ⟨9524000208595575664546579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50794667779176403544248421 9524000208595575664546579)
          ·
            refine ⟨14286000312893363496819869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524000208595575664546579 14286000312893363496819869)
            ·
              refine ⟨5357250117335011311307451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14286000312893363496819869 5357250117335011311307451)
              ·
                refine ⟨8035875176002516966961177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357250117335011311307451 8035875176002516966961177)
                ·
                  refine ⟨6026906382001887725220883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8035875176002516966961177 6026906382001887725220883)
                  ·
                    refine ⟨9040359573002831587831325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026906382001887725220883 9040359573002831587831325)
                    ·
                      refine ⟨3390134839876061845436747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9040359573002831587831325 3390134839876061845436747)
                      ·
                        rfl

theorem cell23_6602264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6602264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602264 prefixEnd_6602264 := by exact prefixLift 6602264
  have htrace : WordTrace (prefixWord ++ tailWord_6602264) baseStart_6602264 baseEnd_6602264 := by
    simpa [prefixWord, tailWord_6602264, baseEnd_6602264] using wordTrace_append hprefix tailTrace_6602264
  have hstable : (prefixWord ++ tailWord_6602264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602264).length < 2 ^ (prefixWord ++ tailWord_6602264).sum := by decide
  have hdescent : baseEnd_6602264 < baseStart_6602264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602340 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_6602340 : Nat := 118140960795 + 6602340 * 2 ^ 59
def prefixEnd_6602340 : Nat := 4983230072969 + 3 ^ 40 * 6602340 * 2
def baseEnd_6602340 : Nat := 1130057954801934516028799

theorem tailTrace_6602340 : CollatzResearch.WordTrace tailWord_6602340 prefixEnd_6602340 1130057954801934516028799 := by
  unfold tailWord_6602340
  simp only [CollatzResearch.WordTrace]
  refine ⟨120403561450428622372546237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160538081933904829830061649 120403561450428622372546237)
  ·
    refine ⟨45151335543910733389704839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120403561450428622372546237 45151335543910733389704839)
    ·
      refine ⟨67727003315866100084557259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45151335543910733389704839 67727003315866100084557259)
      ·
        refine ⟨101590504973799150126835889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67727003315866100084557259 101590504973799150126835889)
        ·
          refine ⟨76192878730349362595126917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101590504973799150126835889 76192878730349362595126917)
          ·
            refine ⟨14286164761940505486586297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76192878730349362595126917 14286164761940505486586297)
            ·
              refine ⟨10714623571455379114939723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14286164761940505486586297 10714623571455379114939723)
              ·
                refine ⟨16071935357183068672409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10714623571455379114939723 16071935357183068672409585)
                ·
                  refine ⟨12053951517887301504307189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16071935357183068672409585 12053951517887301504307189)
                  ·
                    refine ⟨1130057954801934516028799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053951517887301504307189 1130057954801934516028799)
                    ·
                      rfl

theorem cell23_6602340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_6602340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602340 prefixEnd_6602340 := by exact prefixLift 6602340
  have htrace : WordTrace (prefixWord ++ tailWord_6602340) baseStart_6602340 baseEnd_6602340 := by
    simpa [prefixWord, tailWord_6602340, baseEnd_6602340] using wordTrace_append hprefix tailTrace_6602340
  have hstable : (prefixWord ++ tailWord_6602340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602340).length < 2 ^ (prefixWord ++ tailWord_6602340).sum := by decide
  have hdescent : baseEnd_6602340 < baseStart_6602340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602343 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6602343 : Nat := 118140960795 + 6602343 * 2 ^ 59
def prefixEnd_6602343 : Nat := 4983230072969 + 3 ^ 40 * 6602343 * 2
def baseEnd_6602343 : Nat := 3390175404847767036348883

theorem tailTrace_6602343 : CollatzResearch.WordTrace tailWord_6602343 prefixEnd_6602343 3390175404847767036348883 := by
  unfold tailWord_6602343
  simp only [CollatzResearch.WordTrace]
  refine ⟨240807232319846376257451683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160538154879897584171634455 240807232319846376257451683)
  ·
    refine ⟨361210848479769564386177525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240807232319846376257451683 361210848479769564386177525)
    ·
      refine ⟨33863517044978396661204143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361210848479769564386177525 33863517044978396661204143)
      ·
        refine ⟨50795275567467594991806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33863517044978396661204143 50795275567467594991806215)
        ·
          refine ⟨76192913351201392487709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50795275567467594991806215 76192913351201392487709323)
          ·
            refine ⟨114289370026802088731563985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76192913351201392487709323 114289370026802088731563985)
            ·
              refine ⟨85717027520101566548672989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114289370026802088731563985 85717027520101566548672989)
              ·
                refine ⟨32143885320038087455752371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85717027520101566548672989 32143885320038087455752371)
                ·
                  refine ⟨48215827980057131183628557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32143885320038087455752371 48215827980057131183628557)
                  ·
                    refine ⟨18080935492521424193860709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48215827980057131183628557 18080935492521424193860709)
                    ·
                      refine ⟨3390175404847767036348883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18080935492521424193860709 3390175404847767036348883)
                      ·
                        rfl

theorem cell23_6602343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6602343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602343 prefixEnd_6602343 := by exact prefixLift 6602343
  have htrace : WordTrace (prefixWord ++ tailWord_6602343) baseStart_6602343 baseEnd_6602343 := by
    simpa [prefixWord, tailWord_6602343, baseEnd_6602343] using wordTrace_append hprefix tailTrace_6602343
  have hstable : (prefixWord ++ tailWord_6602343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602343).length < 2 ^ (prefixWord ++ tailWord_6602343).sum := by decide
  have hdescent : baseEnd_6602343 < baseStart_6602343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602393 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_6602393 : Nat := 118140960795 + 6602393 * 2 ^ 59
def prefixEnd_6602393 : Nat := 4983230072969 + 3 ^ 40 * 6602393 * 2
def baseEnd_6602393 : Nat := 3390201078880491840723653

theorem tailTrace_6602393 : CollatzResearch.WordTrace tailWord_6602393 prefixEnd_6602393 3390201078880491840723653 := by
  unfold tailWord_6602393
  simp only [CollatzResearch.WordTrace]
  refine ⟨240809055969665234796771833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160539370646443489864514555 240809055969665234796771833)
  ·
    refine ⟨180606791977248926097578875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240809055969665234796771833 180606791977248926097578875)
    ·
      refine ⟨270910187965873389146368313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180606791977248926097578875 270910187965873389146368313)
      ·
        refine ⟨203182640974405041859776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270910187965873389146368313 203182640974405041859776235)
        ·
          refine ⟨304773961461607562789664353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203182640974405041859776235 304773961461607562789664353)
          ·
            refine ⟨228580471096205672092248265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304773961461607562789664353 228580471096205672092248265)
            ·
              refine ⟨171435353322154254069186199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228580471096205672092248265 171435353322154254069186199)
              ·
                refine ⟨257153029983231381103779299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171435353322154254069186199 257153029983231381103779299)
                ·
                  refine ⟨385729544974847071655668949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257153029983231381103779299 385729544974847071655668949)
                  ·
                    refine ⟨9040536210347978241929741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 385729544974847071655668949 9040536210347978241929741)
                    ·
                      refine ⟨3390201078880491840723653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9040536210347978241929741 3390201078880491840723653)
                      ·
                        rfl

theorem cell23_6602393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_6602393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602393 prefixEnd_6602393 := by exact prefixLift 6602393
  have htrace : WordTrace (prefixWord ++ tailWord_6602393) baseStart_6602393 baseEnd_6602393 := by
    simpa [prefixWord, tailWord_6602393, baseEnd_6602393] using wordTrace_append hprefix tailTrace_6602393
  have hstable : (prefixWord ++ tailWord_6602393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602393).length < 2 ^ (prefixWord ++ tailWord_6602393).sum := by decide
  have hdescent : baseEnd_6602393 < baseStart_6602393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602404 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_6602404 : Nat := 118140960795 + 6602404 * 2 ^ 59
def prefixEnd_6602404 : Nat := 4983230072969 + 3 ^ 40 * 6602404 * 2
def baseEnd_6602404 : Nat := 1130068909055897099228701

theorem tailTrace_6602404 : CollatzResearch.WordTrace tailWord_6602404 prefixEnd_6602404 1130068909055897099228701 := by
  unfold tailWord_6602404
  simp only [CollatzResearch.WordTrace]
  refine ⟨120404728586312691837711133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160539638115083589116948177 120404728586312691837711133)
  ·
    refine ⟨45151773219867259439141675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120404728586312691837711133 45151773219867259439141675)
    ·
      refine ⟨67727659829800889158712513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45151773219867259439141675 67727659829800889158712513)
      ·
        refine ⟨50795744872350666869034385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67727659829800889158712513 50795744872350666869034385)
        ·
          refine ⟨38096808654263000151775789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50795744872350666869034385 38096808654263000151775789)
          ·
            refine ⟨14286303245348625056915921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38096808654263000151775789 14286303245348625056915921)
            ·
              refine ⟨10714727434011468792686941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14286303245348625056915921 10714727434011468792686941)
              ·
                refine ⟨4018022787754300797257603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10714727434011468792686941 4018022787754300797257603)
                ·
                  refine ⟨6027034181631451195886405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018022787754300797257603 6027034181631451195886405)
                  ·
                    refine ⟨1130068909055897099228701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027034181631451195886405 1130068909055897099228701)
                    ·
                      rfl

theorem cell23_6602404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_6602404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602404 prefixEnd_6602404 := by exact prefixLift 6602404
  have htrace : WordTrace (prefixWord ++ tailWord_6602404) baseStart_6602404 baseEnd_6602404 := by
    simpa [prefixWord, tailWord_6602404, baseEnd_6602404] using wordTrace_append hprefix tailTrace_6602404
  have hstable : (prefixWord ++ tailWord_6602404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602404).length < 2 ^ (prefixWord ++ tailWord_6602404).sum := by decide
  have hdescent : baseEnd_6602404 < baseStart_6602404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602471 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6602471 : Nat := 118140960795 + 6602471 * 2 ^ 59
def prefixEnd_6602471 : Nat := 4983230072969 + 3 ^ 40 * 6602471 * 2
def baseEnd_6602471 : Nat := 3390241130371542535548295

theorem tailTrace_6602471 : CollatzResearch.WordTrace tailWord_6602471 prefixEnd_6602471 3390241130371542535548295 := by
  unfold tailWord_6602471
  simp only [CollatzResearch.WordTrace]
  refine ⟨240811900863382654118111267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160541267242255102745407511 240811900863382654118111267)
  ·
    refine ⟨361217851295073981177166901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240811900863382654118111267 361217851295073981177166901)
    ·
      refine ⟨33864173558913185735359397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361217851295073981177166901 33864173558913185735359397)
      ·
        refine ⟨6349532542296222325379887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33864173558913185735359397 6349532542296222325379887)
        ·
          refine ⟨9524298813444333488069831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349532542296222325379887 9524298813444333488069831)
          ·
            refine ⟨14286448220166500232104747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524298813444333488069831 14286448220166500232104747)
            ·
              refine ⟨21429672330249750348157121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286448220166500232104747 21429672330249750348157121)
              ·
                refine ⟨16072254247687312761117841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21429672330249750348157121 16072254247687312761117841)
                ·
                  refine ⟨12054190685765484570838381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16072254247687312761117841 12054190685765484570838381)
                  ·
                    refine ⟨4520321507162056714064393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12054190685765484570838381 4520321507162056714064393)
                    ·
                      refine ⟨3390241130371542535548295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520321507162056714064393 3390241130371542535548295)
                      ·
                        rfl

theorem cell23_6602471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6602471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602471 prefixEnd_6602471 := by exact prefixLift 6602471
  have htrace : WordTrace (prefixWord ++ tailWord_6602471) baseStart_6602471 baseEnd_6602471 := by
    simpa [prefixWord, tailWord_6602471, baseEnd_6602471] using wordTrace_append hprefix tailTrace_6602471
  have hstable : (prefixWord ++ tailWord_6602471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602471).length < 2 ^ (prefixWord ++ tailWord_6602471).sum := by decide
  have hdescent : baseEnd_6602471 < baseStart_6602471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602477 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_6602477 : Nat := 118140960795 + 6602477 * 2 ^ 59
def prefixEnd_6602477 : Nat := 4983230072969 + 3 ^ 40 * 6602477 * 2
def baseEnd_6602477 : Nat := 1130081403751823170691089

theorem tailTrace_6602477 : CollatzResearch.WordTrace tailWord_6602477 prefixEnd_6602477 1130081403751823170691089 := by
  unfold tailWord_6602477
  simp only [CollatzResearch.WordTrace]
  refine ⟨240812119701360917142829685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160541413134240611428553123 240812119701360917142829685)
  ·
    refine ⟨22576136222002585982140283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240812119701360917142829685 22576136222002585982140283)
    ·
      refine ⟨33864204333003878973210425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22576136222002585982140283 33864204333003878973210425)
      ·
        refine ⟨25398153249752909229907819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33864204333003878973210425 25398153249752909229907819)
        ·
          refine ⟨38097229874629363844861729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25398153249752909229907819 38097229874629363844861729)
          ·
            refine ⟨28572922405972022883646297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38097229874629363844861729 28572922405972022883646297)
            ·
              refine ⟨21429691804479017162734723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28572922405972022883646297 21429691804479017162734723)
              ·
                refine ⟨32144537706718525744102085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21429691804479017162734723 32144537706718525744102085)
                ·
                  refine ⟨6027100820009723577019141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32144537706718525744102085 6027100820009723577019141)
                  ·
                    refine ⟨1130081403751823170691089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027100820009723577019141 1130081403751823170691089)
                    ·
                      rfl

theorem cell23_6602477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_6602477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602477 prefixEnd_6602477 := by exact prefixLift 6602477
  have htrace : WordTrace (prefixWord ++ tailWord_6602477) baseStart_6602477 baseEnd_6602477 := by
    simpa [prefixWord, tailWord_6602477, baseEnd_6602477] using wordTrace_append hprefix tailTrace_6602477
  have hstable : (prefixWord ++ tailWord_6602477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602477).length < 2 ^ (prefixWord ++ tailWord_6602477).sum := by decide
  have hdescent : baseEnd_6602477 < baseStart_6602477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602514 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6602514 : Nat := 118140960795 + 6602514 * 2 ^ 59
def prefixEnd_6602514 : Nat := 4983230072969 + 3 ^ 40 * 6602514 * 2
def baseEnd_6602514 : Nat := 3390263210039685867310597

theorem tailTrace_6602514 : CollatzResearch.WordTrace tailWord_6602514 prefixEnd_6602514 3390263210039685867310597 := by
  unfold tailWord_6602514
  simp only [CollatzResearch.WordTrace]
  refine ⟨60203367300556718115481649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160542312801484581641284397 60203367300556718115481649)
  ·
    refine ⟨45152525475417538586611237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60203367300556718115481649 45152525475417538586611237)
    ·
      refine ⟨8466098526640788484989607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45152525475417538586611237 8466098526640788484989607)
      ·
        refine ⟨12699147789961182727484411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466098526640788484989607 12699147789961182727484411)
        ·
          refine ⟨19048721684941774091226617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699147789961182727484411 19048721684941774091226617)
          ·
            refine ⟨14286541263706330568419963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19048721684941774091226617 14286541263706330568419963)
            ·
              refine ⟨21429811895559495852629945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286541263706330568419963 21429811895559495852629945)
              ·
                refine ⟨16072358921669621889472459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21429811895559495852629945 16072358921669621889472459)
                ·
                  refine ⟨24108538382504432834208689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16072358921669621889472459 24108538382504432834208689)
                  ·
                    refine ⟨18081403786878324625656517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24108538382504432834208689 18081403786878324625656517)
                    ·
                      refine ⟨3390263210039685867310597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18081403786878324625656517 3390263210039685867310597)
                      ·
                        rfl

theorem cell23_6602514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6602514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602514 prefixEnd_6602514 := by exact prefixLift 6602514
  have htrace : WordTrace (prefixWord ++ tailWord_6602514) baseStart_6602514 baseEnd_6602514 := by
    simpa [prefixWord, tailWord_6602514, baseEnd_6602514] using wordTrace_append hprefix tailTrace_6602514
  have hstable : (prefixWord ++ tailWord_6602514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602514).length < 2 ^ (prefixWord ++ tailWord_6602514).sum := by decide
  have hdescent : baseEnd_6602514 < baseStart_6602514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602517 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_6602517 : Nat := 118140960795 + 6602517 * 2 ^ 59
def prefixEnd_6602517 : Nat := 4983230072969 + 3 ^ 40 * 6602517 * 2
def baseEnd_6602517 : Nat := 3390264750481649355573083

theorem tailTrace_6602517 : CollatzResearch.WordTrace tailWord_6602517 prefixEnd_6602517 3390264750481649355573083 := by
  unfold tailWord_6602517
  simp only [CollatzResearch.WordTrace]
  refine ⟨240813578621216003974285805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160542385747477335982857203 240813578621216003974285805)
  ·
    refine ⟨90305091982956001490357177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240813578621216003974285805 90305091982956001490357177)
    ·
      refine ⟨67728818987217001117767883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90305091982956001490357177 67728818987217001117767883)
      ·
        refine ⟨101593228480825501676651825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67728818987217001117767883 101593228480825501676651825)
        ·
          refine ⟨76194921360619126257488869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101593228480825501676651825 76194921360619126257488869)
          ·
            refine ⟨14286547755116086173279163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76194921360619126257488869 14286547755116086173279163)
            ·
              refine ⟨21429821632674129259918745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286547755116086173279163 21429821632674129259918745)
              ·
                refine ⟨16072366224505596944939059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21429821632674129259918745 16072366224505596944939059)
                ·
                  refine ⟨24108549336758395417408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16072366224505596944939059 24108549336758395417408589)
                  ·
                    refine ⟨9040706001284398281528221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24108549336758395417408589 9040706001284398281528221)
                    ·
                      refine ⟨3390264750481649355573083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9040706001284398281528221 3390264750481649355573083)
                      ·
                        rfl

theorem cell23_6602517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_6602517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602517 prefixEnd_6602517 := by exact prefixLift 6602517
  have htrace : WordTrace (prefixWord ++ tailWord_6602517) baseStart_6602517 baseEnd_6602517 := by
    simpa [prefixWord, tailWord_6602517, baseEnd_6602517] using wordTrace_append hprefix tailTrace_6602517
  have hstable : (prefixWord ++ tailWord_6602517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602517).length < 2 ^ (prefixWord ++ tailWord_6602517).sum := by decide
  have hdescent : baseEnd_6602517 < baseStart_6602517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602523 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_6602523 : Nat := 118140960795 + 6602523 * 2 ^ 59
def prefixEnd_6602523 : Nat := 4983230072969 + 3 ^ 40 * 6602523 * 2
def baseEnd_6602523 : Nat := 3390267831365576332098055

theorem tailTrace_6602523 : CollatzResearch.WordTrace tailWord_6602523 prefixEnd_6602523 3390267831365576332098055 := by
  unfold tailWord_6602523
  simp only [CollatzResearch.WordTrace]
  refine ⟨240813797459194266999004223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160542531639462844666002815 240813797459194266999004223)
  ·
    refine ⟨361220696188791400498506335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240813797459194266999004223 361220696188791400498506335)
    ·
      refine ⟨541831044283187100747759503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361220696188791400498506335 541831044283187100747759503)
      ·
        refine ⟨812746566424780651121639255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541831044283187100747759503 812746566424780651121639255)
        ·
          refine ⟨1219119849637170976682458883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812746566424780651121639255 1219119849637170976682458883)
          ·
            refine ⟨1828679774455756465023688325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219119849637170976682458883 1828679774455756465023688325)
            ·
              refine ⟨342877457710454337191941561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1828679774455756465023688325 342877457710454337191941561)
              ·
                refine ⟨257158093282840752893956171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342877457710454337191941561 257158093282840752893956171)
                ·
                  refine ⟨385737139924261129340934257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257158093282840752893956171 385737139924261129340934257)
                  ·
                    refine ⟨289302854943195847005700693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385737139924261129340934257 289302854943195847005700693)
                    ·
                      refine ⟨3390267831365576332098055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289302854943195847005700693 3390267831365576332098055)
                      ·
                        rfl

theorem cell23_6602523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_6602523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602523 prefixEnd_6602523 := by exact prefixLift 6602523
  have htrace : WordTrace (prefixWord ++ tailWord_6602523) baseStart_6602523 baseEnd_6602523 := by
    simpa [prefixWord, tailWord_6602523, baseEnd_6602523] using wordTrace_append hprefix tailTrace_6602523
  have hstable : (prefixWord ++ tailWord_6602523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602523).length < 2 ^ (prefixWord ++ tailWord_6602523).sum := by decide
  have hdescent : baseEnd_6602523 < baseStart_6602523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602540 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_6602540 : Nat := 118140960795 + 6602540 * 2 ^ 59
def prefixEnd_6602540 : Nat := 4983230072969 + 3 ^ 40 * 6602540 * 2
def baseEnd_6602540 : Nat := 3390276560536702765585477

theorem tailTrace_6602540 : CollatzResearch.WordTrace tailWord_6602540 prefixEnd_6602540 3390276560536702765585477 := by
  unfold tailWord_6602540
  simp only [CollatzResearch.WordTrace]
  refine ⟨120407208750066339451186537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160542945000088452601582049 120407208750066339451186537)
  ·
    refine ⟨90305406562549754588389903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120407208750066339451186537 90305406562549754588389903)
    ·
      refine ⟨135458109843824631882584855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90305406562549754588389903 135458109843824631882584855)
      ·
        refine ⟨203187164765736947823877283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135458109843824631882584855 203187164765736947823877283)
        ·
          refine ⟨304780747148605421735815925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203187164765736947823877283 304780747148605421735815925)
          ·
            refine ⟨28573195045181758287732743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304780747148605421735815925 28573195045181758287732743)
            ·
              refine ⟨42859792567772637431599115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28573195045181758287732743 42859792567772637431599115)
              ·
                refine ⟨64289688851658956147398673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42859792567772637431599115 64289688851658956147398673)
                ·
                  refine ⟨48217266638744217110549005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64289688851658956147398673 48217266638744217110549005)
                  ·
                    refine ⟨18081474989529081416455877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48217266638744217110549005 18081474989529081416455877)
                    ·
                      refine ⟨3390276560536702765585477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18081474989529081416455877 3390276560536702765585477)
                      ·
                        rfl

theorem cell23_6602540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_6602540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602540 prefixEnd_6602540 := by exact prefixLift 6602540
  have htrace : WordTrace (prefixWord ++ tailWord_6602540) baseStart_6602540 baseEnd_6602540 := by
    simpa [prefixWord, tailWord_6602540, baseEnd_6602540] using wordTrace_append hprefix tailTrace_6602540
  have hstable : (prefixWord ++ tailWord_6602540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602540).length < 2 ^ (prefixWord ++ tailWord_6602540).sum := by decide
  have hdescent : baseEnd_6602540 < baseStart_6602540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602570 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_6602570 : Nat := 118140960795 + 6602570 * 2 ^ 59
def prefixEnd_6602570 : Nat := 4983230072969 + 3 ^ 40 * 6602570 * 2
def baseEnd_6602570 : Nat := 3390291964956337648210339

theorem tailTrace_6602570 : CollatzResearch.WordTrace tailWord_6602570 prefixEnd_6602570 3390291964956337648210339 := by
  unfold tailWord_6602570
  simp only [CollatzResearch.WordTrace]
  refine ⟨60203877922505998506491291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160543674460015996017310109 60203877922505998506491291)
  ·
    refine ⟨90305816883758997759736937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60203877922505998506491291 90305816883758997759736937)
    ·
      refine ⟨67729362662819248319802703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90305816883758997759736937 67729362662819248319802703)
      ·
        refine ⟨101594043994228872479704055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67729362662819248319802703 101594043994228872479704055)
        ·
          refine ⟨152391065991343308719556083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101594043994228872479704055 152391065991343308719556083)
          ·
            refine ⟨228586598987014963079334125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152391065991343308719556083 228586598987014963079334125)
            ·
              refine ⟨85719974620130611154750297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228586598987014963079334125 85719974620130611154750297)
              ·
                refine ⟨64289980965097958366062723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85719974620130611154750297 64289980965097958366062723)
                ·
                  refine ⟨96434971447646937549094085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64289980965097958366062723 96434971447646937549094085)
                  ·
                    refine ⟨18081557146433800790455141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96434971447646937549094085 18081557146433800790455141)
                    ·
                      refine ⟨3390291964956337648210339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18081557146433800790455141 3390291964956337648210339)
                      ·
                        rfl

theorem cell23_6602570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_6602570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602570 prefixEnd_6602570 := by exact prefixLift 6602570
  have htrace : WordTrace (prefixWord ++ tailWord_6602570) baseStart_6602570 baseEnd_6602570 := by
    simpa [prefixWord, tailWord_6602570, baseEnd_6602570] using wordTrace_append hprefix tailTrace_6602570
  have hstable : (prefixWord ++ tailWord_6602570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602570).length < 2 ^ (prefixWord ++ tailWord_6602570).sum := by decide
  have hdescent : baseEnd_6602570 < baseStart_6602570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602578 : List Nat := [3, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_6602578 : Nat := 118140960795 + 6602578 * 2 ^ 59
def prefixEnd_6602578 : Nat := 4983230072969 + 3 ^ 40 * 6602578 * 2
def baseEnd_6602578 : Nat := 3390296072801573616910303

theorem tailTrace_6602578 : CollatzResearch.WordTrace tailWord_6602578 prefixEnd_6602578 3390296072801573616910303 := by
  unfold tailWord_6602578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60203950868498752848064097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160543868982663340928170925 60203950868498752848064097)
  ·
    refine ⟨45152963151374064636048073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60203950868498752848064097 45152963151374064636048073)
    ·
      refine ⟨33864722363530548477036055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45152963151374064636048073 33864722363530548477036055)
      ·
        refine ⟨50797083545295822715554083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33864722363530548477036055 50797083545295822715554083)
        ·
          refine ⟨76195625317943734073331125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50797083545295822715554083 76195625317943734073331125)
          ·
            refine ⟨7143339873557225069374793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76195625317943734073331125 7143339873557225069374793)
            ·
              refine ⟨5357504905167918802031095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143339873557225069374793 5357504905167918802031095)
              ·
                refine ⟨8036257357751878203046643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357504905167918802031095 8036257357751878203046643)
                ·
                  refine ⟨12054386036627817304569965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036257357751878203046643 12054386036627817304569965)
                  ·
                    refine ⟨4520394763735431489213737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12054386036627817304569965 4520394763735431489213737)
                    ·
                      refine ⟨3390296072801573616910303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520394763735431489213737 3390296072801573616910303)
                      ·
                        rfl

theorem cell23_6602578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_6602578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602578 prefixEnd_6602578 := by exact prefixLift 6602578
  have htrace : WordTrace (prefixWord ++ tailWord_6602578) baseStart_6602578 baseEnd_6602578 := by
    simpa [prefixWord, tailWord_6602578, baseEnd_6602578] using wordTrace_append hprefix tailTrace_6602578
  have hstable : (prefixWord ++ tailWord_6602578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602578).length < 2 ^ (prefixWord ++ tailWord_6602578).sum := by decide
  have hdescent : baseEnd_6602578 < baseStart_6602578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602591 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 2, 2, 2]
def baseStart_6602591 : Nat := 118140960795 + 6602591 * 2 ^ 59
def prefixEnd_6602591 : Nat := 4983230072969 + 3 ^ 40 * 6602591 * 2
def baseEnd_6602591 : Nat := 3390302748050082066047743

theorem tailTrace_6602591 : CollatzResearch.WordTrace tailWord_6602591 prefixEnd_6602591 3390302748050082066047743 := by
  unfold tailWord_6602591
  simp only [CollatzResearch.WordTrace]
  refine ⟨240816277622947914612479627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160544185081965276408319751 240816277622947914612479627)
  ·
    refine ⟨361224416434421871918719441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240816277622947914612479627 361224416434421871918719441)
    ·
      refine ⟨270918312325816403939039581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361224416434421871918719441 270918312325816403939039581)
      ·
        refine ⟨101594367122181151477139843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270918312325816403939039581 101594367122181151477139843)
        ·
          refine ⟨152391550683271727215709765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101594367122181151477139843 152391550683271727215709765)
          ·
            refine ⟨28573415753113448852945581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152391550683271727215709765 28573415753113448852945581)
            ·
              refine ⟨10715030907417543319854593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28573415753113448852945581 10715030907417543319854593)
              ·
                refine ⟨8036273180563157489890945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10715030907417543319854593 8036273180563157489890945)
                ·
                  refine ⟨6027204885422368117418209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036273180563157489890945 6027204885422368117418209)
                  ·
                    refine ⟨4520403664066776088063657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6027204885422368117418209 4520403664066776088063657)
                    ·
                      refine ⟨3390302748050082066047743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520403664066776088063657 3390302748050082066047743)
                      ·
                        rfl

theorem cell23_6602591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_6602591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602591 prefixEnd_6602591 := by exact prefixLift 6602591
  have htrace : WordTrace (prefixWord ++ tailWord_6602591) baseStart_6602591 baseEnd_6602591 := by
    simpa [prefixWord, tailWord_6602591, baseEnd_6602591] using wordTrace_append hprefix tailTrace_6602591
  have hstable : (prefixWord ++ tailWord_6602591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602591).length < 2 ^ (prefixWord ++ tailWord_6602591).sum := by decide
  have hdescent : baseEnd_6602591 < baseStart_6602591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602620 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_6602620 : Nat := 118140960795 + 6602620 * 2 ^ 59
def prefixEnd_6602620 : Nat := 4983230072969 + 3 ^ 40 * 6602620 * 2
def baseEnd_6602620 : Nat := 3390317638989062452585109

theorem tailTrace_6602620 : CollatzResearch.WordTrace tailWord_6602620 prefixEnd_6602620 3390317638989062452585109 := by
  unfold tailWord_6602620
  simp only [CollatzResearch.WordTrace]
  refine ⟨120408667669921426282642657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160544890226561901710190209 120408667669921426282642657)
  ·
    refine ⟨90306500752441069711981993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120408667669921426282642657 90306500752441069711981993)
    ·
      refine ⟨67729875564330802283986495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90306500752441069711981993 67729875564330802283986495)
      ·
        refine ⟨101594813346496203425979743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67729875564330802283986495 101594813346496203425979743)
        ·
          refine ⟨152392220019744305138969615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101594813346496203425979743 152392220019744305138969615)
          ·
            refine ⟨228588330029616457708454423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152392220019744305138969615 228588330029616457708454423)
            ·
              refine ⟨342882495044424686562681635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228588330029616457708454423 342882495044424686562681635)
              ·
                refine ⟨514323742566637029844022453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342882495044424686562681635 514323742566637029844022453)
                ·
                  refine ⟨48217850865622221547877105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514323742566637029844022453 48217850865622221547877105)
                  ·
                    refine ⟨36163388149216666160907829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48217850865622221547877105 36163388149216666160907829)
                    ·
                      refine ⟨3390317638989062452585109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36163388149216666160907829 3390317638989062452585109)
                      ·
                        rfl

theorem cell23_6602620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_6602620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602620 prefixEnd_6602620 := by exact prefixLift 6602620
  have htrace : WordTrace (prefixWord ++ tailWord_6602620) baseStart_6602620 baseEnd_6602620 := by
    simpa [prefixWord, tailWord_6602620, baseEnd_6602620] using wordTrace_append hprefix tailTrace_6602620
  have hstable : (prefixWord ++ tailWord_6602620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602620).length < 2 ^ (prefixWord ++ tailWord_6602620).sum := by decide
  have hdescent : baseEnd_6602620 < baseStart_6602620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602631 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 5]
def baseStart_6602631 : Nat := 118140960795 + 6602631 * 2 ^ 59
def prefixEnd_6602631 : Nat := 4983230072969 + 3 ^ 40 * 6602631 * 2
def baseEnd_6602631 : Nat := 376702587475140212171951

theorem tailTrace_6602631 : CollatzResearch.WordTrace tailWord_6602631 prefixEnd_6602631 376702587475140212171951 := by
  unfold tailWord_6602631
  simp only [CollatzResearch.WordTrace]
  refine ⟨240817736542803001443935747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160545157695202000962623831 240817736542803001443935747)
  ·
    refine ⟨361226604814204502165903621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240817736542803001443935747 361226604814204502165903621)
    ·
      refine ⟨67729988402663344156106929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361226604814204502165903621 67729988402663344156106929)
      ·
        refine ⟨50797491301997508117080197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67729988402663344156106929 50797491301997508117080197)
        ·
          refine ⟨9524529619124532771952537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50797491301997508117080197 9524529619124532771952537)
          ·
            refine ⟨7143397214343399578964403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524529619124532771952537 7143397214343399578964403)
            ·
              refine ⟨10715095821515099368446605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143397214343399578964403 10715095821515099368446605)
              ·
                refine ⟨4018160933068162263167477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10715095821515099368446605 4018160933068162263167477)
                ·
                  refine ⟨376702587475140212171951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4018160933068162263167477 376702587475140212171951)
                  ·
                    rfl

theorem cell23_6602631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 5].length) (baseStart_6602631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602631 prefixEnd_6602631 := by exact prefixLift 6602631
  have htrace : WordTrace (prefixWord ++ tailWord_6602631) baseStart_6602631 baseEnd_6602631 := by
    simpa [prefixWord, tailWord_6602631, baseEnd_6602631] using wordTrace_append hprefix tailTrace_6602631
  have hstable : (prefixWord ++ tailWord_6602631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602631).length < 2 ^ (prefixWord ++ tailWord_6602631).sum := by decide
  have hdescent : baseEnd_6602631 < baseStart_6602631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602644 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6602644 : Nat := 118140960795 + 6602644 * 2 ^ 59
def prefixEnd_6602644 : Nat := 4983230072969 + 3 ^ 40 * 6602644 * 2
def baseEnd_6602644 : Nat := 1130109987508256786228333

theorem tailTrace_6602644 : CollatzResearch.WordTrace tailWord_6602644 prefixEnd_6602644 1130109987508256786228333 := by
  unfold tailWord_6602644
  simp only [CollatzResearch.WordTrace]
  refine ⟨120409105345877952332079493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160545473794503936442772657 120409105345877952332079493)
  ·
    refine ⟨22576707252352116062264905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120409105345877952332079493 22576707252352116062264905)
    ·
      refine ⟨16932530439264087046698679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22576707252352116062264905 16932530439264087046698679)
      ·
        refine ⟨25398795658896130570048019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16932530439264087046698679 25398795658896130570048019)
        ·
          refine ⟨38098193488344195855072029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25398795658896130570048019 38098193488344195855072029)
          ·
            refine ⟨14286822558129073445652011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38098193488344195855072029 14286822558129073445652011)
            ·
              refine ⟨21430233837193610168478017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286822558129073445652011 21430233837193610168478017)
              ·
                refine ⟨16072675377895207626358513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21430233837193610168478017 16072675377895207626358513)
                ·
                  refine ⟨12054506533421405719768885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16072675377895207626358513 12054506533421405719768885)
                  ·
                    refine ⟨1130109987508256786228333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12054506533421405719768885 1130109987508256786228333)
                    ·
                      rfl

theorem cell23_6602644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6602644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602644 prefixEnd_6602644 := by exact prefixLift 6602644
  have htrace : WordTrace (prefixWord ++ tailWord_6602644) baseStart_6602644 baseEnd_6602644 := by
    simpa [prefixWord, tailWord_6602644, baseEnd_6602644] using wordTrace_append hprefix tailTrace_6602644
  have hstable : (prefixWord ++ tailWord_6602644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602644).length < 2 ^ (prefixWord ++ tailWord_6602644).sum := by decide
  have hdescent : baseEnd_6602644 < baseStart_6602644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602647 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_6602647 : Nat := 118140960795 + 6602647 * 2 ^ 59
def prefixEnd_6602647 : Nat := 4983230072969 + 3 ^ 40 * 6602647 * 2
def baseEnd_6602647 : Nat := 3390331502966733846947485

theorem tailTrace_6602647 : CollatzResearch.WordTrace tailWord_6602647 prefixEnd_6602647 3390331502966733846947485 := by
  unfold tailWord_6602647
  simp only [CollatzResearch.WordTrace]
  refine ⟨240818320110745036176518195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160545546740496690784345463 240818320110745036176518195)
  ·
    refine ⟨361227480166117554264777293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240818320110745036176518195 361227480166117554264777293)
    ·
      refine ⟨135460305062294082849291485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361227480166117554264777293 135460305062294082849291485)
      ·
        refine ⟨50797614398360281068484307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135460305062294082849291485 50797614398360281068484307)
        ·
          refine ⟨76196421597540421602726461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50797614398360281068484307 76196421597540421602726461)
          ·
            refine ⟨28573658099077658101022423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76196421597540421602726461 28573658099077658101022423)
            ·
              refine ⟨42860487148616487151533635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28573658099077658101022423 42860487148616487151533635)
              ·
                refine ⟨64290730722924730727300453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42860487148616487151533635 64290730722924730727300453)
                ·
                  refine ⟨12054512010548387011368835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64290730722924730727300453 12054512010548387011368835)
                  ·
                    refine ⟨18081768015822580517053253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12054512010548387011368835 18081768015822580517053253)
                    ·
                      refine ⟨3390331502966733846947485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18081768015822580517053253 3390331502966733846947485)
                      ·
                        rfl

theorem cell23_6602647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_6602647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602647 prefixEnd_6602647 := by exact prefixLift 6602647
  have htrace : WordTrace (prefixWord ++ tailWord_6602647) baseStart_6602647 baseEnd_6602647 := by
    simpa [prefixWord, tailWord_6602647, baseEnd_6602647] using wordTrace_append hprefix tailTrace_6602647
  have hstable : (prefixWord ++ tailWord_6602647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602647).length < 2 ^ (prefixWord ++ tailWord_6602647).sum := by decide
  have hdescent : baseEnd_6602647 < baseStart_6602647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602648 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 5]
def baseStart_6602648 : Nat := 118140960795 + 6602648 * 2 ^ 59
def prefixEnd_6602648 : Nat := 4983230072969 + 3 ^ 40 * 6602648 * 2
def baseEnd_6602648 : Nat := 376703557383043149226109

theorem tailTrace_6602648 : CollatzResearch.WordTrace tailWord_6602648 prefixEnd_6602648 376703557383043149226109 := by
  unfold tailWord_6602648
  simp only [CollatzResearch.WordTrace]
  refine ⟨120409178291870706673652299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160545571055827608898203065 120409178291870706673652299)
  ·
    refine ⟨180613767437806060010478449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120409178291870706673652299 180613767437806060010478449)
    ·
      refine ⟨135460325578354545007858837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180613767437806060010478449 135460325578354545007858837)
      ·
        refine ⟨6349702761485369297243383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135460325578354545007858837 6349702761485369297243383)
        ·
          refine ⟨9524554142228053945865075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349702761485369297243383 9524554142228053945865075)
          ·
            refine ⟨14286831213342080918797613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524554142228053945865075 14286831213342080918797613)
            ·
              refine ⟨5357561705003280344549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14286831213342080918797613 5357561705003280344549105)
              ·
                refine ⟨4018171278752460258411829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357561705003280344549105 4018171278752460258411829)
                ·
                  refine ⟨376703557383043149226109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4018171278752460258411829 376703557383043149226109)
                  ·
                    rfl

theorem cell23_6602648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 5].length) (baseStart_6602648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602648 prefixEnd_6602648 := by exact prefixLift 6602648
  have htrace : WordTrace (prefixWord ++ tailWord_6602648) baseStart_6602648 baseEnd_6602648 := by
    simpa [prefixWord, tailWord_6602648, baseEnd_6602648] using wordTrace_append hprefix tailTrace_6602648
  have hstable : (prefixWord ++ tailWord_6602648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602648).length < 2 ^ (prefixWord ++ tailWord_6602648).sum := by decide
  have hdescent : baseEnd_6602648 < baseStart_6602648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602724 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_6602724 : Nat := 118140960795 + 6602724 * 2 ^ 59
def prefixEnd_6602724 : Nat := 4983230072969 + 3 ^ 40 * 6602724 * 2
def baseEnd_6602724 : Nat := 3390371040977130045684631

theorem tailTrace_6602724 : CollatzResearch.WordTrace tailWord_6602724 prefixEnd_6602724 3390371040977130045684631 := by
  unfold tailWord_6602724
  simp only [CollatzResearch.WordTrace]
  refine ⟨120410564265733039163535613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160547419020977385551380817 120410564265733039163535613)
  ·
    refine ⟨45153961599649889686325855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120410564265733039163535613 45153961599649889686325855)
    ·
      refine ⟨67730942399474834529488783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45153961599649889686325855 67730942399474834529488783)
      ·
        refine ⟨101596413599212251794233175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67730942399474834529488783 101596413599212251794233175)
        ·
          refine ⟨152394620398818377691349763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101596413599212251794233175 152394620398818377691349763)
          ·
            refine ⟨228591930598227566537024645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152394620398818377691349763 228591930598227566537024645)
            ·
              refine ⟨42860986987167668725692121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228591930598227566537024645 42860986987167668725692121)
              ·
                refine ⟨32145740240375751544269091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42860986987167668725692121 32145740240375751544269091)
                ·
                  refine ⟨48218610360563627316403637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32145740240375751544269091 48218610360563627316403637)
                  ·
                    refine ⟨4520494721302840060912841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48218610360563627316403637 4520494721302840060912841)
                    ·
                      refine ⟨3390371040977130045684631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520494721302840060912841 3390371040977130045684631)
                      ·
                        rfl

theorem cell23_6602724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_6602724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602724 prefixEnd_6602724 := by exact prefixLift 6602724
  have htrace : WordTrace (prefixWord ++ tailWord_6602724) baseStart_6602724 baseEnd_6602724 := by
    simpa [prefixWord, tailWord_6602724, baseEnd_6602724] using wordTrace_append hprefix tailTrace_6602724
  have hstable : (prefixWord ++ tailWord_6602724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602724).length < 2 ^ (prefixWord ++ tailWord_6602724).sum := by decide
  have hdescent : baseEnd_6602724 < baseStart_6602724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602734 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6602734 : Nat := 118140960795 + 6602734 * 2 ^ 59
def prefixEnd_6602734 : Nat := 4983230072969 + 3 ^ 40 * 6602734 * 2
def baseEnd_6602734 : Nat := 1130125391927891668853195

theorem tailTrace_6602734 : CollatzResearch.WordTrace tailWord_6602734 prefixEnd_6602734 1130125391927891668853195 := by
  unfold tailWord_6602734
  simp only [CollatzResearch.WordTrace]
  refine ⟨30102686657678731254366907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160547662174286566689956837 30102686657678731254366907)
  ·
    refine ⟨45154029986518096881550361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30102686657678731254366907 45154029986518096881550361)
    ·
      refine ⟨33865522489888572661162771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45154029986518096881550361 33865522489888572661162771)
      ·
        refine ⟨50798283734832858991744157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33865522489888572661162771 50798283734832858991744157)
        ·
          refine ⟨19049356400562322121904059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50798283734832858991744157 19049356400562322121904059)
          ·
            refine ⟨28574034600843483182856089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19049356400562322121904059 28574034600843483182856089)
            ·
              refine ⟨21430525950632612387142067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28574034600843483182856089 21430525950632612387142067)
              ·
                refine ⟨32145788925948918580713101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21430525950632612387142067 32145788925948918580713101)
                ·
                  refine ⟨12054670847230844467767413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32145788925948918580713101 12054670847230844467767413)
                  ·
                    refine ⟨1130125391927891668853195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12054670847230844467767413 1130125391927891668853195)
                    ·
                      rfl

theorem cell23_6602734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6602734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602734 prefixEnd_6602734 := by exact prefixLift 6602734
  have htrace : WordTrace (prefixWord ++ tailWord_6602734) baseStart_6602734 baseEnd_6602734 := by
    simpa [prefixWord, tailWord_6602734, baseEnd_6602734] using wordTrace_append hprefix tailTrace_6602734
  have hstable : (prefixWord ++ tailWord_6602734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602734).length < 2 ^ (prefixWord ++ tailWord_6602734).sum := by decide
  have hdescent : baseEnd_6602734 < baseStart_6602734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602747 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 6]
def baseStart_6602747 : Nat := 118140960795 + 6602747 * 2 ^ 59
def prefixEnd_6602747 : Nat := 4983230072969 + 3 ^ 40 * 6602747 * 2
def baseEnd_6602747 : Nat := 1130127617010727818565675

theorem tailTrace_6602747 : CollatzResearch.WordTrace tailWord_6602747 prefixEnd_6602747 1130127617010727818565675 := by
  unfold tailWord_6602747
  simp only [CollatzResearch.WordTrace]
  refine ⟨240821967410382753255158495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160547978273588502170105663 240821967410382753255158495)
  ·
    refine ⟨361232951115574129882737743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240821967410382753255158495 361232951115574129882737743)
    ·
      refine ⟨541849426673361194824106615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361232951115574129882737743 541849426673361194824106615)
      ·
        refine ⟨812774140010041792236159923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541849426673361194824106615 812774140010041792236159923)
        ·
          refine ⟨1219161210015062688354239885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812774140010041792236159923 1219161210015062688354239885)
          ·
            refine ⟨457185453755648508132839957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1219161210015062688354239885 457185453755648508132839957)
            ·
              refine ⟨21430568144796023818726873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 457185453755648508132839957 21430568144796023818726873)
              ·
                refine ⟨16072926108597017864045155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21430568144796023818726873 16072926108597017864045155)
                ·
                  refine ⟨24109389162895526796067733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16072926108597017864045155 24109389162895526796067733)
                  ·
                    refine ⟨1130127617010727818565675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24109389162895526796067733 1130127617010727818565675)
                    ·
                      rfl

theorem cell23_6602747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_6602747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602747 prefixEnd_6602747 := by exact prefixLift 6602747
  have htrace : WordTrace (prefixWord ++ tailWord_6602747) baseStart_6602747 baseEnd_6602747 := by
    simpa [prefixWord, tailWord_6602747, baseEnd_6602747] using wordTrace_append hprefix tailTrace_6602747
  have hstable : (prefixWord ++ tailWord_6602747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602747).length < 2 ^ (prefixWord ++ tailWord_6602747).sum := by decide
  have hdescent : baseEnd_6602747 < baseStart_6602747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602748 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_6602748 : Nat := 118140960795 + 6602748 * 2 ^ 59
def prefixEnd_6602748 : Nat := 4983230072969 + 3 ^ 40 * 6602748 * 2
def baseEnd_6602748 : Nat := 3390383364512837951784521

theorem tailTrace_6602748 : CollatzResearch.WordTrace tailWord_6602748 prefixEnd_6602748 3390383364512837951784521 := by
  unfold tailWord_6602748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120411001941689565212972449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160548002588919420283963265 120411001941689565212972449)
  ·
    refine ⟨90308251456267173909729337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120411001941689565212972449 90308251456267173909729337)
    ·
      refine ⟨67731188592200380432297003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90308251456267173909729337 67731188592200380432297003)
      ·
        refine ⟨101596782888300570648445505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67731188592200380432297003 101596782888300570648445505)
        ·
          refine ⟨76197587166225427986334129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101596782888300570648445505 76197587166225427986334129)
          ·
            refine ⟨57148190374669070989750597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76197587166225427986334129 57148190374669070989750597)
            ·
              refine ⟨10715285695250450810578237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57148190374669070989750597 10715285695250450810578237)
              ·
                refine ⟨4018232135718919053966839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10715285695250450810578237 4018232135718919053966839)
                ·
                  refine ⟨6027348203578378580950259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018232135718919053966839 6027348203578378580950259)
                  ·
                    refine ⟨9041022305367567871425389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027348203578378580950259 9041022305367567871425389)
                    ·
                      refine ⟨3390383364512837951784521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041022305367567871425389 3390383364512837951784521)
                      ·
                        rfl

theorem cell23_6602748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_6602748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602748 prefixEnd_6602748 := by exact prefixLift 6602748
  have htrace : WordTrace (prefixWord ++ tailWord_6602748) baseStart_6602748 baseEnd_6602748 := by
    simpa [prefixWord, tailWord_6602748, baseEnd_6602748] using wordTrace_append hprefix tailTrace_6602748
  have hstable : (prefixWord ++ tailWord_6602748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602748).length < 2 ^ (prefixWord ++ tailWord_6602748).sum := by decide
  have hdescent : baseEnd_6602748 < baseStart_6602748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602764 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_6602764 : Nat := 118140960795 + 6602764 * 2 ^ 59
def prefixEnd_6602764 : Nat := 4983230072969 + 3 ^ 40 * 6602764 * 2
def baseEnd_6602764 : Nat := 1130130526734436629728149

theorem tailTrace_6602764 : CollatzResearch.WordTrace tailWord_6602764 prefixEnd_6602764 1130130526734436629728149 := by
  unfold tailWord_6602764
  simp only [CollatzResearch.WordTrace]
  refine ⟨120411293725660582579263673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160548391634214110105684897 120411293725660582579263673)
  ·
    refine ⟨90308470294245436934447755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120411293725660582579263673 90308470294245436934447755)
    ·
      refine ⟨135462705441368155401671633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90308470294245436934447755 135462705441368155401671633)
      ·
        refine ⟨101597029081026116551253725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135462705441368155401671633 101597029081026116551253725)
        ·
          refine ⟨38098885905384793706720147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101597029081026116551253725 38098885905384793706720147)
          ·
            refine ⟨57148328858077190560080221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38098885905384793706720147 57148328858077190560080221)
            ·
              refine ⟨21430623321778946460030083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57148328858077190560080221 21430623321778946460030083)
              ·
                refine ⟨32145934982668419690045125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21430623321778946460030083 32145934982668419690045125)
                ·
                  refine ⟨6027362809250328691883461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32145934982668419690045125 6027362809250328691883461)
                  ·
                    refine ⟨1130130526734436629728149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027362809250328691883461 1130130526734436629728149)
                    ·
                      rfl

theorem cell23_6602764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_6602764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602764 prefixEnd_6602764 := by exact prefixLift 6602764
  have htrace : WordTrace (prefixWord ++ tailWord_6602764) baseStart_6602764 baseEnd_6602764 := by
    simpa [prefixWord, tailWord_6602764, baseEnd_6602764] using wordTrace_append hprefix tailTrace_6602764
  have hstable : (prefixWord ++ tailWord_6602764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602764).length < 2 ^ (prefixWord ++ tailWord_6602764).sum := by decide
  have hdescent : baseEnd_6602764 < baseStart_6602764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602771 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 3, 2, 2]
def baseStart_6602771 : Nat := 118140960795 + 6602771 * 2 ^ 59
def prefixEnd_6602771 : Nat := 4983230072969 + 3 ^ 40 * 6602771 * 2
def baseEnd_6602771 : Nat := 3390395174567891361796915

theorem tailTrace_6602771 : CollatzResearch.WordTrace tailWord_6602771 prefixEnd_6602771 3390395174567891361796915 := by
  unfold tailWord_6602771
  simp only [CollatzResearch.WordTrace]
  refine ⟨240822842762295805354032167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160548561841530536902688111 240822842762295805354032167)
  ·
    refine ⟨361234264143443708031048251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240822842762295805354032167 361234264143443708031048251)
    ·
      refine ⟨541851396215165562046572377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361234264143443708031048251 541851396215165562046572377)
      ·
        refine ⟨406388547161374171534929283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541851396215165562046572377 406388547161374171534929283)
        ·
          refine ⟨609582820742061257302393925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406388547161374171534929283 609582820742061257302393925)
          ·
            refine ⟨114296778889136485744198861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609582820742061257302393925 114296778889136485744198861)
            ·
              refine ⟨42861292083426182154074573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114296778889136485744198861 42861292083426182154074573)
              ·
                refine ⟨16072984531284818307777965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42861292083426182154074573 16072984531284818307777965)
                ·
                  refine ⟨6027369199231806865416737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16072984531284818307777965 6027369199231806865416737)
                  ·
                    refine ⟨4520526899423855149062553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6027369199231806865416737 4520526899423855149062553)
                    ·
                      refine ⟨3390395174567891361796915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520526899423855149062553 3390395174567891361796915)
                      ·
                        rfl

theorem cell23_6602771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2, 2].length) (baseStart_6602771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602771 prefixEnd_6602771 := by exact prefixLift 6602771
  have htrace : WordTrace (prefixWord ++ tailWord_6602771) baseStart_6602771 baseEnd_6602771 := by
    simpa [prefixWord, tailWord_6602771, baseEnd_6602771] using wordTrace_append hprefix tailTrace_6602771
  have hstable : (prefixWord ++ tailWord_6602771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602771).length < 2 ^ (prefixWord ++ tailWord_6602771).sum := by decide
  have hdescent : baseEnd_6602771 < baseStart_6602771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602781 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6602781 : Nat := 118140960795 + 6602781 * 2 ^ 59
def prefixEnd_6602781 : Nat := 4983230072969 + 3 ^ 40 * 6602781 * 2
def baseEnd_6602781 : Nat := 1130133436458145440890623

theorem tailTrace_6602781 : CollatzResearch.WordTrace tailWord_6602781 prefixEnd_6602781 1130133436458145440890623 := by
  unfold tailWord_6602781
  simp only [CollatzResearch.WordTrace]
  refine ⟨240823207492259577061896197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160548804994839718041264131 240823207492259577061896197)
  ·
    refine ⟨45154351404798670699105537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240823207492259577061896197 45154351404798670699105537)
    ·
      refine ⟨33865763553599003024329153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45154351404798670699105537 33865763553599003024329153)
      ·
        refine ⟨25399322665199252268246865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33865763553599003024329153 25399322665199252268246865)
        ·
          refine ⟨19049491998899439201185149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25399322665199252268246865 19049491998899439201185149)
          ·
            refine ⟨7143559499587289700444431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19049491998899439201185149 7143559499587289700444431)
            ·
              refine ⟨10715339249380934550666647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143559499587289700444431 10715339249380934550666647)
              ·
                refine ⟨16073008874071401825999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10715339249380934550666647 16073008874071401825999971)
                ·
                  refine ⟨24109513311107102738999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16073008874071401825999971 24109513311107102738999957)
                  ·
                    refine ⟨1130133436458145440890623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24109513311107102738999957 1130133436458145440890623)
                    ·
                      rfl

theorem cell23_6602781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6602781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602781 prefixEnd_6602781 := by exact prefixLift 6602781
  have htrace : WordTrace (prefixWord ++ tailWord_6602781) baseStart_6602781 baseEnd_6602781 := by
    simpa [prefixWord, tailWord_6602781, baseEnd_6602781] using wordTrace_append hprefix tailTrace_6602781
  have hstable : (prefixWord ++ tailWord_6602781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602781).length < 2 ^ (prefixWord ++ tailWord_6602781).sum := by decide
  have hdescent : baseEnd_6602781 < baseStart_6602781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602788 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6602788 : Nat := 118140960795 + 6602788 * 2 ^ 59
def prefixEnd_6602788 : Nat := 4983230072969 + 3 ^ 40 * 6602788 * 2
def baseEnd_6602788 : Nat := 3390403903739017795284337

theorem tailTrace_6602788 : CollatzResearch.WordTrace tailWord_6602788 prefixEnd_6602788 3390403903739017795284337 := by
  unfold tailWord_6602788
  simp only [CollatzResearch.WordTrace]
  refine ⟨120411731401617108628700509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160548975202156144838267345 120411731401617108628700509)
  ·
    refine ⟨45154399275606415735762691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120411731401617108628700509 45154399275606415735762691)
    ·
      refine ⟨67731598913409623603644037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45154399275606415735762691 67731598913409623603644037)
      ·
        refine ⟨12699674796264304425683257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67731598913409623603644037 12699674796264304425683257)
        ·
          refine ⟨9524756097198228319262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12699674796264304425683257 9524756097198228319262443)
          ·
            refine ⟨14287134145797342478893665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524756097198228319262443 14287134145797342478893665)
            ·
              refine ⟨10715350609348006859170249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14287134145797342478893665 10715350609348006859170249)
              ·
                refine ⟨8036512957011005144377687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10715350609348006859170249 8036512957011005144377687)
                ·
                  refine ⟨12054769435516507716566531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036512957011005144377687 12054769435516507716566531)
                  ·
                    refine ⟨18082154153274761574849797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12054769435516507716566531 18082154153274761574849797)
                    ·
                      refine ⟨3390403903739017795284337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18082154153274761574849797 3390403903739017795284337)
                      ·
                        rfl

theorem cell23_6602788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6602788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602788 prefixEnd_6602788 := by exact prefixLift 6602788
  have htrace : WordTrace (prefixWord ++ tailWord_6602788) baseStart_6602788 baseEnd_6602788 := by
    simpa [prefixWord, tailWord_6602788, baseEnd_6602788] using wordTrace_append hprefix tailTrace_6602788
  have hstable : (prefixWord ++ tailWord_6602788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602788).length < 2 ^ (prefixWord ++ tailWord_6602788).sum := by decide
  have hdescent : baseEnd_6602788 < baseStart_6602788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602794 : List Nat := [3, 1, 4, 1, 2, 2, 1, 9]
def baseStart_6602794 : Nat := 118140960795 + 6602794 * 2 ^ 59
def prefixEnd_6602794 : Nat := 4983230072969 + 3 ^ 40 * 6602794 * 2
def baseEnd_6602794 : Nat := 125570629060109065622567

theorem tailTrace_6602794 : CollatzResearch.WordTrace tailWord_6602794 prefixEnd_6602794 125570629060109065622567 := by
  unfold tailWord_6602794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60205920410303120070529859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160549121094141653521412957 60205920410303120070529859)
  ·
    refine ⟨90308880615454680105794789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60205920410303120070529859 90308880615454680105794789)
    ·
      refine ⟨16932915115397752519836523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90308880615454680105794789 16932915115397752519836523)
      ·
        refine ⟨25399372673096628779754785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16932915115397752519836523 25399372673096628779754785)
        ·
          refine ⟨19049529504822471584816089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25399372673096628779754785 19049529504822471584816089)
          ·
            refine ⟨14287147128616853688612067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19049529504822471584816089 14287147128616853688612067)
            ·
              refine ⟨21430720692925280532918101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14287147128616853688612067 21430720692925280532918101)
              ·
                refine ⟨125570629060109065622567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21430720692925280532918101 125570629060109065622567)
                ·
                  rfl

theorem cell23_6602794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_6602794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602794 prefixEnd_6602794 := by exact prefixLift 6602794
  have htrace : WordTrace (prefixWord ++ tailWord_6602794) baseStart_6602794 baseEnd_6602794 := by
    simpa [prefixWord, tailWord_6602794, baseEnd_6602794] using wordTrace_append hprefix tailTrace_6602794
  have hstable : (prefixWord ++ tailWord_6602794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602794).length < 2 ^ (prefixWord ++ tailWord_6602794).sum := by decide
  have hdescent : baseEnd_6602794 < baseStart_6602794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602805 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_6602805 : Nat := 118140960795 + 6602805 * 2 ^ 59
def prefixEnd_6602805 : Nat := 4983230072969 + 3 ^ 40 * 6602805 * 2
def baseEnd_6602805 : Nat := 3390412632910144228771759

theorem tailTrace_6602805 : CollatzResearch.WordTrace tailWord_6602805 prefixEnd_6602805 3390412632910144228771759 := by
  unfold tailWord_6602805
  simp only [CollatzResearch.WordTrace]
  refine ⟨240824082844172629160769869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160549388562781752773846579 240824082844172629160769869)
  ·
    refine ⟨90309031066564735935288701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240824082844172629160769869 90309031066564735935288701)
    ·
      refine ⟨33865886649961775975733263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90309031066564735935288701 33865886649961775975733263)
      ·
        refine ⟨50798829974942663963599895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33865886649961775975733263 50798829974942663963599895)
        ·
          refine ⟨76198244962413995945399843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50798829974942663963599895 76198244962413995945399843)
          ·
            refine ⟨114297367443620993918099765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76198244962413995945399843 114297367443620993918099765)
            ·
              refine ⟨10715378197839468179821853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114297367443620993918099765 10715378197839468179821853)
              ·
                refine ⟨4018266824189800567433195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10715378197839468179821853 4018266824189800567433195)
                ·
                  refine ⟨6027400236284700851149793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018266824189800567433195 6027400236284700851149793)
                  ·
                    refine ⟨4520550177213525638362345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6027400236284700851149793 4520550177213525638362345)
                    ·
                      refine ⟨3390412632910144228771759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520550177213525638362345 3390412632910144228771759)
                      ·
                        rfl

theorem cell23_6602805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_6602805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602805 prefixEnd_6602805 := by exact prefixLift 6602805
  have htrace : WordTrace (prefixWord ++ tailWord_6602805) baseStart_6602805 baseEnd_6602805 := by
    simpa [prefixWord, tailWord_6602805, baseEnd_6602805] using wordTrace_append hprefix tailTrace_6602805
  have hstable : (prefixWord ++ tailWord_6602805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602805).length < 2 ^ (prefixWord ++ tailWord_6602805).sum := by decide
  have hdescent : baseEnd_6602805 < baseStart_6602805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602821 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_6602821 : Nat := 118140960795 + 6602821 * 2 ^ 59
def prefixEnd_6602821 : Nat := 4983230072969 + 3 ^ 40 * 6602821 * 2
def baseEnd_6602821 : Nat := 3390420848600616166171685

theorem tailTrace_6602821 : CollatzResearch.WordTrace tailWord_6602821 prefixEnd_6602821 3390420848600616166171685 := by
  unfold tailWord_6602821
  simp only [CollatzResearch.WordTrace]
  refine ⟨240824666412114663893352317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160549777608076442595568211 240824666412114663893352317)
  ·
    refine ⟨90309249904542998960007119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240824666412114663893352317 90309249904542998960007119)
    ·
      refine ⟨135463874856814498440010679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90309249904542998960007119 135463874856814498440010679)
      ·
        refine ⟨203195812285221747660016019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135463874856814498440010679 203195812285221747660016019)
        ·
          refine ⟨304793718427832621490024029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203195812285221747660016019 304793718427832621490024029)
          ·
            refine ⟨114297644410437233058759011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304793718427832621490024029 114297644410437233058759011)
            ·
              refine ⟨171446466615655849588138517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114297644410437233058759011 171446466615655849588138517)
              ·
                refine ⟨8036553122608867949443993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171446466615655849588138517 8036553122608867949443993)
                ·
                  refine ⟨6027414841956650962082995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036553122608867949443993 6027414841956650962082995)
                  ·
                    refine ⟨9041122262934976443124493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027414841956650962082995 9041122262934976443124493)
                    ·
                      refine ⟨3390420848600616166171685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041122262934976443124493 3390420848600616166171685)
                      ·
                        rfl

theorem cell23_6602821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_6602821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602821 prefixEnd_6602821 := by exact prefixLift 6602821
  have htrace : WordTrace (prefixWord ++ tailWord_6602821) baseStart_6602821 baseEnd_6602821 := by
    simpa [prefixWord, tailWord_6602821, baseEnd_6602821] using wordTrace_append hprefix tailTrace_6602821
  have hstable : (prefixWord ++ tailWord_6602821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602821).length < 2 ^ (prefixWord ++ tailWord_6602821).sum := by decide
  have hdescent : baseEnd_6602821 < baseStart_6602821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602827 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_6602827 : Nat := 118140960795 + 6602827 * 2 ^ 59
def prefixEnd_6602827 : Nat := 4983230072969 + 3 ^ 40 * 6602827 * 2
def baseEnd_6602827 : Nat := 3390423929484543142696657

theorem tailTrace_6602827 : CollatzResearch.WordTrace tailWord_6602827 prefixEnd_6602827 3390423929484543142696657 := by
  unfold tailWord_6602827
  simp only [CollatzResearch.WordTrace]
  refine ⟨240824885250092926918070735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160549923500061951278713823 240824885250092926918070735)
  ·
    refine ⟨361237327875139390377106103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240824885250092926918070735 361237327875139390377106103)
    ·
      refine ⟨541855991812709085565659155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361237327875139390377106103 541855991812709085565659155)
      ·
        refine ⟨812783987719063628348488733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541855991812709085565659155 812783987719063628348488733)
        ·
          refine ⟨304793995394648860630683275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812783987719063628348488733 304793995394648860630683275)
          ·
            refine ⟨457190993091973290946024913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304793995394648860630683275 457190993091973290946024913)
            ·
              refine ⟨342893244818979968209518685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457190993091973290946024913 342893244818979968209518685)
              ·
                refine ⟨128584966807117488078569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342893244818979968209518685 128584966807117488078569507)
                ·
                  refine ⟨192877450210676232117854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128584966807117488078569507 192877450210676232117854261)
                  ·
                    refine ⟨18082260957250896761048837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 192877450210676232117854261 18082260957250896761048837)
                    ·
                      refine ⟨3390423929484543142696657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18082260957250896761048837 3390423929484543142696657)
                      ·
                        rfl

theorem cell23_6602827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_6602827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602827 prefixEnd_6602827 := by exact prefixLift 6602827
  have htrace : WordTrace (prefixWord ++ tailWord_6602827) baseStart_6602827 baseEnd_6602827 := by
    simpa [prefixWord, tailWord_6602827, baseEnd_6602827] using wordTrace_append hprefix tailTrace_6602827
  have hstable : (prefixWord ++ tailWord_6602827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602827).length < 2 ^ (prefixWord ++ tailWord_6602827).sum := by decide
  have hdescent : baseEnd_6602827 < baseStart_6602827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602848 : List Nat := [2, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2]
def baseStart_6602848 : Nat := 118140960795 + 6602848 * 2 ^ 59
def prefixEnd_6602848 : Nat := 4983230072969 + 3 ^ 40 * 6602848 * 2
def baseEnd_6602848 : Nat := 3390434712578287560534061

theorem tailTrace_6602848 : CollatzResearch.WordTrace tailWord_6602848 prefixEnd_6602848 3390434712578287560534061 := by
  unfold tailWord_6602848
  simp only [CollatzResearch.WordTrace]
  refine ⟨120412825591508423752292599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160550434122011231669723465 120412825591508423752292599)
  ·
    refine ⟨180619238387262635628438899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120412825591508423752292599 180619238387262635628438899)
    ·
      refine ⟨270928857580893953442658349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180619238387262635628438899 270928857580893953442658349)
      ·
        refine ⟨101598321592835232540996881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270928857580893953442658349 101598321592835232540996881)
        ·
          refine ⟨76198741194626424405747661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101598321592835232540996881 76198741194626424405747661)
          ·
            refine ⟨28574527947984909152155373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76198741194626424405747661 28574527947984909152155373)
            ·
              refine ⟨10715447980494340932058265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28574527947984909152155373 10715447980494340932058265)
              ·
                refine ⟨8036585985370755699043699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10715447980494340932058265 8036585985370755699043699)
                ·
                  refine ⟨12054878978056133548565549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036585985370755699043699 12054878978056133548565549)
                  ·
                    refine ⟨4520579616771050080712081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12054878978056133548565549 4520579616771050080712081)
                    ·
                      refine ⟨3390434712578287560534061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520579616771050080712081 3390434712578287560534061)
                      ·
                        rfl

theorem cell23_6602848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_6602848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602848 prefixEnd_6602848 := by exact prefixLift 6602848
  have htrace : WordTrace (prefixWord ++ tailWord_6602848) baseStart_6602848 baseEnd_6602848 := by
    simpa [prefixWord, tailWord_6602848, baseEnd_6602848] using wordTrace_append hprefix tailTrace_6602848
  have hstable : (prefixWord ++ tailWord_6602848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602848).length < 2 ^ (prefixWord ++ tailWord_6602848).sum := by decide
  have hdescent : baseEnd_6602848 < baseStart_6602848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602864 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_6602864 : Nat := 118140960795 + 6602864 * 2 ^ 59
def prefixEnd_6602864 : Nat := 4983230072969 + 3 ^ 40 * 6602864 * 2
def baseEnd_6602864 : Nat := 3390442928268759497933987

theorem tailTrace_6602864 : CollatzResearch.WordTrace tailWord_6602864 prefixEnd_6602864 3390442928268759497933987 := by
  unfold tailWord_6602864
  simp only [CollatzResearch.WordTrace]
  refine ⟨120413117375479441118583823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160550823167305921491445097 120413117375479441118583823)
  ·
    refine ⟨180619676063219161677875735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120413117375479441118583823 180619676063219161677875735)
    ·
      refine ⟨270929514094828742516813603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180619676063219161677875735 270929514094828742516813603)
      ·
        refine ⟨406394271142243113775220405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270929514094828742516813603 406394271142243113775220405)
        ·
          refine ⟨38099462919585291916426913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406394271142243113775220405 38099462919585291916426913)
          ·
            refine ⟨28574597189688968937320185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38099462919585291916426913 28574597189688968937320185)
            ·
              refine ⟨21430947892266726702990139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28574597189688968937320185 21430947892266726702990139)
              ·
                refine ⟨32146421838400090054485209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21430947892266726702990139 32146421838400090054485209)
                ·
                  refine ⟨24109816378800067540863907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32146421838400090054485209 24109816378800067540863907)
                  ·
                    refine ⟨36164724568200101311295861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24109816378800067540863907 36164724568200101311295861)
                    ·
                      refine ⟨3390442928268759497933987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36164724568200101311295861 3390442928268759497933987)
                      ·
                        rfl

theorem cell23_6602864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_6602864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602864 prefixEnd_6602864 := by exact prefixLift 6602864
  have htrace : WordTrace (prefixWord ++ tailWord_6602864) baseStart_6602864 baseEnd_6602864 := by
    simpa [prefixWord, tailWord_6602864, baseEnd_6602864] using wordTrace_append hprefix tailTrace_6602864
  have hstable : (prefixWord ++ tailWord_6602864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602864).length < 2 ^ (prefixWord ++ tailWord_6602864).sum := by decide
  have hdescent : baseEnd_6602864 < baseStart_6602864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602884 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 7]
def baseStart_6602884 : Nat := 118140960795 + 6602884 * 2 ^ 59
def prefixEnd_6602884 : Nat := 4983230072969 + 3 ^ 40 * 6602884 * 2
def baseEnd_6602884 : Nat := 376717021986872157742655

theorem tailTrace_6602884 : CollatzResearch.WordTrace tailWord_6602884 prefixEnd_6602884 376717021986872157742655 := by
  unfold tailWord_6602884
  simp only [CollatzResearch.WordTrace]
  refine ⟨120413482105443212826447853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160551309473924283768597137 120413482105443212826447853)
  ·
    refine ⟨45155055789541204809917945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120413482105443212826447853 45155055789541204809917945)
    ·
      refine ⟨33866291842155903607438459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45155055789541204809917945 33866291842155903607438459)
      ·
        refine ⟨50799437763233855411157689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33866291842155903607438459 50799437763233855411157689)
        ·
          refine ⟨38099578322425391558368267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50799437763233855411157689 38099578322425391558368267)
          ·
            refine ⟨57149367483638087337552401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38099578322425391558368267 57149367483638087337552401)
            ·
              refine ⟨42862025612728565503164301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57149367483638087337552401 42862025612728565503164301)
              ·
                refine ⟨16073259604773212063686613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42862025612728565503164301 16073259604773212063686613)
                ·
                  refine ⟨376717021986872157742655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16073259604773212063686613 376717021986872157742655)
                  ·
                    rfl

theorem cell23_6602884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_6602884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602884 prefixEnd_6602884 := by exact prefixLift 6602884
  have htrace : WordTrace (prefixWord ++ tailWord_6602884) baseStart_6602884 baseEnd_6602884 := by
    simpa [prefixWord, tailWord_6602884, baseEnd_6602884] using wordTrace_append hprefix tailTrace_6602884
  have hstable : (prefixWord ++ tailWord_6602884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602884).length < 2 ^ (prefixWord ++ tailWord_6602884).sum := by decide
  have hdescent : baseEnd_6602884 < baseStart_6602884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602929 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6602929 : Nat := 118140960795 + 6602929 * 2 ^ 59
def prefixEnd_6602929 : Nat := 4983230072969 + 3 ^ 40 * 6602929 * 2
def baseEnd_6602929 : Nat := 3390476304511301743621189

theorem tailTrace_6602929 : CollatzResearch.WordTrace tailWord_6602929 prefixEnd_6602929 3390476304511301743621189 := by
  unfold tailWord_6602929
  simp only [CollatzResearch.WordTrace]
  refine ⟨240828605495723398338283841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160552403663815598892189227 240828605495723398338283841)
  ·
    refine ⟨180621454121792548753712881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240828605495723398338283841 180621454121792548753712881)
    ·
      refine ⟨135466090591344411565284661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180621454121792548753712881 135466090591344411565284661)
      ·
        refine ⟨12699945992938538584245437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135466090591344411565284661 12699945992938538584245437)
        ·
          refine ⟨4762479747351951969092039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12699945992938538584245437 4762479747351951969092039)
          ·
            refine ⟨7143719621027927953638059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762479747351951969092039 7143719621027927953638059)
            ·
              refine ⟨10715579431541891930457089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143719621027927953638059 10715579431541891930457089)
              ·
                refine ⟨8036684573656418947842817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10715579431541891930457089 8036684573656418947842817)
                ·
                  refine ⟨6027513430242314210882113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036684573656418947842817 6027513430242314210882113)
                  ·
                    refine ⟨4520635072681735658161585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6027513430242314210882113 4520635072681735658161585)
                    ·
                      refine ⟨3390476304511301743621189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520635072681735658161585 3390476304511301743621189)
                      ·
                        rfl

theorem cell23_6602929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6602929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602929 prefixEnd_6602929 := by exact prefixLift 6602929
  have htrace : WordTrace (prefixWord ++ tailWord_6602929) baseStart_6602929 baseEnd_6602929 := by
    simpa [prefixWord, tailWord_6602929, baseEnd_6602929] using wordTrace_append hprefix tailTrace_6602929
  have hstable : (prefixWord ++ tailWord_6602929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602929).length < 2 ^ (prefixWord ++ tailWord_6602929).sum := by decide
  have hdescent : baseEnd_6602929 < baseStart_6602929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602946 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6602946 : Nat := 118140960795 + 6602946 * 2 ^ 59
def prefixEnd_6602946 : Nat := 4983230072969 + 3 ^ 40 * 6602946 * 2
def baseEnd_6602946 : Nat := 3390485033682428177108611

theorem tailTrace_6602946 : CollatzResearch.WordTrace tailWord_6602946 prefixEnd_6602946 3390485033682428177108611 := by
  unfold tailWord_6602946
  simp only [CollatzResearch.WordTrace]
  refine ⟨60207306384165452560413173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160552817024441206827768461 60207306384165452560413173)
  ·
    refine ⟨5644434973515511177538735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60207306384165452560413173 5644434973515511177538735)
    ·
      refine ⟨8466652460273266766308103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5644434973515511177538735 8466652460273266766308103)
      ·
        refine ⟨12699978690409900149462155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466652460273266766308103 12699978690409900149462155)
        ·
          refine ⟨19049968035614850224193233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699978690409900149462155 19049968035614850224193233)
          ·
            refine ⟨14287476026711137668144925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19049968035614850224193233 14287476026711137668144925)
            ·
              refine ⟨5357803510016676625554347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14287476026711137668144925 5357803510016676625554347)
              ·
                refine ⟨8036705265025014938331521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357803510016676625554347 8036705265025014938331521)
                ·
                  refine ⟨6027528948768761203748641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036705265025014938331521 6027528948768761203748641)
                  ·
                    refine ⟨4520646711576570902811481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6027528948768761203748641 4520646711576570902811481)
                    ·
                      refine ⟨3390485033682428177108611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520646711576570902811481 3390485033682428177108611)
                      ·
                        rfl

theorem cell23_6602946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6602946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602946 prefixEnd_6602946 := by exact prefixLift 6602946
  have htrace : WordTrace (prefixWord ++ tailWord_6602946) baseStart_6602946 baseEnd_6602946 := by
    simpa [prefixWord, tailWord_6602946, baseEnd_6602946] using wordTrace_append hprefix tailTrace_6602946
  have hstable : (prefixWord ++ tailWord_6602946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602946).length < 2 ^ (prefixWord ++ tailWord_6602946).sum := by decide
  have hdescent : baseEnd_6602946 < baseStart_6602946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602961 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_6602961 : Nat := 118140960795 + 6602961 * 2 ^ 59
def prefixEnd_6602961 : Nat := 4983230072969 + 3 ^ 40 * 6602961 * 2
def baseEnd_6602961 : Nat := 1130164245297415206140347

theorem tailTrace_6602961 : CollatzResearch.WordTrace tailWord_6602961 prefixEnd_6602961 1130164245297415206140347 := by
  unfold tailWord_6602961
  simp only [CollatzResearch.WordTrace]
  refine ⟨240829772631607467803448737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160553181754404978535632491 240829772631607467803448737)
  ·
    refine ⟨180622329473705600852586553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240829772631607467803448737 180622329473705600852586553)
    ·
      refine ⟨135466747105279200639439915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180622329473705600852586553 135466747105279200639439915)
      ·
        refine ⟨203200120657918800959159873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135466747105279200639439915 203200120657918800959159873)
        ·
          refine ⟨152400090493439100719369905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203200120657918800959159873 152400090493439100719369905)
          ·
            refine ⟨114300067870079325539527429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152400090493439100719369905 114300067870079325539527429)
            ·
              refine ⟨21431262725639873538661393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114300067870079325539527429 21431262725639873538661393)
              ·
                refine ⟨16073447044229905153996045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21431262725639873538661393 16073447044229905153996045)
                ·
                  refine ⟨6027542641586214432748517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16073447044229905153996045 6027542641586214432748517)
                  ·
                    refine ⟨1130164245297415206140347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027542641586214432748517 1130164245297415206140347)
                    ·
                      rfl

theorem cell23_6602961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_6602961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602961 prefixEnd_6602961 := by exact prefixLift 6602961
  have htrace : WordTrace (prefixWord ++ tailWord_6602961) baseStart_6602961 baseEnd_6602961 := by
    simpa [prefixWord, tailWord_6602961, baseEnd_6602961] using wordTrace_append hprefix tailTrace_6602961
  have hstable : (prefixWord ++ tailWord_6602961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602961).length < 2 ^ (prefixWord ++ tailWord_6602961).sum := by decide
  have hdescent : baseEnd_6602961 < baseStart_6602961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6602995 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 1, 4]
def baseStart_6602995 : Nat := 118140960795 + 6602995 * 2 ^ 59
def prefixEnd_6602995 : Nat := 4983230072969 + 3 ^ 40 * 6602995 * 2
def baseEnd_6602995 : Nat := 1130170064744832828465295

theorem tailTrace_6602995 : CollatzResearch.WordTrace tailWord_6602995 prefixEnd_6602995 1130170064744832828465295 := by
  unfold tailWord_6602995
  simp only [CollatzResearch.WordTrace]
  refine ⟨240831012713484291610186439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160554008475656194406790959 240831012713484291610186439)
  ·
    refine ⟨361246519070226437415279659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240831012713484291610186439 361246519070226437415279659)
    ·
      refine ⟨541869778605339656122919489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361246519070226437415279659 541869778605339656122919489)
      ·
        refine ⟨406402333954004742092189617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541869778605339656122919489 406402333954004742092189617)
        ·
          refine ⟨304801750465503556569142213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406402333954004742092189617 304801750465503556569142213)
          ·
            refine ⟨57150328212281916856714165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304801750465503556569142213 57150328212281916856714165)
            ·
              refine ⟨5357843269901429705316953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57150328212281916856714165 5357843269901429705316953)
              ·
                refine ⟨4018382452426072278987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357843269901429705316953 4018382452426072278987715)
                ·
                  refine ⟨6027573678639108418481573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018382452426072278987715 6027573678639108418481573)
                  ·
                    refine ⟨1130170064744832828465295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027573678639108418481573 1130170064744832828465295)
                    ·
                      rfl

theorem cell23_6602995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 4].length) (baseStart_6602995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6602995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6602995 prefixEnd_6602995 := by exact prefixLift 6602995
  have htrace : WordTrace (prefixWord ++ tailWord_6602995) baseStart_6602995 baseEnd_6602995 := by
    simpa [prefixWord, tailWord_6602995, baseEnd_6602995] using wordTrace_append hprefix tailTrace_6602995
  have hstable : (prefixWord ++ tailWord_6602995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6602995).length < 2 ^ (prefixWord ++ tailWord_6602995).sum := by decide
  have hdescent : baseEnd_6602995 < baseStart_6602995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6602995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603018 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_6603018 : Nat := 118140960795 + 6603018 * 2 ^ 59
def prefixEnd_6603018 : Nat := 4983230072969 + 3 ^ 40 * 6603018 * 2
def baseEnd_6603018 : Nat := 3390522004289551895408279

theorem tailTrace_6603018 : CollatzResearch.WordTrace tailWord_6603018 prefixEnd_6603018 3390522004289551895408279 := by
  unfold tailWord_6603018
  simp only [CollatzResearch.WordTrace]
  refine ⟨60207962898100241634568427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160554567728267311025515805 60207962898100241634568427)
  ·
    refine ⟨90311944347150362451852641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60207962898100241634568427 90311944347150362451852641)
    ·
      refine ⟨67733958260362771838889481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90311944347150362451852641 67733958260362771838889481)
      ·
        refine ⟨50800468695272078879167111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67733958260362771838889481 50800468695272078879167111)
        ·
          refine ⟨76200703042908118318750667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50800468695272078879167111 76200703042908118318750667)
          ·
            refine ⟨114301054564362177478126001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76200703042908118318750667 114301054564362177478126001)
            ·
              refine ⟨85725790923271633108594501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114301054564362177478126001 85725790923271633108594501)
              ·
                refine ⟨16073585798113431207861469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85725790923271633108594501 16073585798113431207861469)
                ·
                  refine ⟨6027594674292536702948051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16073585798113431207861469 6027594674292536702948051)
                  ·
                    refine ⟨9041392011438805054422077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027594674292536702948051 9041392011438805054422077)
                    ·
                      refine ⟨3390522004289551895408279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041392011438805054422077 3390522004289551895408279)
                      ·
                        rfl

theorem cell23_6603018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_6603018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603018 prefixEnd_6603018 := by exact prefixLift 6603018
  have htrace : WordTrace (prefixWord ++ tailWord_6603018) baseStart_6603018 baseEnd_6603018 := by
    simpa [prefixWord, tailWord_6603018, baseEnd_6603018] using wordTrace_append hprefix tailTrace_6603018
  have hstable : (prefixWord ++ tailWord_6603018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603018).length < 2 ^ (prefixWord ++ tailWord_6603018).sum := by decide
  have hdescent : baseEnd_6603018 < baseStart_6603018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603052 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_6603052 : Nat := 118140960795 + 6603052 * 2 ^ 59
def prefixEnd_6603052 : Nat := 4983230072969 + 3 ^ 40 * 6603052 * 2
def baseEnd_6603052 : Nat := 3390539462631804762383123

theorem tailTrace_6603052 : CollatzResearch.WordTrace tailWord_6603052 prefixEnd_6603052 3390539462631804762383123 := by
  unfold tailWord_6603052
  simp only [CollatzResearch.WordTrace]
  refine ⟨120416545837138895172505705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160555394449518526896674273 120416545837138895172505705)
  ·
    refine ⟨90312409377854171379379279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120416545837138895172505705 90312409377854171379379279)
    ·
      refine ⟨135468614066781257069068919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90312409377854171379379279 135468614066781257069068919)
      ·
        refine ⟨203202921100171885603603379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135468614066781257069068919 203202921100171885603603379)
        ·
          refine ⟨304804381650257828405405069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203202921100171885603603379 304804381650257828405405069)
          ·
            refine ⟨114301643118846685652026901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304804381650257828405405069 114301643118846685652026901)
            ·
              refine ⟨5357889521195938389938761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114301643118846685652026901 5357889521195938389938761)
              ·
                refine ⟨4018417140896953792454071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357889521195938389938761 4018417140896953792454071)
                ·
                  refine ⟨6027625711345430688681107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018417140896953792454071 6027625711345430688681107)
                  ·
                    refine ⟨9041438567018146033021661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027625711345430688681107 9041438567018146033021661)
                    ·
                      refine ⟨3390539462631804762383123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041438567018146033021661 3390539462631804762383123)
                      ·
                        rfl

theorem cell23_6603052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_6603052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603052 prefixEnd_6603052 := by exact prefixLift 6603052
  have htrace : WordTrace (prefixWord ++ tailWord_6603052) baseStart_6603052 baseEnd_6603052 := by
    simpa [prefixWord, tailWord_6603052, baseEnd_6603052] using wordTrace_append hprefix tailTrace_6603052
  have hstable : (prefixWord ++ tailWord_6603052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603052).length < 2 ^ (prefixWord ++ tailWord_6603052).sum := by decide
  have hdescent : baseEnd_6603052 < baseStart_6603052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603061 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_6603061 : Nat := 118140960795 + 6603061 * 2 ^ 59
def prefixEnd_6603061 : Nat := 4983230072969 + 3 ^ 40 * 6603061 * 2
def baseEnd_6603061 : Nat := 3390544083957695227170581

theorem tailTrace_6603061 : CollatzResearch.WordTrace tailWord_6603061 prefixEnd_6603061 3390544083957695227170581 := by
  unfold tailWord_6603061
  simp only [CollatzResearch.WordTrace]
  refine ⟨240833419931245184882089037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160555613287496789921392691 240833419931245184882089037)
  ·
    refine ⟨90312532474216944330783389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240833419931245184882089037 90312532474216944330783389)
    ·
      refine ⟨33867199677831354124043771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90312532474216944330783389 33867199677831354124043771)
      ·
        refine ⟨50800799516747031186065657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33867199677831354124043771 50800799516747031186065657)
        ·
          refine ⟨38100599637560273389549243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50800799516747031186065657 38100599637560273389549243)
          ·
            refine ⟨57150899456340410084323865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38100599637560273389549243 57150899456340410084323865)
            ·
              refine ⟨42863174592255307563242899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57150899456340410084323865 42863174592255307563242899)
              ·
                refine ⟨64294761888382961344864349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42863174592255307563242899 64294761888382961344864349)
                ·
                  refine ⟨24110535708143610504324131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64294761888382961344864349 24110535708143610504324131)
                  ·
                    refine ⟨36165803562215415756486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24110535708143610504324131 36165803562215415756486197)
                    ·
                      refine ⟨3390544083957695227170581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36165803562215415756486197 3390544083957695227170581)
                      ·
                        rfl

theorem cell23_6603061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_6603061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603061 prefixEnd_6603061 := by exact prefixLift 6603061
  have htrace : WordTrace (prefixWord ++ tailWord_6603061) baseStart_6603061 baseEnd_6603061 := by
    simpa [prefixWord, tailWord_6603061, baseEnd_6603061] using wordTrace_append hprefix tailTrace_6603061
  have hstable : (prefixWord ++ tailWord_6603061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603061).length < 2 ^ (prefixWord ++ tailWord_6603061).sum := by decide
  have hdescent : baseEnd_6603061 < baseStart_6603061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603068 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_6603068 : Nat := 118140960795 + 6603068 * 2 ^ 59
def prefixEnd_6603068 : Nat := 4983230072969 + 3 ^ 40 * 6603068 * 2
def baseEnd_6603068 : Nat := 1130182559440758899927683

theorem tailTrace_6603068 : CollatzResearch.WordTrace tailWord_6603068 prefixEnd_6603068 1130182559440758899927683 := by
  unfold tailWord_6603068
  simp only [CollatzResearch.WordTrace]
  refine ⟨120416837621109912538796929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160555783494813216718395905 120416837621109912538796929)
  ·
    refine ⟨90312628215832434404097697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120416837621109912538796929 90312628215832434404097697)
    ·
      refine ⟨67734471161874325803073273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90312628215832434404097697 67734471161874325803073273)
      ·
        refine ⟨50800853371405744352304955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67734471161874325803073273 50800853371405744352304955)
        ·
          refine ⟨76201280057108616528457433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50800853371405744352304955 76201280057108616528457433)
          ·
            refine ⟨57150960042831462396343075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76201280057108616528457433 57150960042831462396343075)
            ·
              refine ⟨85726440064247193594514613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57150960042831462396343075 85726440064247193594514613)
              ·
                refine ⟨8036853756023174399485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85726440064247193594514613 8036853756023174399485745)
                ·
                  refine ⟨6027640317017380799614309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036853756023174399485745 6027640317017380799614309)
                  ·
                    refine ⟨1130182559440758899927683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027640317017380799614309 1130182559440758899927683)
                    ·
                      rfl

theorem cell23_6603068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_6603068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603068 prefixEnd_6603068 := by exact prefixLift 6603068
  have htrace : WordTrace (prefixWord ++ tailWord_6603068) baseStart_6603068 baseEnd_6603068 := by
    simpa [prefixWord, tailWord_6603068, baseEnd_6603068] using wordTrace_append hprefix tailTrace_6603068
  have hstable : (prefixWord ++ tailWord_6603068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603068).length < 2 ^ (prefixWord ++ tailWord_6603068).sum := by decide
  have hdescent : baseEnd_6603068 < baseStart_6603068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603091 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3]
def baseStart_6603091 : Nat := 118140960795 + 6603091 * 2 ^ 59
def prefixEnd_6603091 : Nat := 4983230072969 + 3 ^ 40 * 6603091 * 2
def baseEnd_6603091 : Nat := 3390559488377330109795443

theorem tailTrace_6603091 : CollatzResearch.WordTrace tailWord_6603091 prefixEnd_6603091 3390559488377330109795443 := by
  unfold tailWord_6603091
  simp only [CollatzResearch.WordTrace]
  refine ⟨240834514121136500005681127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160556342747424333337120751 240834514121136500005681127)
  ·
    refine ⟨361251771181704750008521691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240834514121136500005681127 361251771181704750008521691)
    ·
      refine ⟨541877656772557125012782537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361251771181704750008521691 541877656772557125012782537)
      ·
        refine ⟨406408242579417843759586903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541877656772557125012782537 406408242579417843759586903)
        ·
          refine ⟨609612363869126765639380355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406408242579417843759586903 609612363869126765639380355)
          ·
            refine ⟨914418545803690148459070533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609612363869126765639380355 914418545803690148459070533)
            ·
              refine ⟨171453477338191902836075725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 914418545803690148459070533 171453477338191902836075725)
              ·
                refine ⟨64295054001821963563528397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171453477338191902836075725 64295054001821963563528397)
                ·
                  refine ⟨24110645250683236336323149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64295054001821963563528397 24110645250683236336323149)
                  ·
                    refine ⟨9041491969006213626121181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24110645250683236336323149 9041491969006213626121181)
                    ·
                      refine ⟨3390559488377330109795443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041491969006213626121181 3390559488377330109795443)
                      ·
                        rfl

theorem cell23_6603091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_6603091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603091 prefixEnd_6603091 := by exact prefixLift 6603091
  have htrace : WordTrace (prefixWord ++ tailWord_6603091) baseStart_6603091 baseEnd_6603091 := by
    simpa [prefixWord, tailWord_6603091, baseEnd_6603091] using wordTrace_append hprefix tailTrace_6603091
  have hstable : (prefixWord ++ tailWord_6603091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603091).length < 2 ^ (prefixWord ++ tailWord_6603091).sum := by decide
  have hdescent : baseEnd_6603091 < baseStart_6603091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603092 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_6603092 : Nat := 118140960795 + 6603092 * 2 ^ 59
def prefixEnd_6603092 : Nat := 4983230072969 + 3 ^ 40 * 6603092 * 2
def baseEnd_6603092 : Nat := 3390560001857984605882939

theorem tailTrace_6603092 : CollatzResearch.WordTrace tailWord_6603092 prefixEnd_6603092 3390560001857984605882939 := by
  unfold tailWord_6603092
  simp only [CollatzResearch.WordTrace]
  refine ⟨120417275297066438588233765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160556367062755251450978353 120417275297066438588233765)
  ·
    refine ⟨22578239118199957235293831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120417275297066438588233765 22578239118199957235293831)
    ·
      refine ⟨33867358677299935852940747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22578239118199957235293831 33867358677299935852940747)
      ·
        refine ⟨50801038015949903779411121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33867358677299935852940747 50801038015949903779411121)
        ·
          refine ⟨38100778511962427834558341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50801038015949903779411121 38100778511962427834558341)
          ·
            refine ⟨7143895970992955218979689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38100778511962427834558341 7143895970992955218979689)
            ·
              refine ⟨5357921978244716414234767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143895970992955218979689 5357921978244716414234767)
              ·
                refine ⟨8036882967367074621352151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357921978244716414234767 8036882967367074621352151)
                ·
                  refine ⟨12055324451050611932028227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036882967367074621352151 12055324451050611932028227)
                  ·
                    refine ⟨18082986676575917898042341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12055324451050611932028227 18082986676575917898042341)
                    ·
                      refine ⟨3390560001857984605882939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18082986676575917898042341 3390560001857984605882939)
                      ·
                        rfl

theorem cell23_6603092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_6603092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603092 prefixEnd_6603092 := by exact prefixLift 6603092
  have htrace : WordTrace (prefixWord ++ tailWord_6603092) baseStart_6603092 baseEnd_6603092 := by
    simpa [prefixWord, tailWord_6603092, baseEnd_6603092] using wordTrace_append hprefix tailTrace_6603092
  have hstable : (prefixWord ++ tailWord_6603092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603092).length < 2 ^ (prefixWord ++ tailWord_6603092).sum := by decide
  have hdescent : baseEnd_6603092 < baseStart_6603092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603125 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6603125 : Nat := 118140960795 + 6603125 * 2 ^ 59
def prefixEnd_6603125 : Nat := 4983230072969 + 3 ^ 40 * 6603125 * 2
def baseEnd_6603125 : Nat := 3390576946719582976770287

theorem tailTrace_6603125 : CollatzResearch.WordTrace tailWord_6603125 prefixEnd_6603125 3390576946719582976770287 := by
  unfold tailWord_6603125
  simp only [CollatzResearch.WordTrace]
  refine ⟨240835754203013323812418829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160557169468675549208279219 240835754203013323812418829)
  ·
    refine ⟨90313407826129996429657061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240835754203013323812418829 90313407826129996429657061)
    ·
      refine ⟨16933763967399374330560699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90313407826129996429657061 16933763967399374330560699)
      ·
        refine ⟨25400645951099061495841049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16933763967399374330560699 25400645951099061495841049)
        ·
          refine ⟨19050484463324296121880787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25400645951099061495841049 19050484463324296121880787)
          ·
            refine ⟨28575726694986444182821181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050484463324296121880787 28575726694986444182821181)
            ·
              refine ⟨10715897510619916568557943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28575726694986444182821181 10715897510619916568557943)
              ·
                refine ⟨16073846265929874852836915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10715897510619916568557943 16073846265929874852836915)
                ·
                  refine ⟨24110769398894812279255373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16073846265929874852836915 24110769398894812279255373)
                  ·
                    refine ⟨9041538524585554604720765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24110769398894812279255373 9041538524585554604720765)
                    ·
                      refine ⟨3390576946719582976770287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041538524585554604720765 3390576946719582976770287)
                      ·
                        rfl

theorem cell23_6603125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6603125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603125 prefixEnd_6603125 := by exact prefixLift 6603125
  have htrace : WordTrace (prefixWord ++ tailWord_6603125) baseStart_6603125 baseEnd_6603125 := by
    simpa [prefixWord, tailWord_6603125, baseEnd_6603125] using wordTrace_append hprefix tailTrace_6603125
  have hstable : (prefixWord ++ tailWord_6603125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603125).length < 2 ^ (prefixWord ++ tailWord_6603125).sum := by decide
  have hdescent : baseEnd_6603125 < baseStart_6603125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603176 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6603176 : Nat := 118140960795 + 6603176 * 2 ^ 59
def prefixEnd_6603176 : Nat := 4983230072969 + 3 ^ 40 * 6603176 * 2
def baseEnd_6603176 : Nat := 3390603134232962277232553

theorem tailTrace_6603176 : CollatzResearch.WordTrace tailWord_6603176 prefixEnd_6603176 3390603134232962277232553 := by
  unfold tailWord_6603176
  simp only [CollatzResearch.WordTrace]
  refine ⟨120418807162914279761262691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160558409550552373015016921 120418807162914279761262691)
  ·
    refine ⟨180628210744371419641894037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120418807162914279761262691 180628210744371419641894037)
    ·
      refine ⟨8466947378642410295713783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180628210744371419641894037 8466947378642410295713783)
      ·
        refine ⟨12700421067963615443570675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466947378642410295713783 12700421067963615443570675)
        ·
          refine ⟨19050631601945423165356013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700421067963615443570675 19050631601945423165356013)
          ·
            refine ⟨7143986850729533687008505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19050631601945423165356013 7143986850729533687008505)
            ·
              refine ⟨5357990138047150265256379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7143986850729533687008505 5357990138047150265256379)
              ·
                refine ⟨8036985207070725397884569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357990138047150265256379 8036985207070725397884569)
                ·
                  refine ⟨6027738905303044048413427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8036985207070725397884569 6027738905303044048413427)
                  ·
                    refine ⟨9041608357954566072620141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6027738905303044048413427 9041608357954566072620141)
                    ·
                      refine ⟨3390603134232962277232553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9041608357954566072620141 3390603134232962277232553)
                      ·
                        rfl

theorem cell23_6603176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6603176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603176 prefixEnd_6603176 := by exact prefixLift 6603176
  have htrace : WordTrace (prefixWord ++ tailWord_6603176) baseStart_6603176 baseEnd_6603176 := by
    simpa [prefixWord, tailWord_6603176, baseEnd_6603176] using wordTrace_append hprefix tailTrace_6603176
  have hstable : (prefixWord ++ tailWord_6603176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603176).length < 2 ^ (prefixWord ++ tailWord_6603176).sum := by decide
  have hdescent : baseEnd_6603176 < baseStart_6603176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603222 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6603222 : Nat := 118140960795 + 6603222 * 2 ^ 59
def prefixEnd_6603222 : Nat := 4983230072969 + 3 ^ 40 * 6603222 * 2
def baseEnd_6603222 : Nat := 376736306038118788584149

theorem tailTrace_6603222 : CollatzResearch.WordTrace tailWord_6603222 prefixEnd_6603222 376736306038118788584149 := by
  unfold tailWord_6603222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052455755228869336168745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160559528055774606252466613 15052455755228869336168745)
  ·
    refine ⟨11289341816421652002126559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15052455755228869336168745 11289341816421652002126559)
    ·
      refine ⟨16934012724632478003189839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11289341816421652002126559 16934012724632478003189839)
      ·
        refine ⟨25401019086948717004784759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16934012724632478003189839 25401019086948717004784759)
        ·
          refine ⟨38101528630423075507177139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25401019086948717004784759 38101528630423075507177139)
          ·
            refine ⟨57152292945634613260765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38101528630423075507177139 57152292945634613260765709)
            ·
              refine ⟨21432109854612979972787141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57152292945634613260765709 21432109854612979972787141)
              ·
                refine ⟨4018520597739933744897589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21432109854612979972787141 4018520597739933744897589)
                ·
                  refine ⟨376736306038118788584149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4018520597739933744897589 376736306038118788584149)
                  ·
                    rfl

theorem cell23_6603222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6603222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603222 prefixEnd_6603222 := by exact prefixLift 6603222
  have htrace : WordTrace (prefixWord ++ tailWord_6603222) baseStart_6603222 baseEnd_6603222 := by
    simpa [prefixWord, tailWord_6603222, baseEnd_6603222] using wordTrace_append hprefix tailTrace_6603222
  have hstable : (prefixWord ++ tailWord_6603222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603222).length < 2 ^ (prefixWord ++ tailWord_6603222).sum := by decide
  have hdescent : baseEnd_6603222 < baseStart_6603222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603298 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6603298 : Nat := 118140960795 + 6603298 * 2 ^ 59
def prefixEnd_6603298 : Nat := 4983230072969 + 3 ^ 40 * 6603298 * 2
def baseEnd_6603298 : Nat := 3390665778872810799906991

theorem tailTrace_6603298 : CollatzResearch.WordTrace tailWord_6603298 prefixEnd_6603298 3390665778872810799906991 := by
  unfold tailWord_6603298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60210516007846643589616637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160561376020924382905644365 60210516007846643589616637)
  ·
    refine ⟨22578943502942491346106239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60210516007846643589616637 22578943502942491346106239)
    ·
      refine ⟨33868415254413737019159359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22578943502942491346106239 33868415254413737019159359)
      ·
        refine ⟨50802622881620605528739039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33868415254413737019159359 50802622881620605528739039)
        ·
          refine ⟨76203934322430908293108559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50802622881620605528739039 76203934322430908293108559)
          ·
            refine ⟨114305901483646362439662839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76203934322430908293108559 114305901483646362439662839)
            ·
              refine ⟨171458852225469543659494259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114305901483646362439662839 171458852225469543659494259)
              ·
                refine ⟨257188278338204315489241389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171458852225469543659494259 257188278338204315489241389)
                ·
                  refine ⟨96445604376826618308465521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257188278338204315489241389 96445604376826618308465521)
                  ·
                    refine ⟨72334203282619963731349141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96445604376826618308465521 72334203282619963731349141)
                    ·
                      refine ⟨3390665778872810799906991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72334203282619963731349141 3390665778872810799906991)
                      ·
                        rfl

theorem cell23_6603298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6603298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603298 prefixEnd_6603298 := by exact prefixLift 6603298
  have htrace : WordTrace (prefixWord ++ tailWord_6603298) baseStart_6603298 baseEnd_6603298 := by
    simpa [prefixWord, tailWord_6603298, baseEnd_6603298] using wordTrace_append hprefix tailTrace_6603298
  have hstable : (prefixWord ++ tailWord_6603298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603298).length < 2 ^ (prefixWord ++ tailWord_6603298).sum := by decide
  have hdescent : baseEnd_6603298 < baseStart_6603298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603308 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_6603308 : Nat := 118140960795 + 6603308 * 2 ^ 59
def prefixEnd_6603308 : Nat := 4983230072969 + 3 ^ 40 * 6603308 * 2
def baseEnd_6603308 : Nat := 1130223637893118586927315

theorem tailTrace_6603308 : CollatzResearch.WordTrace tailWord_6603308 prefixEnd_6603308 1130223637893118586927315 := by
  unfold tailWord_6603308
  simp only [CollatzResearch.WordTrace]
  refine ⟨120421214380675173033165289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160561619174233564044220385 120421214380675173033165289)
  ·
    refine ⟨90315910785506379774873967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120421214380675173033165289 90315910785506379774873967)
    ·
      refine ⟨135473866178259569662310951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90315910785506379774873967 135473866178259569662310951)
      ·
        refine ⟨203210799267389354493466427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135473866178259569662310951 203210799267389354493466427)
        ·
          refine ⟨304816198901084031740199641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203210799267389354493466427 304816198901084031740199641)
          ·
            refine ⟨228612149175813023805149731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304816198901084031740199641 228612149175813023805149731)
            ·
              refine ⟨342918223763719535707724597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228612149175813023805149731 342918223763719535707724597)
              ·
                refine ⟨32148583477848706472599181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342918223763719535707724597 32148583477848706472599181)
                ·
                  refine ⟨12055718804193264927224693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32148583477848706472599181 12055718804193264927224693)
                  ·
                    refine ⟨1130223637893118586927315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12055718804193264927224693 1130223637893118586927315)
                    ·
                      rfl

theorem cell23_6603308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_6603308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603308 prefixEnd_6603308 := by exact prefixLift 6603308
  have htrace : WordTrace (prefixWord ++ tailWord_6603308) baseStart_6603308 baseEnd_6603308 := by
    simpa [prefixWord, tailWord_6603308, baseEnd_6603308] using wordTrace_append hprefix tailTrace_6603308
  have hstable : (prefixWord ++ tailWord_6603308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603308).length < 2 ^ (prefixWord ++ tailWord_6603308).sum := by decide
  have hdescent : baseEnd_6603308 < baseStart_6603308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603315 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 1, 5, 2]
def baseStart_6603315 : Nat := 118140960795 + 6603315 * 2 ^ 59
def prefixEnd_6603315 : Nat := 4983230072969 + 3 ^ 40 * 6603315 * 2
def baseEnd_6603315 : Nat := 3390674508043937233394413

theorem tailTrace_6603315 : CollatzResearch.WordTrace tailWord_6603315 prefixEnd_6603315 3390674508043937233394413 := by
  unfold tailWord_6603315
  simp only [CollatzResearch.WordTrace]
  refine ⟨240842684072324986261835399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160561789381549990841223599 240842684072324986261835399)
  ·
    refine ⟨361264026108487479392753099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240842684072324986261835399 361264026108487479392753099)
    ·
      refine ⟨541896039162731219089129649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361264026108487479392753099 541896039162731219089129649)
      ·
        refine ⟨406422029372048414316847237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541896039162731219089129649 406422029372048414316847237)
        ·
          refine ⟨76204130507259077684408857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406422029372048414316847237 76204130507259077684408857)
          ·
            refine ⟨57153097880444308263306643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76204130507259077684408857 57153097880444308263306643)
            ·
              refine ⟨85729646820666462394959965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57153097880444308263306643 85729646820666462394959965)
              ·
                refine ⟨32148617557749923398109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85729646820666462394959965 32148617557749923398109987)
                ·
                  refine ⟨48222926336624885097164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32148617557749923398109987 48222926336624885097164981)
                  ·
                    refine ⟨4520899344058582977859217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48222926336624885097164981 4520899344058582977859217)
                    ·
                      refine ⟨3390674508043937233394413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520899344058582977859217 3390674508043937233394413)
                      ·
                        rfl

theorem cell23_6603315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5, 2].length) (baseStart_6603315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603315 prefixEnd_6603315 := by exact prefixLift 6603315
  have htrace : WordTrace (prefixWord ++ tailWord_6603315) baseStart_6603315 baseEnd_6603315 := by
    simpa [prefixWord, tailWord_6603315, baseEnd_6603315] using wordTrace_append hprefix tailTrace_6603315
  have hstable : (prefixWord ++ tailWord_6603315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603315).length < 2 ^ (prefixWord ++ tailWord_6603315).sum := by decide
  have hdescent : baseEnd_6603315 < baseStart_6603315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603389 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_6603389 : Nat := 118140960795 + 6603389 * 2 ^ 59
def prefixEnd_6603389 : Nat := 4983230072969 + 3 ^ 40 * 6603389 * 2
def baseEnd_6603389 : Nat := 1130237501870789981289691

theorem tailTrace_6603389 : CollatzResearch.WordTrace tailWord_6603389 prefixEnd_6603389 1130237501870789981289691 := by
  unfold tailWord_6603389
  simp only [CollatzResearch.WordTrace]
  refine ⟨240845383074056896900029221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160563588716037931266686147 240845383074056896900029221)
  ·
    refine ⟨45158509326385668168755479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240845383074056896900029221 45158509326385668168755479)
    ·
      refine ⟨67737763989578502253133219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45158509326385668168755479 67737763989578502253133219)
      ·
        refine ⟨101606645984367753379699829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67737763989578502253133219 101606645984367753379699829)
        ·
          refine ⟨9525623061034476879346859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101606645984367753379699829 9525623061034476879346859)
          ·
            refine ⟨14288434591551715319020289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525623061034476879346859 14288434591551715319020289)
            ·
              refine ⟨10716325943663786489265217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14288434591551715319020289 10716325943663786489265217)
              ·
                refine ⟨8037244457747839866948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10716325943663786489265217 8037244457747839866948913)
                ·
                  refine ⟨6027933343310879900211685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8037244457747839866948913 6027933343310879900211685)
                  ·
                    refine ⟨1130237501870789981289691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6027933343310879900211685 1130237501870789981289691)
                    ·
                      rfl

theorem cell23_6603389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_6603389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603389 prefixEnd_6603389 := by exact prefixLift 6603389
  have htrace : WordTrace (prefixWord ++ tailWord_6603389) baseStart_6603389 baseEnd_6603389 := by
    simpa [prefixWord, tailWord_6603389, baseEnd_6603389] using wordTrace_append hprefix tailTrace_6603389
  have hstable : (prefixWord ++ tailWord_6603389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603389).length < 2 ^ (prefixWord ++ tailWord_6603389).sum := by decide
  have hdescent : baseEnd_6603389 < baseStart_6603389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603402 : List Nat := [3, 1, 2, 3, 3, 2, 1, 8]
def baseStart_6603402 : Nat := 118140960795 + 6603402 * 2 ^ 59
def prefixEnd_6603402 : Nat := 4983230072969 + 3 ^ 40 * 6603402 * 2
def baseEnd_6603402 : Nat := 125582191883736236778019

theorem tailTrace_6603402 : CollatzResearch.WordTrace tailWord_6603402 prefixEnd_6603402 125582191883736236778019 := by
  unfold tailWord_6603402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60211464305752450030063115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160563904815339866746834973 60211464305752450030063115)
  ·
    refine ⟨90317196458628675045094673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60211464305752450030063115 90317196458628675045094673)
    ·
      refine ⟨67737897343971506283821005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90317196458628675045094673 67737897343971506283821005)
      ·
        refine ⟨25401711503989314856432877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67737897343971506283821005 25401711503989314856432877)
        ·
          refine ⟨9525641813995993071162329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25401711503989314856432877 9525641813995993071162329)
          ·
            refine ⟨7144231360496994803371747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9525641813995993071162329 7144231360496994803371747)
            ·
              refine ⟨10716347040745492205057621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144231360496994803371747 10716347040745492205057621)
              ·
                refine ⟨125582191883736236778019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10716347040745492205057621 125582191883736236778019)
                ·
                  rfl

theorem cell23_6603402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_6603402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603402 prefixEnd_6603402 := by exact prefixLift 6603402
  have htrace : WordTrace (prefixWord ++ tailWord_6603402) baseStart_6603402 baseEnd_6603402 := by
    simpa [prefixWord, tailWord_6603402, baseEnd_6603402] using wordTrace_append hprefix tailTrace_6603402
  have hstable : (prefixWord ++ tailWord_6603402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603402).length < 2 ^ (prefixWord ++ tailWord_6603402).sum := by decide
  have hdescent : baseEnd_6603402 < baseStart_6603402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603408 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_6603408 : Nat := 118140960795 + 6603408 * 2 ^ 59
def prefixEnd_6603408 : Nat := 4983230072969 + 3 ^ 40 * 6603408 * 2
def baseEnd_6603408 : Nat := 3390722261744805369531485

theorem tailTrace_6603408 : CollatzResearch.WordTrace tailWord_6603408 prefixEnd_6603408 3390722261744805369531485 := by
  unfold tailWord_6603408
  simp only [CollatzResearch.WordTrace]
  refine ⟨120423038030494031572485439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160564050707325375429980585 120423038030494031572485439)
  ·
    refine ⟨180634557045741047358728159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120423038030494031572485439 180634557045741047358728159)
    ·
      refine ⟨270951835568611571038092239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180634557045741047358728159 270951835568611571038092239)
      ·
        refine ⟨406427753352917356557138359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270951835568611571038092239 406427753352917356557138359)
        ·
          refine ⟨609641630029376034835707539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406427753352917356557138359 609641630029376034835707539)
          ·
            refine ⟨914462445044064052253561309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609641630029376034835707539 914462445044064052253561309)
            ·
              refine ⟨342923416891524019595085491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914462445044064052253561309 342923416891524019595085491)
              ·
                refine ⟨514385125337286029392628237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342923416891524019595085491 514385125337286029392628237)
                ·
                  refine ⟨192894422001482261022235589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514385125337286029392628237 192894422001482261022235589)
                  ·
                    refine ⟨36167704125277923941669173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192894422001482261022235589 36167704125277923941669173)
                    ·
                      refine ⟨3390722261744805369531485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36167704125277923941669173 3390722261744805369531485)
                      ·
                        rfl

theorem cell23_6603408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_6603408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603408 prefixEnd_6603408 := by exact prefixLift 6603408
  have htrace : WordTrace (prefixWord ++ tailWord_6603408) baseStart_6603408 baseEnd_6603408 := by
    simpa [prefixWord, tailWord_6603408, baseEnd_6603408] using wordTrace_append hprefix tailTrace_6603408
  have hstable : (prefixWord ++ tailWord_6603408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603408).length < 2 ^ (prefixWord ++ tailWord_6603408).sum := by decide
  have hdescent : baseEnd_6603408 < baseStart_6603408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603439 : List Nat := [1, 1, 2, 1, 2, 6, 1, 3, 1, 3, 2]
def baseStart_6603439 : Nat := 118140960795 + 6603439 * 2 ^ 59
def prefixEnd_6603439 : Nat := 4983230072969 + 3 ^ 40 * 6603439 * 2
def baseEnd_6603439 : Nat := 3390738179645094748243843

theorem tailTrace_6603439 : CollatzResearch.WordTrace tailWord_6603439 prefixEnd_6603439 3390738179645094748243843 := by
  unfold tailWord_6603439
  simp only [CollatzResearch.WordTrace]
  refine ⟨240847206723875755439349371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160564804482583836959566247 240847206723875755439349371)
  ·
    refine ⟨361270810085813633159024057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240847206723875755439349371 361270810085813633159024057)
    ·
      refine ⟨270953107564360224869268043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361270810085813633159024057 270953107564360224869268043)
      ·
        refine ⟨406429661346540337303902065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270953107564360224869268043 406429661346540337303902065)
        ·
          refine ⟨304822246009905252977926549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406429661346540337303902065 304822246009905252977926549)
          ·
            refine ⟨14288542781714308733340307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304822246009905252977926549 14288542781714308733340307)
            ·
              refine ⟨21432814172571463100010461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14288542781714308733340307 21432814172571463100010461)
              ·
                refine ⟨8037305314714298662503923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21432814172571463100010461 8037305314714298662503923)
                ·
                  refine ⟨12055957972071447993755885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8037305314714298662503923 12055957972071447993755885)
                  ·
                    refine ⟨4520984239526792997658457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12055957972071447993755885 4520984239526792997658457)
                    ·
                      refine ⟨3390738179645094748243843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4520984239526792997658457 3390738179645094748243843)
                      ·
                        rfl

theorem cell23_6603439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 3, 2].length) (baseStart_6603439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603439 prefixEnd_6603439 := by exact prefixLift 6603439
  have htrace : WordTrace (prefixWord ++ tailWord_6603439) baseStart_6603439 baseEnd_6603439 := by
    simpa [prefixWord, tailWord_6603439, baseEnd_6603439] using wordTrace_append hprefix tailTrace_6603439
  have hstable : (prefixWord ++ tailWord_6603439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603439).length < 2 ^ (prefixWord ++ tailWord_6603439).sum := by decide
  have hdescent : baseEnd_6603439 < baseStart_6603439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603512 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_6603512 : Nat := 118140960795 + 6603512 * 2 ^ 59
def prefixEnd_6603512 : Nat := 4983230072969 + 3 ^ 40 * 6603512 * 2
def baseEnd_6603512 : Nat := 3390775663732872962631007

theorem tailTrace_6603512 : CollatzResearch.WordTrace tailWord_6603512 prefixEnd_6603512 3390775663732872962631007 := by
  unfold tailWord_6603512
  simp only [CollatzResearch.WordTrace]
  refine ⟨120424934626305644453378395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160566579501740859271171193 120424934626305644453378395)
  ·
    refine ⟨180637401939458466680067593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120424934626305644453378395 180637401939458466680067593)
    ·
      refine ⟨135478051454593850010050695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180637401939458466680067593 135478051454593850010050695)
      ·
        refine ⟨203217077181890775015076043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135478051454593850010050695 203217077181890775015076043)
        ·
          refine ⟨304825615772836162522614065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203217077181890775015076043 304825615772836162522614065)
          ·
            refine ⟨228619211829627121891960549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304825615772836162522614065 228619211829627121891960549)
            ·
              refine ⟨42866102218055085354742603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228619211829627121891960549 42866102218055085354742603)
              ·
                refine ⟨64299153327082628032113905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42866102218055085354742603 64299153327082628032113905)
                ·
                  refine ⟨48224364995311971024085429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64299153327082628032113905 48224364995311971024085429)
                  ·
                    refine ⟨4521034218310497283508009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48224364995311971024085429 4521034218310497283508009)
                    ·
                      refine ⟨3390775663732872962631007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521034218310497283508009 3390775663732872962631007)
                      ·
                        rfl

theorem cell23_6603512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_6603512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603512 prefixEnd_6603512 := by exact prefixLift 6603512
  have htrace : WordTrace (prefixWord ++ tailWord_6603512) baseStart_6603512 baseEnd_6603512 := by
    simpa [prefixWord, tailWord_6603512, baseEnd_6603512] using wordTrace_append hprefix tailTrace_6603512
  have hstable : (prefixWord ++ tailWord_6603512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603512).length < 2 ^ (prefixWord ++ tailWord_6603512).sum := by decide
  have hdescent : baseEnd_6603512 < baseStart_6603512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603525 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_6603525 : Nat := 118140960795 + 6603525 * 2 ^ 59
def prefixEnd_6603525 : Nat := 4983230072969 + 3 ^ 40 * 6603525 * 2
def baseEnd_6603525 : Nat := 3390782338981381411768447

theorem tailTrace_6603525 : CollatzResearch.WordTrace tailWord_6603525 prefixEnd_6603525 3390782338981381411768447 := by
  unfold tailWord_6603525
  simp only [CollatzResearch.WordTrace]
  refine ⟨240850343401564192126980029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160566895601042794751320019 240850343401564192126980029)
  ·
    refine ⟨90318878775586572047617511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240850343401564192126980029 90318878775586572047617511)
    ·
      refine ⟨135478318163379858071426267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90318878775586572047617511 135478318163379858071426267)
      ·
        refine ⟨203217477245069787107139401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135478318163379858071426267 203217477245069787107139401)
        ·
          refine ⟨152413107933802340330354551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203217477245069787107139401 152413107933802340330354551)
          ·
            refine ⟨228619661900703510495531827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152413107933802340330354551 228619661900703510495531827)
            ·
              refine ⟨342929492851055265743297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228619661900703510495531827 342929492851055265743297741)
              ·
                refine ⟨128598559819145724653736653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342929492851055265743297741 128598559819145724653736653)
                ·
                  refine ⟨48224459932179646745151245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128598559819145724653736653 48224459932179646745151245)
                  ·
                    refine ⟨18084172474567367529431717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48224459932179646745151245 18084172474567367529431717)
                    ·
                      refine ⟨3390782338981381411768447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18084172474567367529431717 3390782338981381411768447)
                      ·
                        rfl

theorem cell23_6603525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_6603525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603525 prefixEnd_6603525 := by exact prefixLift 6603525
  have htrace : WordTrace (prefixWord ++ tailWord_6603525) baseStart_6603525 baseEnd_6603525 := by
    simpa [prefixWord, tailWord_6603525, baseEnd_6603525] using wordTrace_append hprefix tailTrace_6603525
  have hstable : (prefixWord ++ tailWord_6603525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603525).length < 2 ^ (prefixWord ++ tailWord_6603525).sum := by decide
  have hdescent : baseEnd_6603525 < baseStart_6603525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603555 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_6603555 : Nat := 118140960795 + 6603555 * 2 ^ 59
def prefixEnd_6603555 : Nat := 4983230072969 + 3 ^ 40 * 6603555 * 2
def baseEnd_6603555 : Nat := 3390797743401016294393309

theorem tailTrace_6603555 : CollatzResearch.WordTrace tailWord_6603555 prefixEnd_6603555 3390797743401016294393309 := by
  unfold tailWord_6603555
  simp only [CollatzResearch.WordTrace]
  refine ⟨240851437591455507250572119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160567625060970338167048079 240851437591455507250572119)
  ·
    refine ⟨361277156387183260875858179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240851437591455507250572119 361277156387183260875858179)
    ·
      refine ⟨541915734580774891313787269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361277156387183260875858179 541915734580774891313787269)
      ·
        refine ⟨101609200233895292121335113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541915734580774891313787269 101609200233895292121335113)
        ·
          refine ⟨76206900175421469091001335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101609200233895292121335113 76206900175421469091001335)
          ·
            refine ⟨114310350263132203636502003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76206900175421469091001335 114310350263132203636502003)
            ·
              refine ⟨171465525394698305454753005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114310350263132203636502003 171465525394698305454753005)
              ·
                refine ⟨64299572023011864545532377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171465525394698305454753005 64299572023011864545532377)
                ·
                  refine ⟨48224679017258898409149283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64299572023011864545532377 48224679017258898409149283)
                  ·
                    refine ⟨72337018525888347613723925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48224679017258898409149283 72337018525888347613723925)
                    ·
                      refine ⟨3390797743401016294393309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72337018525888347613723925 3390797743401016294393309)
                      ·
                        rfl

theorem cell23_6603555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_6603555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603555 prefixEnd_6603555 := by exact prefixLift 6603555
  have htrace : WordTrace (prefixWord ++ tailWord_6603555) baseStart_6603555 baseEnd_6603555 := by
    simpa [prefixWord, tailWord_6603555, baseEnd_6603555] using wordTrace_append hprefix tailTrace_6603555
  have hstable : (prefixWord ++ tailWord_6603555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603555).length < 2 ^ (prefixWord ++ tailWord_6603555).sum := by decide
  have hdescent : baseEnd_6603555 < baseStart_6603555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603590 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_6603590 : Nat := 118140960795 + 6603590 * 2 ^ 59
def prefixEnd_6603590 : Nat := 4983230072969 + 3 ^ 40 * 6603590 * 2
def baseEnd_6603590 : Nat := 1130271905074641219151883

theorem tailTrace_6603590 : CollatzResearch.WordTrace tailWord_6603590 prefixEnd_6603590 1130271905074641219151883 := by
  unfold tailWord_6603590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526647317072772132128007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160568476097552472152064149 7526647317072772132128007)
  ·
    refine ⟨11289970975609158198192011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7526647317072772132128007 11289970975609158198192011)
    ·
      refine ⟨16934956463413737297288017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11289970975609158198192011 16934956463413737297288017)
      ·
        refine ⟨12701217347560302972966013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16934956463413737297288017 12701217347560302972966013)
        ·
          refine ⟨4762956505335113614862255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12701217347560302972966013 4762956505335113614862255)
          ·
            refine ⟨7144434758002670422293383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762956505335113614862255 7144434758002670422293383)
            ·
              refine ⟨10716652137004005633440075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144434758002670422293383 10716652137004005633440075)
              ·
                refine ⟨16074978205506008450160113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716652137004005633440075 16074978205506008450160113)
                ·
                  refine ⟨12056233654129506337620085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16074978205506008450160113 12056233654129506337620085)
                  ·
                    refine ⟨1130271905074641219151883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12056233654129506337620085 1130271905074641219151883)
                    ·
                      rfl

theorem cell23_6603590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_6603590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603590 prefixEnd_6603590 := by exact prefixLift 6603590
  have htrace : WordTrace (prefixWord ++ tailWord_6603590) baseStart_6603590 baseEnd_6603590 := by
    simpa [prefixWord, tailWord_6603590, baseEnd_6603590] using wordTrace_append hprefix tailTrace_6603590
  have hstable : (prefixWord ++ tailWord_6603590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603590).length < 2 ^ (prefixWord ++ tailWord_6603590).sum := by decide
  have hdescent : baseEnd_6603590 < baseStart_6603590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603596 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6603596 : Nat := 118140960795 + 6603596 * 2 ^ 59
def prefixEnd_6603596 : Nat := 4983230072969 + 3 ^ 40 * 6603596 * 2
def baseEnd_6603596 : Nat := 3390818796107850633980621

theorem tailTrace_6603596 : CollatzResearch.WordTrace tailWord_6603596 prefixEnd_6603596 3390818796107850633980621 := by
  unfold tailWord_6603596
  simp only [CollatzResearch.WordTrace]
  refine ⟨120426466492153485626407321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160568621989537980835209761 120426466492153485626407321)
  ·
    refine ⟨90319849869115114219805491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120426466492153485626407321 90319849869115114219805491)
    ·
      refine ⟨135479774803672671329708237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90319849869115114219805491 135479774803672671329708237)
      ·
        refine ⟨50804915551377251748640589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135479774803672671329708237 50804915551377251748640589)
        ·
          refine ⟨19051843331766469405740221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50804915551377251748640589 19051843331766469405740221)
          ·
            refine ⟨7144441249412426027152583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19051843331766469405740221 7144441249412426027152583)
            ·
              refine ⟨10716661874118639040728875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144441249412426027152583 10716661874118639040728875)
              ·
                refine ⟨16074992811177958561093313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716661874118639040728875 16074992811177958561093313)
                ·
                  refine ⟨12056244608383468920819985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16074992811177958561093313 12056244608383468920819985)
                  ·
                    refine ⟨9042183456287601690614989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12056244608383468920819985 9042183456287601690614989)
                    ·
                      refine ⟨3390818796107850633980621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9042183456287601690614989 3390818796107850633980621)
                      ·
                        rfl

theorem cell23_6603596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6603596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603596 prefixEnd_6603596 := by exact prefixLift 6603596
  have htrace : WordTrace (prefixWord ++ tailWord_6603596) baseStart_6603596 baseEnd_6603596 := by
    simpa [prefixWord, tailWord_6603596, baseEnd_6603596] using wordTrace_append hprefix tailTrace_6603596
  have hstable : (prefixWord ++ tailWord_6603596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603596).length < 2 ^ (prefixWord ++ tailWord_6603596).sum := by decide
  have hdescent : baseEnd_6603596 < baseStart_6603596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603625 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_6603625 : Nat := 118140960795 + 6603625 * 2 ^ 59
def prefixEnd_6603625 : Nat := 4983230072969 + 3 ^ 40 * 6603625 * 2
def baseEnd_6603625 : Nat := 1130277895682277006839329

theorem tailTrace_6603625 : CollatzResearch.WordTrace tailWord_6603625 prefixEnd_6603625 1130277895682277006839329 := by
  unfold tailWord_6603625
  simp only [CollatzResearch.WordTrace]
  refine ⟨240853990701201909205620329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160569327134134606137080219 240853990701201909205620329)
  ·
    refine ⟨180640493025901431904215247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240853990701201909205620329 180640493025901431904215247)
    ·
      refine ⟨270960739538852147856322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180640493025901431904215247 270960739538852147856322871)
      ·
        refine ⟨406441109308278221784484307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270960739538852147856322871 406441109308278221784484307)
        ·
          refine ⟨609661663962417332676726461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406441109308278221784484307 609661663962417332676726461)
          ·
            refine ⟨228623123985906499753772423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609661663962417332676726461 228623123985906499753772423)
            ·
              refine ⟨342934685978859749630658635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228623123985906499753772423 342934685978859749630658635)
              ·
                refine ⟨514402028968289624445987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342934685978859749630658635 514402028968289624445987953)
                ·
                  refine ⟨385801521726217218334490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514402028968289624445987953 385801521726217218334490965)
                  ·
                    refine ⟨1130277895682277006839329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 385801521726217218334490965 1130277895682277006839329)
                    ·
                      rfl

theorem cell23_6603625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_6603625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603625 prefixEnd_6603625 := by exact prefixLift 6603625
  have htrace : WordTrace (prefixWord ++ tailWord_6603625) baseStart_6603625 baseEnd_6603625 := by
    simpa [prefixWord, tailWord_6603625, baseEnd_6603625] using wordTrace_append hprefix tailTrace_6603625
  have hstable : (prefixWord ++ tailWord_6603625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603625).length < 2 ^ (prefixWord ++ tailWord_6603625).sum := by decide
  have hdescent : baseEnd_6603625 < baseStart_6603625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603632 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_6603632 : Nat := 118140960795 + 6603632 * 2 ^ 59
def prefixEnd_6603632 : Nat := 4983230072969 + 3 ^ 40 * 6603632 * 2
def baseEnd_6603632 : Nat := 3390837281411412493130455

theorem tailTrace_6603632 : CollatzResearch.WordTrace tailWord_6603632 prefixEnd_6603632 3390837281411412493130455 := by
  unfold tailWord_6603632
  simp only [CollatzResearch.WordTrace]
  refine ⟨120427123006088274700562575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160569497341451032934083433 120427123006088274700562575)
  ·
    refine ⟨180640684509132412050843863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120427123006088274700562575 180640684509132412050843863)
    ·
      refine ⟨270961026763698618076265795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180640684509132412050843863 270961026763698618076265795)
      ·
        refine ⟨406441540145547927114398693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270961026763698618076265795 406441540145547927114398693)
        ·
          refine ⟨76207788777290236333949755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406441540145547927114398693 76207788777290236333949755)
          ·
            refine ⟨114311683165935354500924633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76207788777290236333949755 114311683165935354500924633)
            ·
              refine ⟨85733762374451515875693475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114311683165935354500924633 85733762374451515875693475)
              ·
                refine ⟨128600643561677273813540213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85733762374451515875693475 128600643561677273813540213)
                ·
                  refine ⟨12056310333907244420019395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128600643561677273813540213 12056310333907244420019395)
                  ·
                    refine ⟨18084465500860866630029093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12056310333907244420019395 18084465500860866630029093)
                    ·
                      refine ⟨3390837281411412493130455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18084465500860866630029093 3390837281411412493130455)
                      ·
                        rfl

theorem cell23_6603632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_6603632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603632 prefixEnd_6603632 := by exact prefixLift 6603632
  have htrace : WordTrace (prefixWord ++ tailWord_6603632) baseStart_6603632 baseEnd_6603632 := by
    simpa [prefixWord, tailWord_6603632, baseEnd_6603632] using wordTrace_append hprefix tailTrace_6603632
  have hstable : (prefixWord ++ tailWord_6603632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603632).length < 2 ^ (prefixWord ++ tailWord_6603632).sum := by decide
  have hdescent : baseEnd_6603632 < baseStart_6603632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6603652 : Nat := 118140960795 + 6603652 * 2 ^ 59
def prefixEnd_6603652 : Nat := 4983230072969 + 3 ^ 40 * 6603652 * 2
def baseEnd_6603652 : Nat := 3390847551024502414880363

theorem tailTrace_6603652 : CollatzResearch.WordTrace tailWord_6603652 prefixEnd_6603652 3390847551024502414880363 := by
  unfold tailWord_6603652
  simp only [CollatzResearch.WordTrace]
  refine ⟨120427487736052046408426605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160569983648069395211235473 120427487736052046408426605)
  ·
    refine ⟨45160307901019517403159977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120427487736052046408426605 45160307901019517403159977)
    ·
      refine ⟨33870230925764638052369983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45160307901019517403159977 33870230925764638052369983)
      ·
        refine ⟨50805346388646957078554975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33870230925764638052369983 50805346388646957078554975)
        ·
          refine ⟨76208019582970435617832463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50805346388646957078554975 76208019582970435617832463)
          ·
            refine ⟨114312029374455653426748695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76208019582970435617832463 114312029374455653426748695)
            ·
              refine ⟨171468044061683480140123043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114312029374455653426748695 171468044061683480140123043)
              ·
                refine ⟨257202066092525220210184565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171468044061683480140123043 257202066092525220210184565)
                ·
                  refine ⟨24112693696174239394704803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257202066092525220210184565 24112693696174239394704803)
                  ·
                    refine ⟨36169040544261359092057205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24112693696174239394704803 36169040544261359092057205)
                    ·
                      refine ⟨3390847551024502414880363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36169040544261359092057205 3390847551024502414880363)
                      ·
                        rfl

theorem cell23_6603652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6603652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603652 prefixEnd_6603652 := by exact prefixLift 6603652
  have htrace : WordTrace (prefixWord ++ tailWord_6603652) baseStart_6603652 baseEnd_6603652 := by
    simpa [prefixWord, tailWord_6603652, baseEnd_6603652] using wordTrace_append hprefix tailTrace_6603652
  have hstable : (prefixWord ++ tailWord_6603652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603652).length < 2 ^ (prefixWord ++ tailWord_6603652).sum := by decide
  have hdescent : baseEnd_6603652 < baseStart_6603652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603669 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_6603669 : Nat := 118140960795 + 6603669 * 2 ^ 59
def prefixEnd_6603669 : Nat := 4983230072969 + 3 ^ 40 * 6603669 * 2
def baseEnd_6603669 : Nat := 3390856280195628848367785

theorem tailTrace_6603669 : CollatzResearch.WordTrace tailWord_6603669 prefixEnd_6603669 3390856280195628848367785 := by
  unfold tailWord_6603669
  simp only [CollatzResearch.WordTrace]
  refine ⟨240855595513042504720222061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160570397008695003146814707 240855595513042504720222061)
  ·
    refine ⟨90320848317390939270083273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240855595513042504720222061 90320848317390939270083273)
    ·
      refine ⟨67740636238043204452562455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90320848317390939270083273 67740636238043204452562455)
      ·
        refine ⟨101610954357064806678843683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67740636238043204452562455 101610954357064806678843683)
        ·
          refine ⟨152416431535597210018265525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101610954357064806678843683 152416431535597210018265525)
          ·
            refine ⟨14289040456462238439212393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152416431535597210018265525 14289040456462238439212393)
            ·
              refine ⟨10716780342346678829409295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14289040456462238439212393 10716780342346678829409295)
              ·
                refine ⟨16075170513520018244113943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716780342346678829409295 16075170513520018244113943)
                ·
                  refine ⟨24112755770280027366170915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16075170513520018244113943 24112755770280027366170915)
                  ·
                    refine ⟨36169133655420041049256373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24112755770280027366170915 36169133655420041049256373)
                    ·
                      refine ⟨3390856280195628848367785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36169133655420041049256373 3390856280195628848367785)
                      ·
                        rfl

theorem cell23_6603669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_6603669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603669 prefixEnd_6603669 := by exact prefixLift 6603669
  have htrace : WordTrace (prefixWord ++ tailWord_6603669) baseStart_6603669 baseEnd_6603669 := by
    simpa [prefixWord, tailWord_6603669, baseEnd_6603669] using wordTrace_append hprefix tailTrace_6603669
  have hstable : (prefixWord ++ tailWord_6603669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603669).length < 2 ^ (prefixWord ++ tailWord_6603669).sum := by decide
  have hdescent : baseEnd_6603669 < baseStart_6603669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603670 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6603670 : Nat := 118140960795 + 6603670 * 2 ^ 59
def prefixEnd_6603670 : Nat := 4983230072969 + 3 ^ 40 * 6603670 * 2
def baseEnd_6603670 : Nat := 3390856793676283344455281

theorem tailTrace_6603670 : CollatzResearch.WordTrace tailWord_6603670 prefixEnd_6603670 3390856793676283344455281 := by
  unfold tailWord_6603670
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053476999127430118188029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160570421324025921260672309 15053476999127430118188029)
  ·
    refine ⟨5645053874672786294320511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15053476999127430118188029 5645053874672786294320511)
    ·
      refine ⟨8467580812009179441480767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645053874672786294320511 8467580812009179441480767)
      ·
        refine ⟨12701371218013769162221151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8467580812009179441480767 12701371218013769162221151)
        ·
          refine ⟨19052056827020653743331727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701371218013769162221151 19052056827020653743331727)
          ·
            refine ⟨28578085240530980614997591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19052056827020653743331727 28578085240530980614997591)
            ·
              refine ⟨42867127860796470922496387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28578085240530980614997591 42867127860796470922496387)
              ·
                refine ⟨64300691791194706383744581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42867127860796470922496387 64300691791194706383744581)
                ·
                  refine ⟨12056379710849007446952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64300691791194706383744581 12056379710849007446952109)
                  ·
                    refine ⟨4521142391568377792607041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12056379710849007446952109 4521142391568377792607041)
                    ·
                      refine ⟨3390856793676283344455281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521142391568377792607041 3390856793676283344455281)
                      ·
                        rfl

theorem cell23_6603670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6603670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603670 prefixEnd_6603670 := by exact prefixLift 6603670
  have htrace : WordTrace (prefixWord ++ tailWord_6603670) baseStart_6603670 baseEnd_6603670 := by
    simpa [prefixWord, tailWord_6603670, baseEnd_6603670] using wordTrace_append hprefix tailTrace_6603670
  have hstable : (prefixWord ++ tailWord_6603670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603670).length < 2 ^ (prefixWord ++ tailWord_6603670).sum := by decide
  have hdescent : baseEnd_6603670 < baseStart_6603670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603683 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 1, 2, 2]
def baseStart_6603683 : Nat := 118140960795 + 6603683 * 2 ^ 59
def prefixEnd_6603683 : Nat := 4983230072969 + 3 ^ 40 * 6603683 * 2
def baseEnd_6603683 : Nat := 3390863468924791793592721

theorem tailTrace_6603683 : CollatzResearch.WordTrace tailWord_6603683 prefixEnd_6603683 3390863468924791793592721 := by
  unfold tailWord_6603683
  simp only [CollatzResearch.WordTrace]
  refine ⟨240856106134991785111231703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160570737423327856740821135 240856106134991785111231703)
  ·
    refine ⟨361284159202487677666847555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240856106134991785111231703 361284159202487677666847555)
    ·
      refine ⟨541926238803731516500271333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361284159202487677666847555 541926238803731516500271333)
      ·
        refine ⟨101611169775699659343800875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541926238803731516500271333 101611169775699659343800875)
        ·
          refine ⟨152416754663549489015701313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101611169775699659343800875 152416754663549489015701313)
          ·
            refine ⟨114312565997662116761775985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152416754663549489015701313 114312565997662116761775985)
            ·
              refine ⟨85734424498246587571331989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114312565997662116761775985 85734424498246587571331989)
              ·
                refine ⟨4018801148355308792406187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85734424498246587571331989 4018801148355308792406187)
                ·
                  refine ⟨6028201722532963188609281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018801148355308792406187 6028201722532963188609281)
                  ·
                    refine ⟨4521151291899722391456961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028201722532963188609281 4521151291899722391456961)
                    ·
                      refine ⟨3390863468924791793592721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521151291899722391456961 3390863468924791793592721)
                      ·
                        rfl

theorem cell23_6603683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_6603683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603683 prefixEnd_6603683 := by exact prefixLift 6603683
  have htrace : WordTrace (prefixWord ++ tailWord_6603683) baseStart_6603683 baseEnd_6603683 := by
    simpa [prefixWord, tailWord_6603683, baseEnd_6603683] using wordTrace_append hprefix tailTrace_6603683
  have hstable : (prefixWord ++ tailWord_6603683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603683).length < 2 ^ (prefixWord ++ tailWord_6603683).sum := by decide
  have hdescent : baseEnd_6603683 < baseStart_6603683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603699 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 3]
def baseStart_6603699 : Nat := 118140960795 + 6603699 * 2 ^ 59
def prefixEnd_6603699 : Nat := 4983230072969 + 3 ^ 40 * 6603699 * 2
def baseEnd_6603699 : Nat := 3390871684615263730992647

theorem tailTrace_6603699 : CollatzResearch.WordTrace tailWord_6603699 prefixEnd_6603699 3390871684615263730992647 := by
  unfold tailWord_6603699
  simp only [CollatzResearch.WordTrace]
  refine ⟨240856689702933819843814151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160571126468622546562542767 240856689702933819843814151)
  ·
    refine ⟨361285034554400729765721227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240856689702933819843814151 361285034554400729765721227)
    ·
      refine ⟨541927551831601094648581841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361285034554400729765721227 541927551831601094648581841)
      ·
        refine ⟨406445663873700820986436381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541927551831601094648581841 406445663873700820986436381)
        ·
          refine ⟨152417123952637807869913643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406445663873700820986436381 152417123952637807869913643)
          ·
            refine ⟨228625685928956711804870465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152417123952637807869913643 228625685928956711804870465)
            ·
              refine ⟨171469264446717533853652849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228625685928956711804870465 171469264446717533853652849)
              ·
                refine ⟨128601948335038150390239637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171469264446717533853652849 128601948335038150390239637)
                ·
                  refine ⟨6028216328204913299542483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128601948335038150390239637 6028216328204913299542483)
                  ·
                    refine ⟨9042324492307369949313725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6028216328204913299542483 9042324492307369949313725)
                    ·
                      refine ⟨3390871684615263730992647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9042324492307369949313725 3390871684615263730992647)
                      ·
                        rfl

theorem cell23_6603699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_6603699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603699 prefixEnd_6603699 := by exact prefixLift 6603699
  have htrace : WordTrace (prefixWord ++ tailWord_6603699) baseStart_6603699 baseEnd_6603699 := by
    simpa [prefixWord, tailWord_6603699, baseEnd_6603699] using wordTrace_append hprefix tailTrace_6603699
  have hstable : (prefixWord ++ tailWord_6603699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603699).length < 2 ^ (prefixWord ++ tailWord_6603699).sum := by decide
  have hdescent : baseEnd_6603699 < baseStart_6603699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603700 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6603700 : Nat := 118140960795 + 6603700 * 2 ^ 59
def prefixEnd_6603700 : Nat := 4983230072969 + 3 ^ 40 * 6603700 * 2
def baseEnd_6603700 : Nat := 3390872198095918227080143

theorem tailTrace_6603700 : CollatzResearch.WordTrace tailWord_6603700 prefixEnd_6603700 3390872198095918227080143 := by
  unfold tailWord_6603700
  simp only [CollatzResearch.WordTrace]
  refine ⟨120428363087965098507300277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160571150783953464676400369 120428363087965098507300277)
  ·
    refine ⟨11290159039496727985059401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120428363087965098507300277 11290159039496727985059401)
    ·
      refine ⟨8467619279622545988794551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11290159039496727985059401 8467619279622545988794551)
      ·
        refine ⟨12701428919433818983191827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8467619279622545988794551 12701428919433818983191827)
        ·
          refine ⟨19052143379150728474787741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701428919433818983191827 19052143379150728474787741)
          ·
            refine ⟨7144553767181523178045403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19052143379150728474787741 7144553767181523178045403)
            ·
              refine ⟨10716830650772284767068105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144553767181523178045403 10716830650772284767068105)
              ·
                refine ⟨8037622988079213575301079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10716830650772284767068105 8037622988079213575301079)
                ·
                  refine ⟨12056434482118820362951619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8037622988079213575301079 12056434482118820362951619)
                  ·
                    refine ⟨18084651723178230544427429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12056434482118820362951619 18084651723178230544427429)
                    ·
                      refine ⟨3390872198095918227080143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18084651723178230544427429 3390872198095918227080143)
                      ·
                        rfl

theorem cell23_6603700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6603700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603700 prefixEnd_6603700 := by exact prefixLift 6603700
  have htrace : WordTrace (prefixWord ++ tailWord_6603700) baseStart_6603700 baseEnd_6603700 := by
    simpa [prefixWord, tailWord_6603700, baseEnd_6603700] using wordTrace_append hprefix tailTrace_6603700
  have hstable : (prefixWord ++ tailWord_6603700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603700).length < 2 ^ (prefixWord ++ tailWord_6603700).sum := by decide
  have hdescent : baseEnd_6603700 < baseStart_6603700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603734 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6603734 : Nat := 118140960795 + 6603734 * 2 ^ 59
def prefixEnd_6603734 : Nat := 4983230072969 + 3 ^ 40 * 6603734 * 2
def baseEnd_6603734 : Nat := 3390889656438171094054987

theorem tailTrace_6603734 : CollatzResearch.WordTrace tailWord_6603734 prefixEnd_6603734 3390889656438171094054987 := by
  unfold tailWord_6603734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053622891112938801333641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160571977505204680547558837 15053622891112938801333641)
  ·
    refine ⟨11290217168334704101000231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15053622891112938801333641 11290217168334704101000231)
    ·
      refine ⟨16935325752502056151500347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11290217168334704101000231 16935325752502056151500347)
      ·
        refine ⟨25402988628753084227250521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16935325752502056151500347 25402988628753084227250521)
        ·
          refine ⟨19052241471564813170437891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25402988628753084227250521 19052241471564813170437891)
          ·
            refine ⟨28578362207347219755656837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19052241471564813170437891 28578362207347219755656837)
            ·
              refine ⟨5358442913877603704185657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28578362207347219755656837 5358442913877603704185657)
              ·
                refine ⟨4018832185408202778139243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5358442913877603704185657 4018832185408202778139243)
                ·
                  refine ⟨6028248278112304167208865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4018832185408202778139243 6028248278112304167208865)
                  ·
                    refine ⟨4521186208584228125406649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028248278112304167208865 4521186208584228125406649)
                    ·
                      refine ⟨3390889656438171094054987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521186208584228125406649 3390889656438171094054987)
                      ·
                        rfl

theorem cell23_6603734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6603734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603734 prefixEnd_6603734 := by exact prefixLift 6603734
  have htrace : WordTrace (prefixWord ++ tailWord_6603734) baseStart_6603734 baseEnd_6603734 := by
    simpa [prefixWord, tailWord_6603734, baseEnd_6603734] using wordTrace_append hprefix tailTrace_6603734
  have hstable : (prefixWord ++ tailWord_6603734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603734).length < 2 ^ (prefixWord ++ tailWord_6603734).sum := by decide
  have hdescent : baseEnd_6603734 < baseStart_6603734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603756 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_6603756 : Nat := 118140960795 + 6603756 * 2 ^ 59
def prefixEnd_6603756 : Nat := 4983230072969 + 3 ^ 40 * 6603756 * 2
def baseEnd_6603756 : Nat := 3390900953012570007979885

theorem tailTrace_6603756 : CollatzResearch.WordTrace tailWord_6603756 prefixEnd_6603756 3390900953012570007979885 := by
  unfold tailWord_6603756
  simp only [CollatzResearch.WordTrace]
  refine ⟨120429384331863659289319561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160572512442484879052426081 120429384331863659289319561)
  ·
    refine ⟨90322038248897744466989671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120429384331863659289319561 90322038248897744466989671)
    ·
      refine ⟨135483057373346616700484507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90322038248897744466989671 135483057373346616700484507)
      ·
        refine ⟨203224586060019925050726761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135483057373346616700484507 203224586060019925050726761)
        ·
          refine ⟨152418439545014943788045071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203224586060019925050726761 152418439545014943788045071)
          ·
            refine ⟨228627659317522415682067607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152418439545014943788045071 228627659317522415682067607)
            ·
              refine ⟨342941488976283623523101411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228627659317522415682067607 342941488976283623523101411)
              ·
                refine ⟨514412233464425435284652117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342941488976283623523101411 514412233464425435284652117)
                ·
                  refine ⟨6028268360911235569742017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 514412233464425435284652117 6028268360911235569742017)
                  ·
                    refine ⟨4521201270683426677306513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028268360911235569742017 4521201270683426677306513)
                    ·
                      refine ⟨3390900953012570007979885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521201270683426677306513 3390900953012570007979885)
                      ·
                        rfl

theorem cell23_6603756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_6603756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603756 prefixEnd_6603756 := by exact prefixLift 6603756
  have htrace : WordTrace (prefixWord ++ tailWord_6603756) baseStart_6603756 baseEnd_6603756 := by
    simpa [prefixWord, tailWord_6603756, baseEnd_6603756] using wordTrace_append hprefix tailTrace_6603756
  have hstable : (prefixWord ++ tailWord_6603756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603756).length < 2 ^ (prefixWord ++ tailWord_6603756).sum := by decide
  have hdescent : baseEnd_6603756 < baseStart_6603756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603790 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6603790 : Nat := 118140960795 + 6603790 * 2 ^ 59
def prefixEnd_6603790 : Nat := 4983230072969 + 3 ^ 40 * 6603790 * 2
def baseEnd_6603790 : Nat := 3390918411354822874954729

theorem tailTrace_6603790 : CollatzResearch.WordTrace tailWord_6603790 prefixEnd_6603790 3390918411354822874954729 := by
  unfold tailWord_6603790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30107501093200517798172103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160573339163736094923584549 30107501093200517798172103)
  ·
    refine ⟨45161251639800776697258155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30107501093200517798172103 45161251639800776697258155)
    ·
      refine ⟨67741877459701165045887233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45161251639800776697258155 67741877459701165045887233)
      ·
        refine ⟨50806408094775873784415425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67741877459701165045887233 50806408094775873784415425)
        ·
          refine ⟨38104806071081905338311569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50806408094775873784415425 38104806071081905338311569)
          ·
            refine ⟨28578604553311429003733677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38104806071081905338311569 28578604553311429003733677)
            ·
              refine ⟨10716976707491785876400129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28578604553311429003733677 10716976707491785876400129)
              ·
                refine ⟨8037732530618839407300097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10716976707491785876400129 8037732530618839407300097)
                ·
                  refine ⟨6028299397964129555475073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8037732530618839407300097 6028299397964129555475073)
                  ·
                    refine ⟨4521224548473097166606305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028299397964129555475073 4521224548473097166606305)
                    ·
                      refine ⟨3390918411354822874954729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521224548473097166606305 3390918411354822874954729)
                      ·
                        rfl

theorem cell23_6603790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6603790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603790 prefixEnd_6603790 := by exact prefixLift 6603790
  have htrace : WordTrace (prefixWord ++ tailWord_6603790) baseStart_6603790 baseEnd_6603790 := by
    simpa [prefixWord, tailWord_6603790, baseEnd_6603790] using wordTrace_append hprefix tailTrace_6603790
  have hstable : (prefixWord ++ tailWord_6603790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603790).length < 2 ^ (prefixWord ++ tailWord_6603790).sum := by decide
  have hdescent : baseEnd_6603790 < baseStart_6603790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_6603792 : Nat := 118140960795 + 6603792 * 2 ^ 59
def prefixEnd_6603792 : Nat := 4983230072969 + 3 ^ 40 * 6603792 * 2
def baseEnd_6603792 : Nat := 1130306479438710622376573

theorem tailTrace_6603792 : CollatzResearch.WordTrace tailWord_6603792 prefixEnd_6603792 1130306479438710622376573 := by
  unfold tailWord_6603792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120430040845798448363474815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160573387794397931151299753 120430040845798448363474815)
  ·
    refine ⟨180645061268697672545212223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120430040845798448363474815 180645061268697672545212223)
    ·
      refine ⟨270967591903046508817818335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180645061268697672545212223 270967591903046508817818335)
      ·
        refine ⟨406451387854569763226727503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270967591903046508817818335 406451387854569763226727503)
        ·
          refine ⟨609677081781854644840091255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406451387854569763226727503 609677081781854644840091255)
          ·
            refine ⟨914515622672781967260136883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609677081781854644840091255 914515622672781967260136883)
            ·
              refine ⟨1371773434009172950890205325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914515622672781967260136883 1371773434009172950890205325)
              ·
                refine ⟨514415037753439856583826997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371773434009172950890205325 514415037753439856583826997)
                ·
                  refine ⟨48226409789384986554733781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514415037753439856583826997 48226409789384986554733781)
                  ·
                    refine ⟨1130306479438710622376573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48226409789384986554733781 1130306479438710622376573)
                    ·
                      rfl

theorem cell23_6603792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_6603792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603792 prefixEnd_6603792 := by exact prefixLift 6603792
  have htrace : WordTrace (prefixWord ++ tailWord_6603792) baseStart_6603792 baseEnd_6603792 := by
    simpa [prefixWord, tailWord_6603792, baseEnd_6603792] using wordTrace_append hprefix tailTrace_6603792
  have hstable : (prefixWord ++ tailWord_6603792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603792).length < 2 ^ (prefixWord ++ tailWord_6603792).sum := by decide
  have hdescent : baseEnd_6603792 < baseStart_6603792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603809 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_6603809 : Nat := 118140960795 + 6603809 * 2 ^ 59
def prefixEnd_6603809 : Nat := 4983230072969 + 3 ^ 40 * 6603809 * 2
def baseEnd_6603809 : Nat := 1130309389162419433539047

theorem tailTrace_6603809 : CollatzResearch.WordTrace tailWord_6603809 prefixEnd_6603809 1130309389162419433539047 := by
  unfold tailWord_6603809
  simp only [CollatzResearch.WordTrace]
  refine ⟨240860701732535308630318481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160573801155023539086878987 240860701732535308630318481)
  ·
    refine ⟨180645526299401481472738861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240860701732535308630318481 180645526299401481472738861)
    ·
      refine ⟨67742072362275555552277073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180645526299401481472738861 67742072362275555552277073)
      ·
        refine ⟨50806554271706666664207805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67742072362275555552277073 50806554271706666664207805)
        ·
          refine ⟨19052457851889999999077927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50806554271706666664207805 19052457851889999999077927)
          ·
            refine ⟨28578686777834999998616891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19052457851889999999077927 28578686777834999998616891)
            ·
              refine ⟨42868030166752499997925337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28578686777834999998616891 42868030166752499997925337)
              ·
                refine ⟨32151022625064374998444003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42868030166752499997925337 32151022625064374998444003)
                ·
                  refine ⟨48226533937596562497666005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32151022625064374998444003 48226533937596562497666005)
                  ·
                    refine ⟨1130309389162419433539047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48226533937596562497666005 1130309389162419433539047)
                    ·
                      rfl

theorem cell23_6603809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_6603809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603809 prefixEnd_6603809 := by exact prefixLift 6603809
  have htrace : WordTrace (prefixWord ++ tailWord_6603809) baseStart_6603809 baseEnd_6603809 := by
    simpa [prefixWord, tailWord_6603809, baseEnd_6603809] using wordTrace_append hprefix tailTrace_6603809
  have hstable : (prefixWord ++ tailWord_6603809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603809).length < 2 ^ (prefixWord ++ tailWord_6603809).sum := by decide
  have hdescent : baseEnd_6603809 < baseStart_6603809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603830 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_6603830 : Nat := 118140960795 + 6603830 * 2 ^ 59
def prefixEnd_6603830 : Nat := 4983230072969 + 3 ^ 40 * 6603830 * 2
def baseEnd_6603830 : Nat := 376770994509000302050505

theorem tailTrace_6603830 : CollatzResearch.WordTrace tailWord_6603830 prefixEnd_6603830 376770994509000302050505 := by
  unfold tailWord_6603830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053841729091201826052059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160574311776972819477888629 15053841729091201826052059)
  ·
    refine ⟨22580762593636802739078089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15053841729091201826052059 22580762593636802739078089)
    ·
      refine ⟨16935571945227602054308567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22580762593636802739078089 16935571945227602054308567)
      ·
        refine ⟨25403357917841403081462851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16935571945227602054308567 25403357917841403081462851)
        ·
          refine ⟨38105036876762104622194277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25403357917841403081462851 38105036876762104622194277)
          ·
            refine ⟨7144694414392894616661427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38105036876762104622194277 7144694414392894616661427)
            ·
              refine ⟨10717041621589341924992141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144694414392894616661427 10717041621589341924992141)
              ·
                refine ⟨4018890608096003221872053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10717041621589341924992141 4018890608096003221872053)
                ·
                  refine ⟨376770994509000302050505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4018890608096003221872053 376770994509000302050505)
                  ·
                    rfl

theorem cell23_6603830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_6603830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603830 prefixEnd_6603830 := by exact prefixLift 6603830
  have htrace : WordTrace (prefixWord ++ tailWord_6603830) baseStart_6603830 baseEnd_6603830 := by
    simpa [prefixWord, tailWord_6603830, baseEnd_6603830] using wordTrace_append hprefix tailTrace_6603830
  have hstable : (prefixWord ++ tailWord_6603830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603830).length < 2 ^ (prefixWord ++ tailWord_6603830).sum := by decide
  have hdescent : baseEnd_6603830 < baseStart_6603830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603849 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_6603849 : Nat := 118140960795 + 6603849 * 2 ^ 59
def prefixEnd_6603849 : Nat := 4983230072969 + 3 ^ 40 * 6603849 * 2
def baseEnd_6603849 : Nat := 3390948706713438144116957

theorem tailTrace_6603849 : CollatzResearch.WordTrace tailWord_6603849 prefixEnd_6603849 3390948706713438144116957 := by
  unfold tailWord_6603849
  simp only [CollatzResearch.WordTrace]
  refine ⟨240862160652390395461774601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160574773768260263641183067 240862160652390395461774601)
  ·
    refine ⟨180646620489292796596330951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240862160652390395461774601 180646620489292796596330951)
    ·
      refine ⟨270969930733939194894496427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180646620489292796596330951 270969930733939194894496427)
      ·
        refine ⟨406454896100908792341744641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270969930733939194894496427 406454896100908792341744641)
        ·
          refine ⟨304841172075681594256308481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406454896100908792341744641 304841172075681594256308481)
          ·
            refine ⟨228630879056761195692231361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304841172075681594256308481 228630879056761195692231361)
            ·
              refine ⟨171473159292570896769173521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228630879056761195692231361 171473159292570896769173521)
              ·
                refine ⟨128604869469428172576880141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171473159292570896769173521 128604869469428172576880141)
                ·
                  refine ⟨48226826051035564716330053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128604869469428172576880141 48226826051035564716330053)
                  ·
                    refine ⟨9042529884569168384311885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48226826051035564716330053 9042529884569168384311885)
                    ·
                      refine ⟨3390948706713438144116957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9042529884569168384311885 3390948706713438144116957)
                      ·
                        rfl

theorem cell23_6603849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_6603849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603849 prefixEnd_6603849 := by exact prefixLift 6603849
  have htrace : WordTrace (prefixWord ++ tailWord_6603849) baseStart_6603849 baseEnd_6603849 := by
    simpa [prefixWord, tailWord_6603849, baseEnd_6603849] using wordTrace_append hprefix tailTrace_6603849
  have hstable : (prefixWord ++ tailWord_6603849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603849).length < 2 ^ (prefixWord ++ tailWord_6603849).sum := by decide
  have hdescent : baseEnd_6603849 < baseStart_6603849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
