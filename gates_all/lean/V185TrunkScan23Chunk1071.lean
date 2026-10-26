import V185TrunkScan23Chunk1070

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6340016 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2]
def baseStart_6340016 : Nat := 118140960795 + 6340016 * 2 ^ 59
def prefixEnd_6340016 : Nat := 4983230072969 + 3 ^ 40 * 6340016 * 2
def baseEnd_6340016 : Nat := 3255475565195771891942803

theorem tailTrace_6340016 : CollatzResearch.WordTrace tailWord_6340016 prefixEnd_6340016 3255475565195771891942803 := by
  unfold tailWord_6340016
  simp only [CollatzResearch.WordTrace]
  refine ⟨115619690299606147686355951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154159587066141530248474601 115619690299606147686355951)
  ·
    refine ⟨173429535449409221529533927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115619690299606147686355951 173429535449409221529533927)
    ·
      refine ⟨260144303174113832294300891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173429535449409221529533927 260144303174113832294300891)
      ·
        refine ⟨390216454761170748441451337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260144303174113832294300891 390216454761170748441451337)
        ·
          refine ⟨292662341070878061331088503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390216454761170748441451337 292662341070878061331088503)
          ·
            refine ⟨438993511606317091996632755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292662341070878061331088503 438993511606317091996632755)
            ·
              refine ⟨658490267409475637994949133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438993511606317091996632755 658490267409475637994949133)
              ·
                refine ⟨246933850278553364248105925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 658490267409475637994949133 246933850278553364248105925)
                ·
                  refine ⟨46300096927228755796519861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246933850278553364248105925 46300096927228755796519861)
                  ·
                    refine ⟨4340634086927695855923737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46300096927228755796519861 4340634086927695855923737)
                    ·
                      refine ⟨3255475565195771891942803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340634086927695855923737 3255475565195771891942803)
                      ·
                        rfl

theorem cell23_6340016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2].length) (baseStart_6340016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340016 prefixEnd_6340016 := by exact prefixLift 6340016
  have htrace : WordTrace (prefixWord ++ tailWord_6340016) baseStart_6340016 baseEnd_6340016 := by
    simpa [prefixWord, tailWord_6340016, baseEnd_6340016] using wordTrace_append hprefix tailTrace_6340016
  have hstable : (prefixWord ++ tailWord_6340016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340016).length < 2 ^ (prefixWord ++ tailWord_6340016).sum := by decide
  have hdescent : baseEnd_6340016 < baseStart_6340016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340063 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 4, 2]
def baseStart_6340063 : Nat := 118140960795 + 6340063 * 2 ^ 59
def prefixEnd_6340063 : Nat := 4983230072969 + 3 ^ 40 * 6340063 * 2
def baseEnd_6340063 : Nat := 3255499698786533208055087

theorem tailTrace_6340063 : CollatzResearch.WordTrace tailWord_6340063 prefixEnd_6340063 3255499698786533208055087 := by
  unfold tailWord_6340063
  simp only [CollatzResearch.WordTrace]
  refine ⟨231241094830042022399672843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154160729886694681599781895 231241094830042022399672843)
  ·
    refine ⟨346861642245063033599509265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231241094830042022399672843 346861642245063033599509265)
    ·
      refine ⟨260146231683797275199631949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346861642245063033599509265 260146231683797275199631949)
      ·
        refine ⟨97554836881423978199861981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260146231683797275199631949 97554836881423978199861981)
        ·
          refine ⟨36583063830533991824948243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97554836881423978199861981 36583063830533991824948243)
          ·
            refine ⟨54874595745800987737422365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36583063830533991824948243 54874595745800987737422365)
            ·
              refine ⟨20577973404675370401533387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54874595745800987737422365 20577973404675370401533387)
              ·
                refine ⟨30866960107013055602300081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20577973404675370401533387 30866960107013055602300081)
                ·
                  refine ⟨23150220080259791701725061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30866960107013055602300081 23150220080259791701725061)
                  ·
                    refine ⟨4340666265048710944073449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23150220080259791701725061 4340666265048710944073449)
                    ·
                      refine ⟨3255499698786533208055087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340666265048710944073449 3255499698786533208055087)
                      ·
                        rfl

theorem cell23_6340063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_6340063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340063 prefixEnd_6340063 := by exact prefixLift 6340063
  have htrace : WordTrace (prefixWord ++ tailWord_6340063) baseStart_6340063 baseEnd_6340063 := by
    simpa [prefixWord, tailWord_6340063, baseEnd_6340063] using wordTrace_append hprefix tailTrace_6340063
  have hstable : (prefixWord ++ tailWord_6340063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340063).length < 2 ^ (prefixWord ++ tailWord_6340063).sum := by decide
  have hdescent : baseEnd_6340063 < baseStart_6340063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340077 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_6340077 : Nat := 118140960795 + 6340077 * 2 ^ 59
def prefixEnd_6340077 : Nat := 4983230072969 + 3 ^ 40 * 6340077 * 2
def baseEnd_6340077 : Nat := 1085168962505232051093341

theorem tailTrace_6340077 : CollatzResearch.WordTrace tailWord_6340077 prefixEnd_6340077 1085168962505232051093341 := by
  unfold tailWord_6340077
  simp only [CollatzResearch.WordTrace]
  refine ⟨231241605451991302790682485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154161070301327535193788323 231241605451991302790682485)
  ·
    refine ⟨21678900511124184636626483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231241605451991302790682485 21678900511124184636626483)
    ·
      refine ⟨32518350766686276954939725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21678900511124184636626483 32518350766686276954939725)
      ·
        refine ⟨12194381537507353858102397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32518350766686276954939725 12194381537507353858102397)
        ·
          refine ⟨4572893076565257696788399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12194381537507353858102397 4572893076565257696788399)
          ·
            refine ⟨6859339614847886545182599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572893076565257696788399 6859339614847886545182599)
            ·
              refine ⟨10289009422271829817773899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859339614847886545182599 10289009422271829817773899)
              ·
                refine ⟨15433514133407744726660849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289009422271829817773899 15433514133407744726660849)
                ·
                  refine ⟨11575135600055808544995637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15433514133407744726660849 11575135600055808544995637)
                  ·
                    refine ⟨1085168962505232051093341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11575135600055808544995637 1085168962505232051093341)
                    ·
                      rfl

theorem cell23_6340077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_6340077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340077 prefixEnd_6340077 := by exact prefixLift 6340077
  have htrace : WordTrace (prefixWord ++ tailWord_6340077) baseStart_6340077 baseEnd_6340077 := by
    simpa [prefixWord, tailWord_6340077, baseEnd_6340077] using wordTrace_append hprefix tailTrace_6340077
  have hstable : (prefixWord ++ tailWord_6340077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340077).length < 2 ^ (prefixWord ++ tailWord_6340077).sum := by decide
  have hdescent : baseEnd_6340077 < baseStart_6340077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340090 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_6340090 : Nat := 118140960795 + 6340090 * 2 ^ 59
def prefixEnd_6340090 : Nat := 4983230072969 + 3 ^ 40 * 6340090 * 2
def baseEnd_6340090 : Nat := 1085171187588068200805821

theorem tailTrace_6340090 : CollatzResearch.WordTrace tailWord_6340090 prefixEnd_6340090 1085171187588068200805821 := by
  unfold tailWord_6340090
  simp only [CollatzResearch.WordTrace]
  refine ⟨57810519900236051502726431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154161386400629470673937149 57810519900236051502726431)
  ·
    refine ⟨86715779850354077254089647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57810519900236051502726431 86715779850354077254089647)
    ·
      refine ⟨130073669775531115881134471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86715779850354077254089647 130073669775531115881134471)
      ·
        refine ⟨195110504663296673821701707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130073669775531115881134471 195110504663296673821701707)
        ·
          refine ⟨292665756994945010732552561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195110504663296673821701707 292665756994945010732552561)
          ·
            refine ⟨219499317746208758049414421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292665756994945010732552561 219499317746208758049414421)
            ·
              refine ⟨10289030519353535533566301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219499317746208758049414421 10289030519353535533566301)
              ·
                refine ⟨3858386444757575825087363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10289030519353535533566301 3858386444757575825087363)
                ·
                  refine ⟨5787579667136363737631045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858386444757575825087363 5787579667136363737631045)
                  ·
                    refine ⟨1085171187588068200805821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787579667136363737631045 1085171187588068200805821)
                    ·
                      rfl

theorem cell23_6340090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_6340090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340090 prefixEnd_6340090 := by exact prefixLift 6340090
  have htrace : WordTrace (prefixWord ++ tailWord_6340090) baseStart_6340090 baseEnd_6340090 := by
    simpa [prefixWord, tailWord_6340090, baseEnd_6340090] using wordTrace_append hprefix tailTrace_6340090
  have hstable : (prefixWord ++ tailWord_6340090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340090).length < 2 ^ (prefixWord ++ tailWord_6340090).sum := by decide
  have hdescent : baseEnd_6340090 < baseStart_6340090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340103 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 6]
def baseStart_6340103 : Nat := 118140960795 + 6340103 * 2 ^ 59
def prefixEnd_6340103 : Nat := 4983230072969 + 3 ^ 40 * 6340103 * 2
def baseEnd_6340103 : Nat := 361724470890301450172767

theorem tailTrace_6340103 : CollatzResearch.WordTrace tailWord_6340103 prefixEnd_6340103 361724470890301450172767 := by
  unfold tailWord_6340103
  simp only [CollatzResearch.WordTrace]
  refine ⟨231242553749897109231128963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154161702499931406154085975 231242553749897109231128963)
  ·
    refine ⟨346863830624845663846693445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231242553749897109231128963 346863830624845663846693445)
    ·
      refine ⟨65036968242158561971255021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346863830624845663846693445 65036968242158561971255021)
      ·
        refine ⟨24388863090809460739220633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65036968242158561971255021 24388863090809460739220633)
        ·
          refine ⟨18291647318107095554415475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24388863090809460739220633 18291647318107095554415475)
          ·
            refine ⟨27437470977160643331623213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291647318107095554415475 27437470977160643331623213)
            ·
              refine ⟨10289051616435241249358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27437470977160643331623213 10289051616435241249358705)
              ·
                refine ⟨7716788712326430937019029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10289051616435241249358705 7716788712326430937019029)
                ·
                  refine ⟨361724470890301450172767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7716788712326430937019029 361724470890301450172767)
                  ·
                    rfl

theorem cell23_6340103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 6].length) (baseStart_6340103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340103 prefixEnd_6340103 := by exact prefixLift 6340103
  have htrace : WordTrace (prefixWord ++ tailWord_6340103) baseStart_6340103 baseEnd_6340103 := by
    simpa [prefixWord, tailWord_6340103, baseEnd_6340103] using wordTrace_append hprefix tailTrace_6340103
  have hstable : (prefixWord ++ tailWord_6340103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340103).length < 2 ^ (prefixWord ++ tailWord_6340103).sum := by decide
  have hdescent : baseEnd_6340103 < baseStart_6340103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340106 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6340106 : Nat := 118140960795 + 6340106 * 2 ^ 59
def prefixEnd_6340106 : Nat := 4983230072969 + 3 ^ 40 * 6340106 * 2
def baseEnd_6340106 : Nat := 3255521778454676539817389

theorem tailTrace_6340106 : CollatzResearch.WordTrace tailWord_6340106 prefixEnd_6340106 3255521778454676539817389 := by
  unfold tailWord_6340106
  simp only [CollatzResearch.WordTrace]
  refine ⟨57810665792221560185872043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154161775445924160495658781 57810665792221560185872043)
  ·
    refine ⟨86715998688332340278808065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57810665792221560185872043 86715998688332340278808065)
    ·
      refine ⟨65036999016249255209106049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86715998688332340278808065 65036999016249255209106049)
      ·
        refine ⟨48777749262186941406829537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65036999016249255209106049 48777749262186941406829537)
        ·
          refine ⟨36583311946640206055122153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48777749262186941406829537 36583311946640206055122153)
          ·
            refine ⟨27437483959980154541341615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36583311946640206055122153 27437483959980154541341615)
            ·
              refine ⟨41156225939970231812012423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27437483959980154541341615 41156225939970231812012423)
              ·
                refine ⟨61734338909955347718018635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41156225939970231812012423 61734338909955347718018635)
                ·
                  refine ⟨92601508364933021577027953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61734338909955347718018635 92601508364933021577027953)
                  ·
                    refine ⟨69451131273699766182770965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92601508364933021577027953 69451131273699766182770965)
                    ·
                      refine ⟨3255521778454676539817389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69451131273699766182770965 3255521778454676539817389)
                      ·
                        rfl

theorem cell23_6340106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6340106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340106 prefixEnd_6340106 := by exact prefixLift 6340106
  have htrace : WordTrace (prefixWord ++ tailWord_6340106) baseStart_6340106 baseEnd_6340106 := by
    simpa [prefixWord, tailWord_6340106, baseEnd_6340106] using wordTrace_append hprefix tailTrace_6340106
  have hstable : (prefixWord ++ tailWord_6340106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340106).length < 2 ^ (prefixWord ++ tailWord_6340106).sum := by decide
  have hdescent : baseEnd_6340106 < baseStart_6340106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340120 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 6]
def baseStart_6340120 : Nat := 118140960795 + 6340120 * 2 ^ 59
def prefixEnd_6340120 : Nat := 4983230072969 + 3 ^ 40 * 6340120 * 2
def baseEnd_6340120 : Nat := 361725440798204387226925

theorem tailTrace_6340120 : CollatzResearch.WordTrace tailWord_6340120 prefixEnd_6340120 361725440798204387226925 := by
  unfold tailWord_6340120
  simp only [CollatzResearch.WordTrace]
  refine ⟨115621586895417760567248907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154162115860557014089665209 115621586895417760567248907)
  ·
    refine ⟨173432380343126640850873361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115621586895417760567248907 173432380343126640850873361)
    ·
      refine ⟨130074285257344980638155021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173432380343126640850873361 130074285257344980638155021)
      ·
        refine ⟨48777856971504367739308133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130074285257344980638155021 48777856971504367739308133)
        ·
          refine ⟨9145848182157068951120275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48777856971504367739308133 9145848182157068951120275)
          ·
            refine ⟨13718772273235603426680413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9145848182157068951120275 13718772273235603426680413)
            ·
              refine ⟨5144539602463351285005155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13718772273235603426680413 5144539602463351285005155)
              ·
                refine ⟨7716809403695026927507733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144539602463351285005155 7716809403695026927507733)
                ·
                  refine ⟨361725440798204387226925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7716809403695026927507733 361725440798204387226925)
                  ·
                    rfl

theorem cell23_6340120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_6340120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340120 prefixEnd_6340120 := by exact prefixLift 6340120
  have htrace : WordTrace (prefixWord ++ tailWord_6340120) baseStart_6340120 baseEnd_6340120 := by
    simpa [prefixWord, tailWord_6340120, baseEnd_6340120] using wordTrace_append hprefix tailTrace_6340120
  have hstable : (prefixWord ++ tailWord_6340120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340120).length < 2 ^ (prefixWord ++ tailWord_6340120).sum := by decide
  have hdescent : baseEnd_6340120 < baseStart_6340120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340130 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_6340130 : Nat := 118140960795 + 6340130 * 2 ^ 59
def prefixEnd_6340130 : Nat := 4983230072969 + 3 ^ 40 * 6340130 * 2
def baseEnd_6340130 : Nat := 3255534101990384445917279

theorem tailTrace_6340130 : CollatzResearch.WordTrace tailWord_6340130 prefixEnd_6340130 3255534101990384445917279 := by
  unfold tailWord_6340130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57810884630199823210590461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154162359013866195228241229 57810884630199823210590461)
  ·
    refine ⟨21679081736324933703971423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57810884630199823210590461 21679081736324933703971423)
    ·
      refine ⟨32518622604487400555957135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21679081736324933703971423 32518622604487400555957135)
      ·
        refine ⟨48777933906731100833935703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32518622604487400555957135 48777933906731100833935703)
        ·
          refine ⟨73166900860096651250903555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48777933906731100833935703 73166900860096651250903555)
          ·
            refine ⟨109750351290144976876355333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73166900860096651250903555 109750351290144976876355333)
            ·
              refine ⟨20578190866902183164316625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109750351290144976876355333 20578190866902183164316625)
              ·
                refine ⟨15433643150176637373237469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20578190866902183164316625 15433643150176637373237469)
                ·
                  refine ⟨5787616181316239014964051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15433643150176637373237469 5787616181316239014964051)
                  ·
                    refine ⟨8681424271974358522446077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787616181316239014964051 8681424271974358522446077)
                    ·
                      refine ⟨3255534101990384445917279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681424271974358522446077 3255534101990384445917279)
                      ·
                        rfl

theorem cell23_6340130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_6340130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340130 prefixEnd_6340130 := by exact prefixLift 6340130
  have htrace : WordTrace (prefixWord ++ tailWord_6340130) baseStart_6340130 baseEnd_6340130 := by
    simpa [prefixWord, tailWord_6340130, baseEnd_6340130] using wordTrace_append hprefix tailTrace_6340130
  have hstable : (prefixWord ++ tailWord_6340130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340130).length < 2 ^ (prefixWord ++ tailWord_6340130).sum := by decide
  have hdescent : baseEnd_6340130 < baseStart_6340130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340146 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_6340146 : Nat := 118140960795 + 6340146 * 2 ^ 59
def prefixEnd_6340146 : Nat := 4983230072969 + 3 ^ 40 * 6340146 * 2
def baseEnd_6340146 : Nat := 1085180772560285461105735

theorem tailTrace_6340146 : CollatzResearch.WordTrace tailWord_6340146 prefixEnd_6340146 1085180772560285461105735 := by
  unfold tailWord_6340146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57811030522185331893736073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154162748059160885049962861 57811030522185331893736073)
  ·
    refine ⟨43358272891638998920302055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57811030522185331893736073 43358272891638998920302055)
    ·
      refine ⟨65037409337458498380453083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43358272891638998920302055 65037409337458498380453083)
      ·
        refine ⟨97556114006187747570679625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65037409337458498380453083 97556114006187747570679625)
        ·
          refine ⟨73167085504640810678009719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97556114006187747570679625 73167085504640810678009719)
          ·
            refine ⟨109750628256961216017014579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73167085504640810678009719 109750628256961216017014579)
            ·
              refine ⟨164625942385441824025521869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109750628256961216017014579 164625942385441824025521869)
              ·
                refine ⟨61734728394540684009570701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164625942385441824025521869 61734728394540684009570701)
                ·
                  refine ⟨23150523147952756503589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61734728394540684009570701 23150523147952756503589013)
                  ·
                    refine ⟨1085180772560285461105735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23150523147952756503589013 1085180772560285461105735)
                    ·
                      rfl

theorem cell23_6340146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_6340146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340146 prefixEnd_6340146 := by exact prefixLift 6340146
  have htrace : WordTrace (prefixWord ++ tailWord_6340146) baseStart_6340146 baseEnd_6340146 := by
    simpa [prefixWord, tailWord_6340146, baseEnd_6340146] using wordTrace_append hprefix tailTrace_6340146
  have hstable : (prefixWord ++ tailWord_6340146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340146).length < 2 ^ (prefixWord ++ tailWord_6340146).sum := by decide
  have hdescent : baseEnd_6340146 < baseStart_6340146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340147 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 1, 1, 3]
def baseStart_6340147 : Nat := 118140960795 + 6340147 * 2 ^ 59
def prefixEnd_6340147 : Nat := 4983230072969 + 3 ^ 40 * 6340147 * 2
def baseEnd_6340147 : Nat := 3255542831161510879404701

theorem tailTrace_6340147 : CollatzResearch.WordTrace tailWord_6340147 prefixEnd_6340147 3255542831161510879404701 := by
  unfold tailWord_6340147
  simp only [CollatzResearch.WordTrace]
  refine ⟨231244158561737704745730695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154162772374491803163820463 231244158561737704745730695)
  ·
    refine ⟨346866237842606557118596043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231244158561737704745730695 346866237842606557118596043)
    ·
      refine ⟨520299356763909835677894065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346866237842606557118596043 520299356763909835677894065)
      ·
        refine ⟨390224517572932376758420549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520299356763909835677894065 390224517572932376758420549)
        ·
          refine ⟨73167097044924820642203853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390224517572932376758420549 73167097044924820642203853)
          ·
            refine ⟨27437661391846807740826445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73167097044924820642203853 27437661391846807740826445)
            ·
              refine ⟨10289123021942552902809917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27437661391846807740826445 10289123021942552902809917)
              ·
                refine ⟨3858421133228457338553719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10289123021942552902809917 3858421133228457338553719)
                ·
                  refine ⟨5787631699842686007830579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858421133228457338553719 5787631699842686007830579)
                  ·
                    refine ⟨8681447549764029011745869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787631699842686007830579 8681447549764029011745869)
                    ·
                      refine ⟨3255542831161510879404701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681447549764029011745869 3255542831161510879404701)
                      ·
                        rfl

theorem cell23_6340147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 1, 3].length) (baseStart_6340147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340147 prefixEnd_6340147 := by exact prefixLift 6340147
  have htrace : WordTrace (prefixWord ++ tailWord_6340147) baseStart_6340147 baseEnd_6340147 := by
    simpa [prefixWord, tailWord_6340147, baseEnd_6340147] using wordTrace_append hprefix tailTrace_6340147
  have hstable : (prefixWord ++ tailWord_6340147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340147).length < 2 ^ (prefixWord ++ tailWord_6340147).sum := by decide
  have hdescent : baseEnd_6340147 < baseStart_6340147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340157 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6340157 : Nat := 118140960795 + 6340157 * 2 ^ 59
def prefixEnd_6340157 : Nat := 4983230072969 + 3 ^ 40 * 6340157 * 2
def baseEnd_6340157 : Nat := 3255547965968055840279655

theorem tailTrace_6340157 : CollatzResearch.WordTrace tailWord_6340157 prefixEnd_6340157 3255547965968055840279655 := by
  unfold tailWord_6340157
  simp only [CollatzResearch.WordTrace]
  refine ⟨231244523291701476453594725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154163015527800984302396483 231244523291701476453594725)
  ·
    refine ⟨43358348117194026835049011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231244523291701476453594725 43358348117194026835049011)
    ·
      refine ⟨65037522175791040252573517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43358348117194026835049011 65037522175791040252573517)
      ·
        refine ⟨24389070815921640094715069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65037522175791040252573517 24389070815921640094715069)
        ·
          refine ⟨9145901555970615035518151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24389070815921640094715069 9145901555970615035518151)
          ·
            refine ⟨13718852333955922553277227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9145901555970615035518151 13718852333955922553277227)
            ·
              refine ⟨20578278500933883829915841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13718852333955922553277227 20578278500933883829915841)
              ·
                refine ⟨15433708875700412872436881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20578278500933883829915841 15433708875700412872436881)
                ·
                  refine ⟨11575281656775309654327661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15433708875700412872436881 11575281656775309654327661)
                  ·
                    refine ⟨4340730621290741120372873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11575281656775309654327661 4340730621290741120372873)
                    ·
                      refine ⟨3255547965968055840279655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340730621290741120372873 3255547965968055840279655)
                      ·
                        rfl

theorem cell23_6340157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6340157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340157 prefixEnd_6340157 := by exact prefixLift 6340157
  have htrace : WordTrace (prefixWord ++ tailWord_6340157) baseStart_6340157 baseEnd_6340157 := by
    simpa [prefixWord, tailWord_6340157, baseEnd_6340157] using wordTrace_append hprefix tailTrace_6340157
  have hstable : (prefixWord ++ tailWord_6340157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340157).length < 2 ^ (prefixWord ++ tailWord_6340157).sum := by decide
  have hdescent : baseEnd_6340157 < baseStart_6340157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340176 : List Nat := [2, 1, 1, 1, 1, 3, 6, 8]
def baseStart_6340176 : Nat := 118140960795 + 6340176 * 2 ^ 59
def prefixEnd_6340176 : Nat := 4983230072969 + 3 ^ 40 * 6340176 * 2
def baseEnd_6340176 : Nat := 120576211929647824664521

theorem tailTrace_6340176 : CollatzResearch.WordTrace tailWord_6340176 prefixEnd_6340176 120576211929647824664521 := by
  unfold tailWord_6340176
  simp only [CollatzResearch.WordTrace]
  refine ⟨115622608139316321349268191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154163477519088428465690921 115622608139316321349268191)
  ·
    refine ⟨173433912208974482023902287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115622608139316321349268191 173433912208974482023902287)
    ·
      refine ⟨260150868313461723035853431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173433912208974482023902287 260150868313461723035853431)
      ·
        refine ⟨390226302470192584553780147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260150868313461723035853431 390226302470192584553780147)
        ·
          refine ⟨585339453705288876830670221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390226302470192584553780147 585339453705288876830670221)
          ·
            refine ⟨219502295139483328811501333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585339453705288876830670221 219502295139483328811501333)
            ·
              refine ⟨10289170084663281038039125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219502295139483328811501333 10289170084663281038039125)
              ·
                refine ⟨120576211929647824664521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10289170084663281038039125 120576211929647824664521)
                ·
                  rfl

theorem cell23_6340176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_6340176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340176 prefixEnd_6340176 := by exact prefixLift 6340176
  have htrace : WordTrace (prefixWord ++ tailWord_6340176) baseStart_6340176 baseEnd_6340176 := by
    simpa [prefixWord, tailWord_6340176, baseEnd_6340176] using wordTrace_append hprefix tailTrace_6340176
  have hstable : (prefixWord ++ tailWord_6340176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340176).length < 2 ^ (prefixWord ++ tailWord_6340176).sum := by decide
  have hdescent : baseEnd_6340176 < baseStart_6340176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340180 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_6340180 : Nat := 118140960795 + 6340180 * 2 ^ 59
def prefixEnd_6340180 : Nat := 4983230072969 + 3 ^ 40 * 6340180 * 2
def baseEnd_6340180 : Nat := 1085186592007703083430683

theorem tailTrace_6340180 : CollatzResearch.WordTrace tailWord_6340180 prefixEnd_6340180 1085186592007703083430683 := by
  unfold tailWord_6340180
  simp only [CollatzResearch.WordTrace]
  refine ⟨115622681085309075690840997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154163574780412100921121329 115622681085309075690840997)
  ·
    refine ⟨21679252703495451692032687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115622681085309075690840997 21679252703495451692032687)
    ·
      refine ⟨32518879055243177538049031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21679252703495451692032687 32518879055243177538049031)
      ·
        refine ⟨48778318582864766307073547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32518879055243177538049031 48778318582864766307073547)
        ·
          refine ⟨73167477874297149460610321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48778318582864766307073547 73167477874297149460610321)
          ·
            refine ⟨54875608405722862095457741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73167477874297149460610321 54875608405722862095457741)
            ·
              refine ⟨20578353152146073285796653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54875608405722862095457741 20578353152146073285796653)
              ·
                refine ⟨7716882432054777482173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20578353152146073285796653 7716882432054777482173745)
                ·
                  refine ⟨5787661824041083111630309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7716882432054777482173745 5787661824041083111630309)
                  ·
                    refine ⟨1085186592007703083430683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787661824041083111630309 1085186592007703083430683)
                    ·
                      rfl

theorem cell23_6340180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_6340180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340180 prefixEnd_6340180 := by exact prefixLift 6340180
  have htrace : WordTrace (prefixWord ++ tailWord_6340180) baseStart_6340180 baseEnd_6340180 := by
    simpa [prefixWord, tailWord_6340180, baseEnd_6340180] using wordTrace_append hprefix tailTrace_6340180
  have hstable : (prefixWord ++ tailWord_6340180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340180).length < 2 ^ (prefixWord ++ tailWord_6340180).sum := by decide
  have hdescent : baseEnd_6340180 < baseStart_6340180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340200 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6340200 : Nat := 118140960795 + 6340200 * 2 ^ 59
def prefixEnd_6340200 : Nat := 4983230072969 + 3 ^ 40 * 6340200 * 2
def baseEnd_6340200 : Nat := 3255570045636199172041957

theorem tailTrace_6340200 : CollatzResearch.WordTrace tailWord_6340200 prefixEnd_6340200 3255570045636199172041957 := by
  unfold tailWord_6340200
  simp only [CollatzResearch.WordTrace]
  refine ⟨115623045815272847398705027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154164061087030463198273369 115623045815272847398705027)
  ·
    refine ⟨173434568722909271098057541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115623045815272847398705027 173434568722909271098057541)
    ·
      refine ⟨32518981635545488330885789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173434568722909271098057541 32518981635545488330885789)
      ·
        refine ⟨12194618113329558124082171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32518981635545488330885789 12194618113329558124082171)
        ·
          refine ⟨18291927169994337186123257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194618113329558124082171 18291927169994337186123257)
          ·
            refine ⟨13718945377495752889592443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18291927169994337186123257 13718945377495752889592443)
            ·
              refine ⟨20578418066243629334388665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13718945377495752889592443 20578418066243629334388665)
              ·
                refine ⟨15433813549682722000791499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20578418066243629334388665 15433813549682722000791499)
                ·
                  refine ⟨23150720324524083001187249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15433813549682722000791499 23150720324524083001187249)
                  ·
                    refine ⟨17363040243393062250890437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23150720324524083001187249 17363040243393062250890437)
                    ·
                      refine ⟨3255570045636199172041957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17363040243393062250890437 3255570045636199172041957)
                      ·
                        rfl

theorem cell23_6340200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6340200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340200 prefixEnd_6340200 := by exact prefixLift 6340200
  have htrace : WordTrace (prefixWord ++ tailWord_6340200) baseStart_6340200 baseEnd_6340200 := by
    simpa [prefixWord, tailWord_6340200, baseEnd_6340200] using wordTrace_append hprefix tailTrace_6340200
  have hstable : (prefixWord ++ tailWord_6340200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340200).length < 2 ^ (prefixWord ++ tailWord_6340200).sum := by decide
  have hdescent : baseEnd_6340200 < baseStart_6340200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340221 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_6340221 : Nat := 118140960795 + 6340221 * 2 ^ 59
def prefixEnd_6340221 : Nat := 4983230072969 + 3 ^ 40 * 6340221 * 2
def baseEnd_6340221 : Nat := 3255580828729943589879361

theorem tailTrace_6340221 : CollatzResearch.WordTrace tailWord_6340221 prefixEnd_6340221 3255580828729943589879361 := by
  unfold tailWord_6340221
  simp only [CollatzResearch.WordTrace]
  refine ⟨231246857563469615383924517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154164571708979743589283011 231246857563469615383924517)
  ·
    refine ⟨43358785793150552884485847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231246857563469615383924517 43358785793150552884485847)
    ·
      refine ⟨65038178689725829326728771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43358785793150552884485847 65038178689725829326728771)
      ·
        refine ⟨97557268034588743990093157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65038178689725829326728771 97557268034588743990093157)
        ·
          refine ⟨18291987756485389498142467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97557268034588743990093157 18291987756485389498142467)
          ·
            refine ⟨27437981634728084247213701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291987756485389498142467 27437981634728084247213701)
            ·
              refine ⟨5144621556511515796352569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27437981634728084247213701 5144621556511515796352569)
              ·
                refine ⟨3858466167383636847264427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5144621556511515796352569 3858466167383636847264427)
                ·
                  refine ⟨5787699251075455270896641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858466167383636847264427 5787699251075455270896641)
                  ·
                    refine ⟨4340774438306591453172481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787699251075455270896641 4340774438306591453172481)
                    ·
                      refine ⟨3255580828729943589879361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340774438306591453172481 3255580828729943589879361)
                      ·
                        rfl

theorem cell23_6340221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_6340221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340221 prefixEnd_6340221 := by exact prefixLift 6340221
  have htrace : WordTrace (prefixWord ++ tailWord_6340221) baseStart_6340221 baseEnd_6340221 := by
    simpa [prefixWord, tailWord_6340221, baseEnd_6340221] using wordTrace_append hprefix tailTrace_6340221
  have hstable : (prefixWord ++ tailWord_6340221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340221).length < 2 ^ (prefixWord ++ tailWord_6340221).sum := by decide
  have hdescent : baseEnd_6340221 < baseStart_6340221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340258 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6340258 : Nat := 118140960795 + 6340258 * 2 ^ 59
def prefixEnd_6340258 : Nat := 4983230072969 + 3 ^ 40 * 6340258 * 2
def baseEnd_6340258 : Nat := 3255599827514159945116691

theorem tailTrace_6340258 : CollatzResearch.WordTrace tailWord_6340258 prefixEnd_6340258 3255599827514159945116691 := by
  unfold tailWord_6340258
  simp only [CollatzResearch.WordTrace]
  refine ⟨57812051766083892675755357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154165471376223713802014285 57812051766083892675755357)
  ·
    refine ⟨21679519412281459753408259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57812051766083892675755357 21679519412281459753408259)
    ·
      refine ⟨32519279118422189630112389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21679519412281459753408259 32519279118422189630112389)
      ·
        refine ⟨6097364834704160555646073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32519279118422189630112389 6097364834704160555646073)
        ·
          refine ⟨4573023626028120416734555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097364834704160555646073 4573023626028120416734555)
          ·
            refine ⟨6859535439042180625101833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573023626028120416734555 6859535439042180625101833)
            ·
              refine ⟨5144651579281635468826375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6859535439042180625101833 5144651579281635468826375)
              ·
                refine ⟨7716977368922453203239563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144651579281635468826375 7716977368922453203239563)
                ·
                  refine ⟨11575466053383679804859345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7716977368922453203239563 11575466053383679804859345)
                  ·
                    refine ⟨8681599540037759853644509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11575466053383679804859345 8681599540037759853644509)
                    ·
                      refine ⟨3255599827514159945116691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681599540037759853644509 3255599827514159945116691)
                      ·
                        rfl

theorem cell23_6340258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6340258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340258 prefixEnd_6340258 := by exact prefixLift 6340258
  have htrace : WordTrace (prefixWord ++ tailWord_6340258) baseStart_6340258 baseEnd_6340258 := by
    simpa [prefixWord, tailWord_6340258, baseEnd_6340258] using wordTrace_append hprefix tailTrace_6340258
  have hstable : (prefixWord ++ tailWord_6340258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340258).length < 2 ^ (prefixWord ++ tailWord_6340258).sum := by decide
  have hdescent : baseEnd_6340258 < baseStart_6340258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340313 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_6340313 : Nat := 118140960795 + 6340313 * 2 ^ 59
def prefixEnd_6340313 : Nat := 4983230072969 + 3 ^ 40 * 6340313 * 2
def baseEnd_6340313 : Nat := 1085209356316719076642979

theorem tailTrace_6340313 : CollatzResearch.WordTrace tailWord_6340313 prefixEnd_6340313 1085209356316719076642979 := by
  unfold tailWord_6340313
  simp only [CollatzResearch.WordTrace]
  refine ⟨231250213079136315096273593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154166808719424210064182395 231250213079136315096273593)
  ·
    refine ⟨173437659809352236322205195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231250213079136315096273593 173437659809352236322205195)
    ·
      refine ⟨260156489714028354483307793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173437659809352236322205195 260156489714028354483307793)
      ·
        refine ⟨195117367285521265862480845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260156489714028354483307793 195117367285521265862480845)
        ·
          refine ⟨73169012732070474698430317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195117367285521265862480845 73169012732070474698430317)
          ·
            refine ⟨27438379774526428011911369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73169012732070474698430317 27438379774526428011911369)
            ·
              refine ⟨20578784830894821008933527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27438379774526428011911369 20578784830894821008933527)
              ·
                refine ⟨30868177246342231513400291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20578784830894821008933527 30868177246342231513400291)
                ·
                  refine ⟨46302265869513347270100437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30868177246342231513400291 46302265869513347270100437)
                  ·
                    refine ⟨1085209356316719076642979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46302265869513347270100437 1085209356316719076642979)
                    ·
                      rfl

theorem cell23_6340313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_6340313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340313 prefixEnd_6340313 := by exact prefixLift 6340313
  have htrace : WordTrace (prefixWord ++ tailWord_6340313) baseStart_6340313 baseEnd_6340313 := by
    simpa [prefixWord, tailWord_6340313, baseEnd_6340313] using wordTrace_append hprefix tailTrace_6340313
  have hstable : (prefixWord ++ tailWord_6340313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340313).length < 2 ^ (prefixWord ++ tailWord_6340313).sum := by decide
  have hdescent : baseEnd_6340313 < baseStart_6340313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340360 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_6340360 : Nat := 118140960795 + 6340360 * 2 ^ 59
def prefixEnd_6340360 : Nat := 4983230072969 + 3 ^ 40 * 6340360 * 2
def baseEnd_6340360 : Nat := 1085217400846972848680407

theorem tailTrace_6340360 : CollatzResearch.WordTrace tailWord_6340360 prefixEnd_6340360 1085217400846972848680407 := by
  unfold tailWord_6340360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115625963654983021061617267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154167951539977361415489689 115625963654983021061617267)
  ·
    refine ⟨173438945482474531592425901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115625963654983021061617267 173438945482474531592425901)
    ·
      refine ⟨65039604555927949347159713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173438945482474531592425901 65039604555927949347159713)
      ·
        refine ⟨48779703416945962010369785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65039604555927949347159713 48779703416945962010369785)
        ·
          refine ⟨36584777562709471507777339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48779703416945962010369785 36584777562709471507777339)
          ·
            refine ⟨54877166344064207261666009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36584777562709471507777339 54877166344064207261666009)
            ·
              refine ⟨41157874758048155446249507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54877166344064207261666009 41157874758048155446249507)
              ·
                refine ⟨61736812137072233169374261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41157874758048155446249507 61736812137072233169374261)
                ·
                  refine ⟨5787826137850521859628837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61736812137072233169374261 5787826137850521859628837)
                  ·
                    refine ⟨1085217400846972848680407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5787826137850521859628837 1085217400846972848680407)
                    ·
                      rfl

theorem cell23_6340360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_6340360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340360 prefixEnd_6340360 := by exact prefixLift 6340360
  have htrace : WordTrace (prefixWord ++ tailWord_6340360) baseStart_6340360 baseEnd_6340360 := by
    simpa [prefixWord, tailWord_6340360, baseEnd_6340360] using wordTrace_append hprefix tailTrace_6340360
  have hstable : (prefixWord ++ tailWord_6340360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340360).length < 2 ^ (prefixWord ++ tailWord_6340360).sum := by decide
  have hdescent : baseEnd_6340360 < baseStart_6340360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340363 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_6340363 : Nat := 118140960795 + 6340363 * 2 ^ 59
def prefixEnd_6340363 : Nat := 4983230072969 + 3 ^ 40 * 6340363 * 2
def baseEnd_6340363 : Nat := 3255653742982882034303707

theorem tailTrace_6340363 : CollatzResearch.WordTrace tailWord_6340363 prefixEnd_6340363 3255653742982882034303707 := by
  unfold tailWord_6340363
  simp only [CollatzResearch.WordTrace]
  refine ⟨231252036728955173635593743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154168024485970115757062495 231252036728955173635593743)
  ·
    refine ⟨346878055093432760453390615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231252036728955173635593743 346878055093432760453390615)
    ·
      refine ⟨520317082640149140680085923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346878055093432760453390615 520317082640149140680085923)
      ·
        refine ⟨780475623960223711020128885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520317082640149140680085923 780475623960223711020128885)
        ·
          refine ⟨73169589746270972908137083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 780475623960223711020128885 73169589746270972908137083)
          ·
            refine ⟨109754384619406459362205625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73169589746270972908137083 109754384619406459362205625)
            ·
              refine ⟨82315788464554844521654219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109754384619406459362205625 82315788464554844521654219)
              ·
                refine ⟨123473682696832266782481329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82315788464554844521654219 123473682696832266782481329)
                ·
                  refine ⟨92605262022624200086860997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123473682696832266782481329 92605262022624200086860997)
                  ·
                    refine ⟨17363486629242037516286437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92605262022624200086860997 17363486629242037516286437)
                    ·
                      refine ⟨3255653742982882034303707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17363486629242037516286437 3255653742982882034303707)
                      ·
                        rfl

theorem cell23_6340363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_6340363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340363 prefixEnd_6340363 := by exact prefixLift 6340363
  have htrace : WordTrace (prefixWord ++ tailWord_6340363) baseStart_6340363 baseEnd_6340363 := by
    simpa [prefixWord, tailWord_6340363, baseEnd_6340363] using wordTrace_append hprefix tailTrace_6340363
  have hstable : (prefixWord ++ tailWord_6340363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340363).length < 2 ^ (prefixWord ++ tailWord_6340363).sum := by decide
  have hdescent : baseEnd_6340363 < baseStart_6340363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340437 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_6340437 : Nat := 118140960795 + 6340437 * 2 ^ 59
def prefixEnd_6340437 : Nat := 4983230072969 + 3 ^ 40 * 6340437 * 2
def baseEnd_6340437 : Nat := 1085230580183771581592789

theorem tailTrace_6340437 : CollatzResearch.WordTrace tailWord_6340437 prefixEnd_6340437 1085230580183771581592789 := by
  unfold tailWord_6340437
  simp only [CollatzResearch.WordTrace]
  refine ⟨231254735730687084273787565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154169823820458056182525043 231254735730687084273787565)
  ·
    refine ⟨86720525899007656602670337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231254735730687084273787565 86720525899007656602670337)
    ·
      refine ⟨65040394424255742452002753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86720525899007656602670337 65040394424255742452002753)
      ·
        refine ⟨48780295818191806839002065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65040394424255742452002753 48780295818191806839002065)
        ·
          refine ⟨36585221863643855129251549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48780295818191806839002065 36585221863643855129251549)
          ·
            refine ⟨13719458198866445673469331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36585221863643855129251549 13719458198866445673469331)
            ·
              refine ⟨20579187298299668510203997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13719458198866445673469331 20579187298299668510203997)
              ·
                refine ⟨7717195236862375691326499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20579187298299668510203997 7717195236862375691326499)
                ·
                  refine ⟨11575792855293563536989749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717195236862375691326499 11575792855293563536989749)
                  ·
                    refine ⟨1085230580183771581592789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11575792855293563536989749 1085230580183771581592789)
                    ·
                      rfl

theorem cell23_6340437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_6340437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340437 prefixEnd_6340437 := by exact prefixLift 6340437
  have htrace : WordTrace (prefixWord ++ tailWord_6340437) baseStart_6340437 baseEnd_6340437 := by
    simpa [prefixWord, tailWord_6340437, baseEnd_6340437] using wordTrace_append hprefix tailTrace_6340437
  have hstable : (prefixWord ++ tailWord_6340437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340437).length < 2 ^ (prefixWord ++ tailWord_6340437).sum := by decide
  have hdescent : baseEnd_6340437 < baseStart_6340437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340443 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_6340443 : Nat := 118140960795 + 6340443 * 2 ^ 59
def prefixEnd_6340443 : Nat := 4983230072969 + 3 ^ 40 * 6340443 * 2
def baseEnd_6340443 : Nat := 3255694821435241721303339

theorem tailTrace_6340443 : CollatzResearch.WordTrace tailWord_6340443 prefixEnd_6340443 3255694821435241721303339 := by
  unfold tailWord_6340443
  simp only [CollatzResearch.WordTrace]
  refine ⟨231254954568665347298505983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154169969712443564865670655 231254954568665347298505983)
  ·
    refine ⟨346882431852998020947758975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231254954568665347298505983 346882431852998020947758975)
    ·
      refine ⟨520323647779497031421638463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346882431852998020947758975 520323647779497031421638463)
      ·
        refine ⟨780485471669245547132457695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520323647779497031421638463 780485471669245547132457695)
        ·
          refine ⟨1170728207503868320698686543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780485471669245547132457695 1170728207503868320698686543)
          ·
            refine ⟨1756092311255802481048029815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170728207503868320698686543 1756092311255802481048029815)
            ·
              refine ⟨2634138466883703721572044723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756092311255802481048029815 2634138466883703721572044723)
              ·
                refine ⟨3951207700325555582358067085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634138466883703721572044723 3951207700325555582358067085)
                ·
                  refine ⟨1481702887622083343384275157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3951207700325555582358067085 1481702887622083343384275157)
                  ·
                    refine ⟨34727411428642578360568949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1481702887622083343384275157 34727411428642578360568949)
                    ·
                      refine ⟨3255694821435241721303339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34727411428642578360568949 3255694821435241721303339)
                      ·
                        rfl

theorem cell23_6340443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_6340443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340443 prefixEnd_6340443 := by exact prefixLift 6340443
  have htrace : WordTrace (prefixWord ++ tailWord_6340443) baseStart_6340443 baseEnd_6340443 := by
    simpa [prefixWord, tailWord_6340443, baseEnd_6340443] using wordTrace_append hprefix tailTrace_6340443
  have hstable : (prefixWord ++ tailWord_6340443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340443).length < 2 ^ (prefixWord ++ tailWord_6340443).sum := by decide
  have hdescent : baseEnd_6340443 < baseStart_6340443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340460 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_6340460 : Nat := 118140960795 + 6340460 * 2 ^ 59
def prefixEnd_6340460 : Nat := 4983230072969 + 3 ^ 40 * 6340460 * 2
def baseEnd_6340460 : Nat := 3255703550606368154790761

theorem tailTrace_6340460 : CollatzResearch.WordTrace tailWord_6340460 prefixEnd_6340460 3255703550606368154790761 := by
  unfold tailWord_6340460
  simp only [CollatzResearch.WordTrace]
  refine ⟨115627787304801879600937417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154170383073069172801249889 115627787304801879600937417)
  ·
    refine ⟨86720840478601409700703063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115627787304801879600937417 86720840478601409700703063)
    ·
      refine ⟨130081260717902114551054595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86720840478601409700703063 130081260717902114551054595)
      ·
        refine ⟨195121891076853171826581893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130081260717902114551054595 195121891076853171826581893)
        ·
          refine ⟨36585354576909969717484105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195121891076853171826581893 36585354576909969717484105)
          ·
            refine ⟨27439015932682477288113079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36585354576909969717484105 27439015932682477288113079)
            ·
              refine ⟨41158523899023715932169619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27439015932682477288113079 41158523899023715932169619)
              ·
                refine ⟨61737785848535573898254429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41158523899023715932169619 61737785848535573898254429)
                ·
                  refine ⟨23151669693200840211845411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61737785848535573898254429 23151669693200840211845411)
                  ·
                    refine ⟨34727504539801260317768117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23151669693200840211845411 34727504539801260317768117)
                    ·
                      refine ⟨3255703550606368154790761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34727504539801260317768117 3255703550606368154790761)
                      ·
                        rfl

theorem cell23_6340460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_6340460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340460 prefixEnd_6340460 := by exact prefixLift 6340460
  have htrace : WordTrace (prefixWord ++ tailWord_6340460) baseStart_6340460 baseEnd_6340460 := by
    simpa [prefixWord, tailWord_6340460, baseEnd_6340460] using wordTrace_append hprefix tailTrace_6340460
  have hstable : (prefixWord ++ tailWord_6340460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340460).length < 2 ^ (prefixWord ++ tailWord_6340460).sum := by decide
  have hdescent : baseEnd_6340460 < baseStart_6340460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340474 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_6340474 : Nat := 118140960795 + 6340474 * 2 ^ 59
def prefixEnd_6340474 : Nat := 4983230072969 + 3 ^ 40 * 6340474 * 2
def baseEnd_6340474 : Nat := 3255710739335531100015697

theorem tailTrace_6340474 : CollatzResearch.WordTrace tailWord_6340474 prefixEnd_6340474 3255710739335531100015697 := by
  unfold tailWord_6340474
  simp only [CollatzResearch.WordTrace]
  refine ⟨57814021307888259898221119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154170723487702026395256317 57814021307888259898221119)
  ·
    refine ⟨86721031961832389847331679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57814021307888259898221119 86721031961832389847331679)
    ·
      refine ⟨130081547942748584770997519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86721031961832389847331679 130081547942748584770997519)
      ·
        refine ⟨195122321914122877156496279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130081547942748584770997519 195122321914122877156496279)
        ·
          refine ⟨292683482871184315734744419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195122321914122877156496279 292683482871184315734744419)
          ·
            refine ⟨439025224306776473602116629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292683482871184315734744419 439025224306776473602116629)
            ·
              refine ⟨20579307389380147200099217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 439025224306776473602116629 20579307389380147200099217)
              ·
                refine ⟨15434480542035110400074413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20579307389380147200099217 15434480542035110400074413)
                ·
                  refine ⟨5787930203263166400027905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15434480542035110400074413 5787930203263166400027905)
                  ·
                    refine ⟨4340947652447374800020929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787930203263166400027905 4340947652447374800020929)
                    ·
                      refine ⟨3255710739335531100015697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340947652447374800020929 3255710739335531100015697)
                      ·
                        rfl

theorem cell23_6340474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_6340474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340474 prefixEnd_6340474 := by exact prefixLift 6340474
  have htrace : WordTrace (prefixWord ++ tailWord_6340474) baseStart_6340474 baseEnd_6340474 := by
    simpa [prefixWord, tailWord_6340474, baseEnd_6340474] using wordTrace_append hprefix tailTrace_6340474
  have hstable : (prefixWord ++ tailWord_6340474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340474).length < 2 ^ (prefixWord ++ tailWord_6340474).sum := by decide
  have hdescent : baseEnd_6340474 < baseStart_6340474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340502 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6340502 : Nat := 118140960795 + 6340502 * 2 ^ 59
def prefixEnd_6340502 : Nat := 4983230072969 + 3 ^ 40 * 6340502 * 2
def baseEnd_6340502 : Nat := 3255725116793856990465569

theorem tailTrace_6340502 : CollatzResearch.WordTrace tailWord_6340502 prefixEnd_6340502 3255725116793856990465569 := by
  unfold tailWord_6340502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453569154715725023431485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154171404316967733583269173 14453569154715725023431485)
  ·
    refine ⟨5420088433018396883786807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14453569154715725023431485 5420088433018396883786807)
    ·
      refine ⟨8130132649527595325680211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420088433018396883786807 8130132649527595325680211)
      ·
        refine ⟨12195198974291392988520317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130132649527595325680211 12195198974291392988520317)
        ·
          refine ⟨4573199615359272370695119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12195198974291392988520317 4573199615359272370695119)
          ·
            refine ⟨6859799423038908556042679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573199615359272370695119 6859799423038908556042679)
            ·
              refine ⟨10289699134558362834064019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859799423038908556042679 10289699134558362834064019)
              ·
                refine ⟨15434548701837544251096029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289699134558362834064019 15434548701837544251096029)
                ·
                  refine ⟨5787955763189079094161011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15434548701837544251096029 5787955763189079094161011)
                  ·
                    refine ⟨8681933644783618641241517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787955763189079094161011 8681933644783618641241517)
                    ·
                      refine ⟨3255725116793856990465569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8681933644783618641241517 3255725116793856990465569)
                      ·
                        rfl

theorem cell23_6340502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6340502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340502 prefixEnd_6340502 := by exact prefixLift 6340502
  have htrace : WordTrace (prefixWord ++ tailWord_6340502) baseStart_6340502 baseEnd_6340502 := by
    simpa [prefixWord, tailWord_6340502, baseEnd_6340502] using wordTrace_append hprefix tailTrace_6340502
  have hstable : (prefixWord ++ tailWord_6340502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340502).length < 2 ^ (prefixWord ++ tailWord_6340502).sum := by decide
  have hdescent : baseEnd_6340502 < baseStart_6340502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340508 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6340508 : Nat := 118140960795 + 6340508 * 2 ^ 59
def prefixEnd_6340508 : Nat := 4983230072969 + 3 ^ 40 * 6340508 * 2
def baseEnd_6340508 : Nat := 3255728197677783966990541

theorem tailTrace_6340508 : CollatzResearch.WordTrace tailWord_6340508 prefixEnd_6340508 3255728197677783966990541 := by
  unfold tailWord_6340508
  simp only [CollatzResearch.WordTrace]
  refine ⟨115628662656714931699811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154171550208953242266414785 115628662656714931699811089)
  ·
    refine ⟨86721496992536198774858317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115628662656714931699811089 86721496992536198774858317)
    ·
      refine ⟨32520561372201074540571869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86721496992536198774858317 32520561372201074540571869)
      ·
        refine ⟨12195210514575402952714451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32520561372201074540571869 12195210514575402952714451)
        ·
          refine ⟨18292815771863104429071677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12195210514575402952714451 18292815771863104429071677)
          ·
            refine ⟨6859805914448664160901879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18292815771863104429071677 6859805914448664160901879)
            ·
              refine ⟨10289708871672996241352819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859805914448664160901879 10289708871672996241352819)
              ·
                refine ⟨15434563307509494362029229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289708871672996241352819 15434563307509494362029229)
                ·
                  refine ⟨5787961240316060385760961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15434563307509494362029229 5787961240316060385760961)
                  ·
                    refine ⟨4340970930237045289320721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787961240316060385760961 4340970930237045289320721)
                    ·
                      refine ⟨3255728197677783966990541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4340970930237045289320721 3255728197677783966990541)
                      ·
                        rfl

theorem cell23_6340508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6340508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340508 prefixEnd_6340508 := by exact prefixLift 6340508
  have htrace : WordTrace (prefixWord ++ tailWord_6340508) baseStart_6340508 baseEnd_6340508 := by
    simpa [prefixWord, tailWord_6340508, baseEnd_6340508] using wordTrace_append hprefix tailTrace_6340508
  have hstable : (prefixWord ++ tailWord_6340508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340508).length < 2 ^ (prefixWord ++ tailWord_6340508).sum := by decide
  have hdescent : baseEnd_6340508 < baseStart_6340508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340564 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6340564 : Nat := 118140960795 + 6340564 * 2 ^ 59
def prefixEnd_6340564 : Nat := 4983230072969 + 3 ^ 40 * 6340564 * 2
def baseEnd_6340564 : Nat := 3255756952594435747890283

theorem tailTrace_6340564 : CollatzResearch.WordTrace tailWord_6340564 prefixEnd_6340564 3255756952594435747890283 := by
  unfold tailWord_6340564
  simp only [CollatzResearch.WordTrace]
  refine ⟨115629683900613492481830373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154172911867484656642440497 115629683900613492481830373)
  ·
    refine ⟨21680565731365029840343195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115629683900613492481830373 21680565731365029840343195)
    ·
      refine ⟨32520848597047544760514793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21680565731365029840343195 32520848597047544760514793)
      ·
        refine ⟨24390636447785658570386095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32520848597047544760514793 24390636447785658570386095)
        ·
          refine ⟨36585954671678487855579143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24390636447785658570386095 36585954671678487855579143)
          ·
            refine ⟨54878932007517731783368715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36585954671678487855579143 54878932007517731783368715)
            ·
              refine ⟨82318398011276597675053073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54878932007517731783368715 82318398011276597675053073)
              ·
                refine ⟨61738798508457448256289805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82318398011276597675053073 61738798508457448256289805)
                ·
                  refine ⟨23152049440671543096108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61738798508457448256289805 23152049440671543096108677)
                  ·
                    refine ⟨4341009270125914330520377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23152049440671543096108677 4341009270125914330520377)
                    ·
                      refine ⟨3255756952594435747890283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341009270125914330520377 3255756952594435747890283)
                      ·
                        rfl

theorem cell23_6340564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6340564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340564 prefixEnd_6340564 := by exact prefixLift 6340564
  have htrace : WordTrace (prefixWord ++ tailWord_6340564) baseStart_6340564 baseEnd_6340564 := by
    simpa [prefixWord, tailWord_6340564, baseEnd_6340564] using wordTrace_append hprefix tailTrace_6340564
  have hstable : (prefixWord ++ tailWord_6340564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340564).length < 2 ^ (prefixWord ++ tailWord_6340564).sum := by decide
  have hdescent : baseEnd_6340564 < baseStart_6340564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340604 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 5]
def baseStart_6340604 : Nat := 118140960795 + 6340604 * 2 ^ 59
def prefixEnd_6340604 : Nat := 4983230072969 + 3 ^ 40 * 6340604 * 2
def baseEnd_6340604 : Nat := 361753054646735065710011

theorem tailTrace_6340604 : CollatzResearch.WordTrace tailWord_6340604 prefixEnd_6340604 361753054646735065710011 := by
  unfold tailWord_6340604
  simp only [CollatzResearch.WordTrace]
  refine ⟨115630413360541035897558433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154173884480721381196744577 115630413360541035897558433)
  ·
    refine ⟨86722810020405776923168825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115630413360541035897558433 86722810020405776923168825)
    ·
      refine ⟨65042107515304332692376619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86722810020405776923168825 65042107515304332692376619)
      ·
        refine ⟨97563161272956499038564929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65042107515304332692376619 97563161272956499038564929)
        ·
          refine ⟨73172370954717374278923697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97563161272956499038564929 73172370954717374278923697)
          ·
            refine ⟨54879278216038030709192773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73172370954717374278923697 54879278216038030709192773)
            ·
              refine ⟨10289864665507130757973645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54879278216038030709192773 10289864665507130757973645)
              ·
                refine ⟨3858699249565174034240117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10289864665507130757973645 3858699249565174034240117)
                ·
                  refine ⟨361753054646735065710011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3858699249565174034240117 361753054646735065710011)
                  ·
                    rfl

theorem cell23_6340604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_6340604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340604 prefixEnd_6340604 := by exact prefixLift 6340604
  have htrace : WordTrace (prefixWord ++ tailWord_6340604) baseStart_6340604 baseEnd_6340604 := by
    simpa [prefixWord, tailWord_6340604, baseEnd_6340604] using wordTrace_append hprefix tailTrace_6340604
  have hstable : (prefixWord ++ tailWord_6340604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340604).length < 2 ^ (prefixWord ++ tailWord_6340604).sum := by decide
  have hdescent : baseEnd_6340604 < baseStart_6340604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340654 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6340654 : Nat := 118140960795 + 6340654 * 2 ^ 59
def prefixEnd_6340654 : Nat := 4983230072969 + 3 ^ 40 * 6340654 * 2
def baseEnd_6340654 : Nat := 3255803165853340395764869

theorem tailTrace_6340654 : CollatzResearch.WordTrace tailWord_6340654 prefixEnd_6340654 3255803165853340395764869 := by
  unfold tailWord_6340654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907831296362616291804627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154175100247267286889624677 28907831296362616291804627)
  ·
    refine ⟨43361746944543924437706941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28907831296362616291804627 43361746944543924437706941)
    ·
      refine ⟨16260655104203971664140103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43361746944543924437706941 16260655104203971664140103)
      ·
        refine ⟨24390982656305957496210155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260655104203971664140103 24390982656305957496210155)
        ·
          refine ⟨36586473984458936244315233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24390982656305957496210155 36586473984458936244315233)
          ·
            refine ⟨27439855488344202183236425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36586473984458936244315233 27439855488344202183236425)
            ·
              refine ⟨20579891616258151637427319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27439855488344202183236425 20579891616258151637427319)
              ·
                refine ⟨30869837424387227456140979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20579891616258151637427319 30869837424387227456140979)
                ·
                  refine ⟨46304756136580841184211469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30869837424387227456140979 46304756136580841184211469)
                  ·
                    refine ⟨17364283551217815444079301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46304756136580841184211469 17364283551217815444079301)
                    ·
                      refine ⟨3255803165853340395764869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17364283551217815444079301 3255803165853340395764869)
                      ·
                        rfl

theorem cell23_6340654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6340654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340654 prefixEnd_6340654 := by exact prefixLift 6340654
  have htrace : WordTrace (prefixWord ++ tailWord_6340654) baseStart_6340654 baseEnd_6340654 := by
    simpa [prefixWord, tailWord_6340654, baseEnd_6340654] using wordTrace_append hprefix tailTrace_6340654
  have hstable : (prefixWord ++ tailWord_6340654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340654).length < 2 ^ (prefixWord ++ tailWord_6340654).sum := by decide
  have hdescent : baseEnd_6340654 < baseStart_6340654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340677 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 6]
def baseStart_6340677 : Nat := 118140960795 + 6340677 * 2 ^ 59
def prefixEnd_6340677 : Nat := 4983230072969 + 3 ^ 40 * 6340677 * 2
def baseEnd_6340677 : Nat := 361757219545377089530807

theorem tailTrace_6340677 : CollatzResearch.WordTrace tailWord_6340677 prefixEnd_6340677 361757219545377089530807 := by
  unfold tailWord_6340677
  simp only [CollatzResearch.WordTrace]
  refine ⟨231263489249817605262524285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154175659499878403508349523 231263489249817605262524285)
  ·
    refine ⟨86723808468681601973446607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231263489249817605262524285 86723808468681601973446607)
    ·
      refine ⟨130085712703022402960169911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86723808468681601973446607 130085712703022402960169911)
      ·
        refine ⟨195128569054533604440254867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130085712703022402960169911 195128569054533604440254867)
        ·
          refine ⟨292692853581800406660382301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195128569054533604440254867 292692853581800406660382301)
          ·
            refine ⟨109759820093175152497643363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292692853581800406660382301 109759820093175152497643363)
            ·
              refine ⟨164639730139762728746465045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109759820093175152497643363 164639730139762728746465045)
              ·
                refine ⟨7717487350301377909990549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164639730139762728746465045 7717487350301377909990549)
                ·
                  refine ⟨361757219545377089530807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7717487350301377909990549 361757219545377089530807)
                  ·
                    rfl

theorem cell23_6340677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_6340677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340677 prefixEnd_6340677 := by exact prefixLift 6340677
  have htrace : WordTrace (prefixWord ++ tailWord_6340677) baseStart_6340677 baseEnd_6340677 := by
    simpa [prefixWord, tailWord_6340677, baseEnd_6340677] using wordTrace_append hprefix tailTrace_6340677
  have hstable : (prefixWord ++ tailWord_6340677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340677).length < 2 ^ (prefixWord ++ tailWord_6340677).sum := by decide
  have hdescent : baseEnd_6340677 < baseStart_6340677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340775 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6340775 : Nat := 118140960795 + 6340775 * 2 ^ 59
def prefixEnd_6340775 : Nat := 4983230072969 + 3 ^ 40 * 6340775 * 2
def baseEnd_6340775 : Nat := 1085288432337511474117271

theorem tailTrace_6340775 : CollatzResearch.WordTrace tailWord_6340775 prefixEnd_6340775 1085288432337511474117271 := by
  unfold tailWord_6340775
  simp only [CollatzResearch.WordTrace]
  refine ⟨231267063603462567999591779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154178042402308378666394519 231267063603462567999591779)
  ·
    refine ⟨346900595405193851999387669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231267063603462567999591779 346900595405193851999387669)
    ·
      refine ⟨16260965409618461812471297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 346900595405193851999387669 16260965409618461812471297)
      ·
        refine ⟨12195724057213846359353473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16260965409618461812471297 12195724057213846359353473)
        ·
          refine ⟨9146793042910384769515105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12195724057213846359353473 9146793042910384769515105)
          ·
            refine ⟨6860094782182788577136329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146793042910384769515105 6860094782182788577136329)
            ·
              refine ⟨5145071086637091432852247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860094782182788577136329 5145071086637091432852247)
              ·
                refine ⟨7717606629955637149278371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145071086637091432852247 7717606629955637149278371)
                ·
                  refine ⟨11576409944933455723917557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717606629955637149278371 11576409944933455723917557)
                  ·
                    refine ⟨1085288432337511474117271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11576409944933455723917557 1085288432337511474117271)
                    ·
                      rfl

theorem cell23_6340775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6340775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340775 prefixEnd_6340775 := by exact prefixLift 6340775
  have htrace : WordTrace (prefixWord ++ tailWord_6340775) baseStart_6340775 baseEnd_6340775 := by
    simpa [prefixWord, tailWord_6340775, baseEnd_6340775] using wordTrace_append hprefix tailTrace_6340775
  have hstable : (prefixWord ++ tailWord_6340775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340775).length < 2 ^ (prefixWord ++ tailWord_6340775).sum := by decide
  have hdescent : baseEnd_6340775 < baseStart_6340775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340787 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_6340787 : Nat := 118140960795 + 6340787 * 2 ^ 59
def prefixEnd_6340787 : Nat := 4983230072969 + 3 ^ 40 * 6340787 * 2
def baseEnd_6340787 : Nat := 3255871458780388375401757

theorem tailTrace_6340787 : CollatzResearch.WordTrace tailWord_6340787 prefixEnd_6340787 3255871458780388375401757 := by
  unfold tailWord_6340787
  simp only [CollatzResearch.WordTrace]
  refine ⟨231267501279419094049028615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154178334186279396032685743 231267501279419094049028615)
  ·
    refine ⟨346901251919128641073542923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231267501279419094049028615 346901251919128641073542923)
    ·
      refine ⟨520351877878692961610314385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346901251919128641073542923 520351877878692961610314385)
      ·
        refine ⟨390263908409019721207735789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520351877878692961610314385 390263908409019721207735789)
        ·
          refine ⟨146348965653382395452900921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390263908409019721207735789 146348965653382395452900921)
          ·
            refine ⟨109761724240036796589675691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146348965653382395452900921 109761724240036796589675691)
            ·
              refine ⟨164642586360055194884513537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109761724240036796589675691 164642586360055194884513537)
              ·
                refine ⟨123481939770041396163385153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164642586360055194884513537 123481939770041396163385153)
                ·
                  refine ⟨92611454827531047122538865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123481939770041396163385153 92611454827531047122538865)
                  ·
                    refine ⟨69458591120648285341904149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92611454827531047122538865 69458591120648285341904149)
                    ·
                      refine ⟨3255871458780388375401757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69458591120648285341904149 3255871458780388375401757)
                      ·
                        rfl

theorem cell23_6340787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_6340787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340787 prefixEnd_6340787 := by exact prefixLift 6340787
  have htrace : WordTrace (prefixWord ++ tailWord_6340787) baseStart_6340787 baseEnd_6340787 := by
    simpa [prefixWord, tailWord_6340787, baseEnd_6340787] using wordTrace_append hprefix tailTrace_6340787
  have hstable : (prefixWord ++ tailWord_6340787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340787).length < 2 ^ (prefixWord ++ tailWord_6340787).sum := by decide
  have hdescent : baseEnd_6340787 < baseStart_6340787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340794 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_6340794 : Nat := 118140960795 + 6340794 * 2 ^ 59
def prefixEnd_6340794 : Nat := 4983230072969 + 3 ^ 40 * 6340794 * 2
def baseEnd_6340794 : Nat := 3255875053144969848014225

theorem tailTrace_6340794 : CollatzResearch.WordTrace tailWord_6340794 prefixEnd_6340794 3255875053144969848014225 := by
  unfold tailWord_6340794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57816939147598433561133359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154178504393595822829688957 57816939147598433561133359)
  ·
    refine ⟨86725408721397650341700039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57816939147598433561133359 86725408721397650341700039)
    ·
      refine ⟨130088113082096475512550059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86725408721397650341700039 130088113082096475512550059)
      ·
        refine ⟨195132169623144713268825089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130088113082096475512550059 195132169623144713268825089)
        ·
          refine ⟨146349127217358534951618817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195132169623144713268825089 146349127217358534951618817)
          ·
            refine ⟨109761845413018901213714113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146349127217358534951618817 109761845413018901213714113)
            ·
              refine ⟨82321384059764175910285585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109761845413018901213714113 82321384059764175910285585)
              ·
                refine ⟨61741038044823131932714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82321384059764175910285585 61741038044823131932714189)
                ·
                  refine ⟨23152889266808674474767821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61741038044823131932714189 23152889266808674474767821)
                  ·
                    refine ⟨8682333475053252928037933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23152889266808674474767821 8682333475053252928037933)
                    ·
                      refine ⟨3255875053144969848014225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8682333475053252928037933 3255875053144969848014225)
                      ·
                        rfl

theorem cell23_6340794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_6340794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340794 prefixEnd_6340794 := by exact prefixLift 6340794
  have htrace : WordTrace (prefixWord ++ tailWord_6340794) baseStart_6340794 baseEnd_6340794 := by
    simpa [prefixWord, tailWord_6340794, baseEnd_6340794] using wordTrace_append hprefix tailTrace_6340794
  have hstable : (prefixWord ++ tailWord_6340794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340794).length < 2 ^ (prefixWord ++ tailWord_6340794).sum := by decide
  have hdescent : baseEnd_6340794 < baseStart_6340794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340824 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6340824 : Nat := 118140960795 + 6340824 * 2 ^ 59
def prefixEnd_6340824 : Nat := 4983230072969 + 3 ^ 40 * 6340824 * 2
def baseEnd_6340824 : Nat := 3255890457564604730639087

theorem tailTrace_6340824 : CollatzResearch.WordTrace tailWord_6340824 prefixEnd_6340824 3255890457564604730639087 := by
  unfold tailWord_6340824
  simp only [CollatzResearch.WordTrace]
  refine ⟨115634425390142524684062763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154179233853523366245417017 115634425390142524684062763)
  ·
    refine ⟨173451638085213787026094145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115634425390142524684062763 173451638085213787026094145)
    ·
      refine ⟨130088728563910340269570609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173451638085213787026094145 130088728563910340269570609)
      ·
        refine ⟨97566546422932755202177957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130088728563910340269570609 97566546422932755202177957)
        ·
          refine ⟨18293727454299891600408367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97566546422932755202177957 18293727454299891600408367)
          ·
            refine ⟨27440591181449837400612551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18293727454299891600408367 27440591181449837400612551)
            ·
              refine ⟨41160886772174756100918827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27440591181449837400612551 41160886772174756100918827)
              ·
                refine ⟨61741330158262134151378241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41160886772174756100918827 61741330158262134151378241)
                ·
                  refine ⟨46305997618696600613533681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61741330158262134151378241 46305997618696600613533681)
                  ·
                    refine ⟨34729498214022450460150261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46305997618696600613533681 34729498214022450460150261)
                    ·
                      refine ⟨3255890457564604730639087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34729498214022450460150261 3255890457564604730639087)
                      ·
                        rfl

theorem cell23_6340824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6340824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340824 prefixEnd_6340824 := by exact prefixLift 6340824
  have htrace : WordTrace (prefixWord ++ tailWord_6340824) baseStart_6340824 baseEnd_6340824 := by
    simpa [prefixWord, tailWord_6340824, baseEnd_6340824] using wordTrace_append hprefix tailTrace_6340824
  have hstable : (prefixWord ++ tailWord_6340824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340824).length < 2 ^ (prefixWord ++ tailWord_6340824).sum := by decide
  have hdescent : baseEnd_6340824 < baseStart_6340824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340827 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 8]
def baseStart_6340827 : Nat := 118140960795 + 6340827 * 2 ^ 59
def prefixEnd_6340827 : Nat := 4983230072969 + 3 ^ 40 * 6340827 * 2
def baseEnd_6340827 : Nat := 1085297332668856072967191

theorem tailTrace_6340827 : CollatzResearch.WordTrace tailWord_6340827 prefixEnd_6340827 1085297332668856072967191 := by
  unfold tailWord_6340827
  simp only [CollatzResearch.WordTrace]
  refine ⟨231268960199274180880484735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154179306799516120586989823 231268960199274180880484735)
  ·
    refine ⟨346903440298911271320727103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231268960199274180880484735 346903440298911271320727103)
    ·
      refine ⟨520355160448366906981090655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346903440298911271320727103 520355160448366906981090655)
      ·
        refine ⟨780532740672550360471635983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520355160448366906981090655 780532740672550360471635983)
        ·
          refine ⟨1170799111008825540707453975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780532740672550360471635983 1170799111008825540707453975)
          ·
            refine ⟨1756198666513238311061180963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170799111008825540707453975 1756198666513238311061180963)
            ·
              refine ⟨2634297999769857466591771445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756198666513238311061180963 2634297999769857466591771445)
              ·
                refine ⟨246965437478424137492978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2634297999769857466591771445 246965437478424137492978573)
                ·
                  refine ⟨92612039054409051559866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246965437478424137492978573 92612039054409051559866965)
                  ·
                    refine ⟨1085297332668856072967191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92612039054409051559866965 1085297332668856072967191)
                    ·
                      rfl

theorem cell23_6340827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_6340827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340827 prefixEnd_6340827 := by exact prefixLift 6340827
  have htrace : WordTrace (prefixWord ++ tailWord_6340827) baseStart_6340827 baseEnd_6340827 := by
    simpa [prefixWord, tailWord_6340827, baseEnd_6340827] using wordTrace_append hprefix tailTrace_6340827
  have hstable : (prefixWord ++ tailWord_6340827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340827).length < 2 ^ (prefixWord ++ tailWord_6340827).sum := by decide
  have hdescent : baseEnd_6340827 < baseStart_6340827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340829 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6340829 : Nat := 118140960795 + 6340829 * 2 ^ 59
def prefixEnd_6340829 : Nat := 4983230072969 + 3 ^ 40 * 6340829 * 2
def baseEnd_6340829 : Nat := 3255893024967877211076565

theorem tailTrace_6340829 : CollatzResearch.WordTrace tailWord_6340829 prefixEnd_6340829 3255893024967877211076565 := by
  unfold tailWord_6340829
  simp only [CollatzResearch.WordTrace]
  refine ⟨231269033145266935222057541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154179355430177956814705027 231269033145266935222057541)
  ·
    refine ⟨43362943714737550354135789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231269033145266935222057541 43362943714737550354135789)
    ·
      refine ⟨16261103893026581382800921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43362943714737550354135789 16261103893026581382800921)
      ·
        refine ⟨12195827919769936037100691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16261103893026581382800921 12195827919769936037100691)
        ·
          refine ⟨18293741879654904055651037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12195827919769936037100691 18293741879654904055651037)
          ·
            refine ⟨6860153204870589020869139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18293741879654904055651037 6860153204870589020869139)
            ·
              refine ⟨10290229807305883531303709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860153204870589020869139 10290229807305883531303709)
              ·
                refine ⟨3858836177739706324238891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10290229807305883531303709 3858836177739706324238891)
                ·
                  refine ⟨5788254266609559486358337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858836177739706324238891 5788254266609559486358337)
                  ·
                    refine ⟨4341190699957169614768753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788254266609559486358337 4341190699957169614768753)
                    ·
                      refine ⟨3255893024967877211076565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341190699957169614768753 3255893024967877211076565)
                      ·
                        rfl

theorem cell23_6340829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6340829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340829 prefixEnd_6340829 := by exact prefixLift 6340829
  have htrace : WordTrace (prefixWord ++ tailWord_6340829) baseStart_6340829 baseEnd_6340829 := by
    simpa [prefixWord, tailWord_6340829, baseEnd_6340829] using wordTrace_append hprefix tailTrace_6340829
  have hstable : (prefixWord ++ tailWord_6340829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340829).length < 2 ^ (prefixWord ++ tailWord_6340829).sum := by decide
  have hdescent : baseEnd_6340829 < baseStart_6340829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340864 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_6340864 : Nat := 118140960795 + 6340864 * 2 ^ 59
def prefixEnd_6340864 : Nat := 4983230072969 + 3 ^ 40 * 6340864 * 2
def baseEnd_6340864 : Nat := 3255910996790784574138903

theorem tailTrace_6340864 : CollatzResearch.WordTrace tailWord_6340864 prefixEnd_6340864 3255910996790784574138903 := by
  unfold tailWord_6340864
  simp only [CollatzResearch.WordTrace]
  refine ⟨115635154850070068099790823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154180206466760090799721097 115635154850070068099790823)
  ·
    refine ⟨173452732275105102149686235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115635154850070068099790823 173452732275105102149686235)
    ·
      refine ⟨260179098412657653224529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173452732275105102149686235 260179098412657653224529353)
      ·
        refine ⟨195134323809493239918397015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260179098412657653224529353 195134323809493239918397015)
        ·
          refine ⟨292701485714239859877595523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195134323809493239918397015 292701485714239859877595523)
          ·
            refine ⟨439052228571359789816393285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292701485714239859877595523 439052228571359789816393285)
            ·
              refine ⟨82322292857129960590573741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439052228571359789816393285 82322292857129960590573741)
              ·
                refine ⟨30870859821423735221465153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82322292857129960590573741 30870859821423735221465153)
                ·
                  refine ⟨23153144866067801416098865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30870859821423735221465153 23153144866067801416098865)
                  ·
                    refine ⟨17364858649550851062074149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23153144866067801416098865 17364858649550851062074149)
                    ·
                      refine ⟨3255910996790784574138903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17364858649550851062074149 3255910996790784574138903)
                      ·
                        rfl

theorem cell23_6340864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_6340864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340864 prefixEnd_6340864 := by exact prefixLift 6340864
  have htrace : WordTrace (prefixWord ++ tailWord_6340864) baseStart_6340864 baseEnd_6340864 := by
    simpa [prefixWord, tailWord_6340864, baseEnd_6340864] using wordTrace_append hprefix tailTrace_6340864
  have hstable : (prefixWord ++ tailWord_6340864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340864).length < 2 ^ (prefixWord ++ tailWord_6340864).sum := by decide
  have hdescent : baseEnd_6340864 < baseStart_6340864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340874 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_6340874 : Nat := 118140960795 + 6340874 * 2 ^ 59
def prefixEnd_6340874 : Nat := 4983230072969 + 3 ^ 40 * 6340874 * 2
def baseEnd_6340874 : Nat := 361768459066369948334873

theorem tailTrace_6340874 : CollatzResearch.WordTrace tailWord_6340874 prefixEnd_6340874 361768459066369948334873 := by
  unfold tailWord_6340874
  simp only [CollatzResearch.WordTrace]
  refine ⟨57817668607525976976861419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154180449620069271938297117 57817668607525976976861419)
  ·
    refine ⟨86726502911288965465292129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57817668607525976976861419 86726502911288965465292129)
    ·
      refine ⟨65044877183466724098969097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86726502911288965465292129 65044877183466724098969097)
      ·
        refine ⟨48783657887600043074226823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65044877183466724098969097 48783657887600043074226823)
        ·
          refine ⟨73175486831400064611340235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48783657887600043074226823 73175486831400064611340235)
          ·
            refine ⟨109763230247100096917010353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73175486831400064611340235 109763230247100096917010353)
            ·
              refine ⟨82322422685325072687757765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109763230247100096917010353 82322422685325072687757765)
              ·
                refine ⟨15435454253498451128954581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82322422685325072687757765 15435454253498451128954581)
                ·
                  refine ⟨361768459066369948334873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15435454253498451128954581 361768459066369948334873)
                  ·
                    rfl

theorem cell23_6340874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_6340874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340874 prefixEnd_6340874 := by exact prefixLift 6340874
  have htrace : WordTrace (prefixWord ++ tailWord_6340874) baseStart_6340874 baseEnd_6340874 := by
    simpa [prefixWord, tailWord_6340874, baseEnd_6340874] using wordTrace_append hprefix tailTrace_6340874
  have hstable : (prefixWord ++ tailWord_6340874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340874).length < 2 ^ (prefixWord ++ tailWord_6340874).sum := by decide
  have hdescent : baseEnd_6340874 < baseStart_6340874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340908 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 5]
def baseStart_6340908 : Nat := 118140960795 + 6340908 * 2 ^ 59
def prefixEnd_6340908 : Nat := 4983230072969 + 3 ^ 40 * 6340908 * 2
def baseEnd_6340908 : Nat := 361770398882175822443189

theorem tailTrace_6340908 : CollatzResearch.WordTrace tailWord_6340908 prefixEnd_6340908 361770398882175822443189 := by
  unfold tailWord_6340908
  simp only [CollatzResearch.WordTrace]
  refine ⟨115635957255990365857091689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154181276341320487809455585 115635957255990365857091689)
  ·
    refine ⟨86726967941992774392818767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115635957255990365857091689 86726967941992774392818767)
    ·
      refine ⟨130090451912989161589228151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86726967941992774392818767 130090451912989161589228151)
      ·
        refine ⟨195135677869483742383842227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130090451912989161589228151 195135677869483742383842227)
        ·
          refine ⟨292703516804225613575763341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195135677869483742383842227 292703516804225613575763341)
          ·
            refine ⟨109763818801584605090911253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292703516804225613575763341 109763818801584605090911253)
            ·
              refine ⟨5145179006324278363636465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109763818801584605090911253 5145179006324278363636465)
              ·
                refine ⟨3858884254743208772727349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145179006324278363636465 3858884254743208772727349)
                ·
                  refine ⟨361770398882175822443189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3858884254743208772727349 361770398882175822443189)
                  ·
                    rfl

theorem cell23_6340908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_6340908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340908 prefixEnd_6340908 := by exact prefixLift 6340908
  have htrace : WordTrace (prefixWord ++ tailWord_6340908) baseStart_6340908 baseEnd_6340908 := by
    simpa [prefixWord, tailWord_6340908, baseEnd_6340908] using wordTrace_append hprefix tailTrace_6340908
  have hstable : (prefixWord ++ tailWord_6340908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340908).length < 2 ^ (prefixWord ++ tailWord_6340908).sum := by decide
  have hdescent : baseEnd_6340908 < baseStart_6340908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340911 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 5, 2]
def baseStart_6340911 : Nat := 118140960795 + 6340911 * 2 ^ 59
def prefixEnd_6340911 : Nat := 4983230072969 + 3 ^ 40 * 6340911 * 2
def baseEnd_6340911 : Nat := 3255935130381545890251187

theorem tailTrace_6340911 : CollatzResearch.WordTrace tailWord_6340911 prefixEnd_6340911 3255935130381545890251187 := by
  unfold tailWord_6340911
  simp only [CollatzResearch.WordTrace]
  refine ⟨231272023930969863226542587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154181349287313242151028391 231272023930969863226542587)
  ·
    refine ⟨346908035896454794839813881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231272023930969863226542587 346908035896454794839813881)
    ·
      refine ⟨260181026922341096129860411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346908035896454794839813881 260181026922341096129860411)
      ·
        refine ⟨390271540383511644194790617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260181026922341096129860411 390271540383511644194790617)
        ·
          refine ⟨292703655287633733146092963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390271540383511644194790617 292703655287633733146092963)
          ·
            refine ⟨439055482931450599719139445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292703655287633733146092963 439055482931450599719139445)
            ·
              refine ⟨41161451524823493723669323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439055482931450599719139445 41161451524823493723669323)
              ·
                refine ⟨61742177287235240585503985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41161451524823493723669323 61742177287235240585503985)
                ·
                  refine ⟨46306632965426430439127989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61742177287235240585503985 46306632965426430439127989)
                  ·
                    refine ⟨4341246840508727853668249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46306632965426430439127989 4341246840508727853668249)
                    ·
                      refine ⟨3255935130381545890251187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341246840508727853668249 3255935130381545890251187)
                      ·
                        rfl

theorem cell23_6340911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5, 2].length) (baseStart_6340911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340911 prefixEnd_6340911 := by exact prefixLift 6340911
  have htrace : WordTrace (prefixWord ++ tailWord_6340911) baseStart_6340911 baseEnd_6340911 := by
    simpa [prefixWord, tailWord_6340911, baseEnd_6340911] using wordTrace_append hprefix tailTrace_6340911
  have hstable : (prefixWord ++ tailWord_6340911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340911).length < 2 ^ (prefixWord ++ tailWord_6340911).sum := by decide
  have hdescent : baseEnd_6340911 < baseStart_6340911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340951 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 5, 4]
def baseStart_6340951 : Nat := 118140960795 + 6340951 * 2 ^ 59
def prefixEnd_6340951 : Nat := 4983230072969 + 3 ^ 40 * 6340951 * 2
def baseEnd_6340951 : Nat := 1085318556535908577917001

theorem tailTrace_6340951 : CollatzResearch.WordTrace tailWord_6340951 prefixEnd_6340951 1085318556535908577917001 := by
  unfold tailWord_6340951
  simp only [CollatzResearch.WordTrace]
  refine ⟨231273482850824950057998707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154182321900549966705332471 231273482850824950057998707)
  ·
    refine ⟨346910224276237425086998061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231273482850824950057998707 346910224276237425086998061)
    ·
      refine ⟨130091334103589034407624273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346910224276237425086998061 130091334103589034407624273)
      ·
        refine ⟨97568500577691775805718205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130091334103589034407624273 97568500577691775805718205)
        ·
          refine ⟨36588187716634415927144327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97568500577691775805718205 36588187716634415927144327)
          ·
            refine ⟨54882281574951623890716491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36588187716634415927144327 54882281574951623890716491)
            ·
              refine ⟨82323422362427435836074737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54882281574951623890716491 82323422362427435836074737)
              ·
                refine ⟨61742566771820576877056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82323422362427435836074737 61742566771820576877056053)
                ·
                  refine ⟨5788365634858179082224005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61742566771820576877056053 5788365634858179082224005)
                  ·
                    refine ⟨1085318556535908577917001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788365634858179082224005 1085318556535908577917001)
                    ·
                      rfl

theorem cell23_6340951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_6340951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340951 prefixEnd_6340951 := by exact prefixLift 6340951
  have htrace : WordTrace (prefixWord ++ tailWord_6340951) baseStart_6340951 baseEnd_6340951 := by
    simpa [prefixWord, tailWord_6340951, baseEnd_6340951] using wordTrace_append hprefix tailTrace_6340951
  have hstable : (prefixWord ++ tailWord_6340951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340951).length < 2 ^ (prefixWord ++ tailWord_6340951).sum := by decide
  have hdescent : baseEnd_6340951 < baseStart_6340951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6340968 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_6340968 : Nat := 118140960795 + 6340968 * 2 ^ 59
def prefixEnd_6340968 : Nat := 4983230072969 + 3 ^ 40 * 6340968 * 2
def baseEnd_6340968 : Nat := 1085321466259617389079475

theorem tailTrace_6340968 : CollatzResearch.WordTrace tailWord_6340968 prefixEnd_6340968 1085321466259617389079475 := by
  unfold tailWord_6340968
  simp only [CollatzResearch.WordTrace]
  refine ⟨115637051445881680980683779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154182735261175574640911705 115637051445881680980683779)
  ·
    refine ⟨173455577168822521471025669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115637051445881680980683779 173455577168822521471025669)
    ·
      refine ⟨32522920719154222775817313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173455577168822521471025669 32522920719154222775817313)
      ·
        refine ⟨24392190539365667081862985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32522920719154222775817313 24392190539365667081862985)
        ·
          refine ⟨18294142904524250311397239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24392190539365667081862985 18294142904524250311397239)
          ·
            refine ⟨27441214356786375467095859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18294142904524250311397239 27441214356786375467095859)
            ·
              refine ⟨41161821535179563200643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27441214356786375467095859 41161821535179563200643789)
              ·
                refine ⟨15435683075692336200241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41161821535179563200643789 15435683075692336200241421)
                ·
                  refine ⟨5788381153384626075090533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15435683075692336200241421 5788381153384626075090533)
                  ·
                    refine ⟨1085321466259617389079475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788381153384626075090533 1085321466259617389079475)
                    ·
                      rfl

theorem cell23_6340968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_6340968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6340968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6340968 prefixEnd_6340968 := by exact prefixLift 6340968
  have htrace : WordTrace (prefixWord ++ tailWord_6340968) baseStart_6340968 baseEnd_6340968 := by
    simpa [prefixWord, tailWord_6340968, baseEnd_6340968] using wordTrace_append hprefix tailTrace_6340968
  have hstable : (prefixWord ++ tailWord_6340968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6340968).length < 2 ^ (prefixWord ++ tailWord_6340968).sum := by decide
  have hdescent : baseEnd_6340968 < baseStart_6340968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6340968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341032 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 6]
def baseStart_6341032 : Nat := 118140960795 + 6341032 * 2 ^ 59
def prefixEnd_6341032 : Nat := 4983230072969 + 3 ^ 40 * 6341032 * 2
def baseEnd_6341032 : Nat := 361777473504526657426459

theorem tailTrace_6341032 : CollatzResearch.WordTrace tailWord_6341032 prefixEnd_6341032 361777473504526657426459 := by
  unfold tailWord_6341032
  simp only [CollatzResearch.WordTrace]
  refine ⟨115638218581765750445848675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154184291442354333927798233 115638218581765750445848675)
  ·
    refine ⟨173457327872648625668773013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115638218581765750445848675 173457327872648625668773013)
    ·
      refine ⟨8130812244030404328223735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173457327872648625668773013 8130812244030404328223735)
      ·
        refine ⟨12196218366045606492335603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130812244030404328223735 12196218366045606492335603)
        ·
          refine ⟨18294327549068409738503405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196218366045606492335603 18294327549068409738503405)
          ·
            refine ⟨6860372830900653651938777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18294327549068409738503405 6860372830900653651938777)
            ·
              refine ⟨5145279623175490238954083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860372830900653651938777 5145279623175490238954083)
              ·
                refine ⟨7717919434763235358431125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145279623175490238954083 7717919434763235358431125)
                ·
                  refine ⟨361777473504526657426459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7717919434763235358431125 361777473504526657426459)
                  ·
                    rfl

theorem cell23_6341032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_6341032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341032 prefixEnd_6341032 := by exact prefixLift 6341032
  have htrace : WordTrace (prefixWord ++ tailWord_6341032) baseStart_6341032 baseEnd_6341032 := by
    simpa [prefixWord, tailWord_6341032, baseEnd_6341032] using wordTrace_append hprefix tailTrace_6341032
  have hstable : (prefixWord ++ tailWord_6341032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341032).length < 2 ^ (prefixWord ++ tailWord_6341032).sum := by decide
  have hdescent : baseEnd_6341032 < baseStart_6341032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341052 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6341052 : Nat := 118140960795 + 6341052 * 2 ^ 59
def prefixEnd_6341052 : Nat := 4983230072969 + 3 ^ 40 * 6341052 * 2
def baseEnd_6341052 : Nat := 3256007531153829838588039

theorem tailTrace_6341052 : CollatzResearch.WordTrace tailWord_6341052 prefixEnd_6341052 3256007531153829838588039 := by
  unfold tailWord_6341052
  simp only [CollatzResearch.WordTrace]
  refine ⟨115638583311729522153712705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154184777748972696204950273 115638583311729522153712705)
  ·
    refine ⟨86728937483797141615284529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115638583311729522153712705 86728937483797141615284529)
    ·
      refine ⟨65046703112847856211463397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86728937483797141615284529 65046703112847856211463397)
      ·
        refine ⟨12196256833658973039649387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65046703112847856211463397 12196256833658973039649387)
        ·
          refine ⟨18294385250488459559474081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196256833658973039649387 18294385250488459559474081)
          ·
            refine ⟨13720788937866344669605561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18294385250488459559474081 13720788937866344669605561)
            ·
              refine ⟨10290591703399758502204171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13720788937866344669605561 10290591703399758502204171)
              ·
                refine ⟨15435887555099637753306257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10290591703399758502204171 15435887555099637753306257)
                ·
                  refine ⟨11576915666324728314979693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15435887555099637753306257 11576915666324728314979693)
                  ·
                    refine ⟨4341343374871773118117385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11576915666324728314979693 4341343374871773118117385)
                    ·
                      refine ⟨3256007531153829838588039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341343374871773118117385 3256007531153829838588039)
                      ·
                        rfl

theorem cell23_6341052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6341052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341052 prefixEnd_6341052 := by exact prefixLift 6341052
  have htrace : WordTrace (prefixWord ++ tailWord_6341052) baseStart_6341052 baseEnd_6341052 := by
    simpa [prefixWord, tailWord_6341052, baseEnd_6341052] using wordTrace_append hprefix tailTrace_6341052
  have hstable : (prefixWord ++ tailWord_6341052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341052).length < 2 ^ (prefixWord ++ tailWord_6341052).sum := by decide
  have hdescent : baseEnd_6341052 < baseStart_6341052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341076 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6341076 : Nat := 118140960795 + 6341076 * 2 ^ 59
def prefixEnd_6341076 : Nat := 4983230072969 + 3 ^ 40 * 6341076 * 2
def baseEnd_6341076 : Nat := 3256019854689537744687929

theorem tailTrace_6341076 : CollatzResearch.WordTrace tailWord_6341076 prefixEnd_6341076 3256019854689537744687929 := by
  unfold tailWord_6341076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115639020987686048203149541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154185361316914730937532721 115639020987686048203149541)
  ·
    refine ⟨21682316435191134038090539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115639020987686048203149541 21682316435191134038090539)
    ·
      refine ⟨32523474652786701057135809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21682316435191134038090539 32523474652786701057135809)
      ·
        refine ⟨24392605989590025792851857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32523474652786701057135809 24392605989590025792851857)
        ·
          refine ⟨18294454492192519344638893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24392605989590025792851857 18294454492192519344638893)
          ·
            refine ⟨6860420434572194754239585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18294454492192519344638893 6860420434572194754239585)
            ·
              refine ⟨5145315325929146065679689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860420434572194754239585 5145315325929146065679689)
              ·
                refine ⟨3858986494446859549259767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145315325929146065679689 3858986494446859549259767)
                ·
                  refine ⟨5788479741670289323889651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858986494446859549259767 5788479741670289323889651)
                  ·
                    refine ⟨8682719612505433985834477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788479741670289323889651 8682719612505433985834477)
                    ·
                      refine ⟨3256019854689537744687929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8682719612505433985834477 3256019854689537744687929)
                      ·
                        rfl

theorem cell23_6341076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6341076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341076 prefixEnd_6341076 := by exact prefixLift 6341076
  have htrace : WordTrace (prefixWord ++ tailWord_6341076) baseStart_6341076 baseEnd_6341076 := by
    simpa [prefixWord, tailWord_6341076, baseEnd_6341076] using wordTrace_append hprefix tailTrace_6341076
  have hstable : (prefixWord ++ tailWord_6341076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341076).length < 2 ^ (prefixWord ++ tailWord_6341076).sum := by decide
  have hdescent : baseEnd_6341076 < baseStart_6341076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341126 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6341126 : Nat := 118140960795 + 6341126 * 2 ^ 59
def prefixEnd_6341126 : Nat := 4983230072969 + 3 ^ 40 * 6341126 * 2
def baseEnd_6341126 : Nat := 1085348509574087516354233

theorem tailTrace_6341126 : CollatzResearch.WordTrace tailWord_6341126 prefixEnd_6341126 1085348509574087516354233 := by
  unfold tailWord_6341126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227495800787217342050601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154186577083460636630412821 7227495800787217342050601)
  ·
    refine ⟨5420621850590413006537951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7227495800787217342050601 5420621850590413006537951)
    ·
      refine ⟨8130932775885619509806927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420621850590413006537951 8130932775885619509806927)
      ·
        refine ⟨12196399163828429264710391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130932775885619509806927 12196399163828429264710391)
        ·
          refine ⟨18294598745742643897065587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196399163828429264710391 18294598745742643897065587)
          ·
            refine ⟨27441898118613965845598381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18294598745742643897065587 27441898118613965845598381)
            ·
              refine ⟨10290711794480237192099393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27441898118613965845598381 10290711794480237192099393)
              ·
                refine ⟨7718033845860177894074545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10290711794480237192099393 7718033845860177894074545)
                ·
                  refine ⟨5788525384395133420555909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7718033845860177894074545 5788525384395133420555909)
                  ·
                    refine ⟨1085348509574087516354233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788525384395133420555909 1085348509574087516354233)
                    ·
                      rfl

theorem cell23_6341126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6341126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341126 prefixEnd_6341126 := by exact prefixLift 6341126
  have htrace : WordTrace (prefixWord ++ tailWord_6341126) baseStart_6341126 baseEnd_6341126 := by
    simpa [prefixWord, tailWord_6341126, baseEnd_6341126] using wordTrace_append hprefix tailTrace_6341126
  have hstable : (prefixWord ++ tailWord_6341126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341126).length < 2 ^ (prefixWord ++ tailWord_6341126).sum := by decide
  have hdescent : baseEnd_6341126 < baseStart_6341126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341132 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_6341132 : Nat := 118140960795 + 6341132 * 2 ^ 59
def prefixEnd_6341132 : Nat := 4983230072969 + 3 ^ 40 * 6341132 * 2
def baseEnd_6341132 : Nat := 3256048609606189525587671

theorem tailTrace_6341132 : CollatzResearch.WordTrace tailWord_6341132 prefixEnd_6341132 3256048609606189525587671 := by
  unfold tailWord_6341132
  simp only [CollatzResearch.WordTrace]
  refine ⟨115640042231584608985168825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154186722975446145313558433 115640042231584608985168825)
  ·
    refine ⟨86730031673688456738876619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115640042231584608985168825 86730031673688456738876619)
    ·
      refine ⟨130095047510532685108314929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86730031673688456738876619 130095047510532685108314929)
      ·
        refine ⟨97571285632899513831236197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130095047510532685108314929 97571285632899513831236197)
        ·
          refine ⟨18294616056168658843356787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97571285632899513831236197 18294616056168658843356787)
          ·
            refine ⟨27441924084252988265035181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18294616056168658843356787 27441924084252988265035181)
            ·
              refine ⟨10290721531594870599388193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27441924084252988265035181 10290721531594870599388193)
              ·
                refine ⟨7718041148696152949541145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10290721531594870599388193 7718041148696152949541145)
                ·
                  refine ⟨5788530861522114712155859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7718041148696152949541145 5788530861522114712155859)
                  ·
                    refine ⟨8682796292283172068233789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788530861522114712155859 8682796292283172068233789)
                    ·
                      refine ⟨3256048609606189525587671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8682796292283172068233789 3256048609606189525587671)
                      ·
                        rfl

theorem cell23_6341132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_6341132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341132 prefixEnd_6341132 := by exact prefixLift 6341132
  have htrace : WordTrace (prefixWord ++ tailWord_6341132) baseStart_6341132 baseEnd_6341132 := by
    simpa [prefixWord, tailWord_6341132, baseEnd_6341132] using wordTrace_append hprefix tailTrace_6341132
  have hstable : (prefixWord ++ tailWord_6341132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341132).length < 2 ^ (prefixWord ++ tailWord_6341132).sum := by decide
  have hdescent : baseEnd_6341132 < baseStart_6341132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341133 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6341133 : Nat := 118140960795 + 6341133 * 2 ^ 59
def prefixEnd_6341133 : Nat := 4983230072969 + 3 ^ 40 * 6341133 * 2
def baseEnd_6341133 : Nat := 3256049123086844021675167

theorem tailTrace_6341133 : CollatzResearch.WordTrace tailWord_6341133 prefixEnd_6341133 3256049123086844021675167 := by
  unfold tailWord_6341133
  simp only [CollatzResearch.WordTrace]
  refine ⟨231280120936165595141124053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154186747290777063427416035 231280120936165595141124053)
  ·
    refine ⟨5420627834441381136120095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 231280120936165595141124053 5420627834441381136120095)
    ·
      refine ⟨8130941751662071704180143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420627834441381136120095 8130941751662071704180143)
      ·
        refine ⟨12196412627493107556270215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130941751662071704180143 12196412627493107556270215)
        ·
          refine ⟨18294618941239661334405323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196412627493107556270215 18294618941239661334405323)
          ·
            refine ⟨27441928411859492001607985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18294618941239661334405323 27441928411859492001607985)
            ·
              refine ⟨20581446308894619001205989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27441928411859492001607985 20581446308894619001205989)
              ·
                refine ⟨3859021182917741062726123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20581446308894619001205989 3859021182917741062726123)
                ·
                  refine ⟨5788531774376611594089185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859021182917741062726123 5788531774376611594089185)
                  ·
                    refine ⟨4341398830782458695566889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788531774376611594089185 4341398830782458695566889)
                    ·
                      refine ⟨3256049123086844021675167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341398830782458695566889 3256049123086844021675167)
                      ·
                        rfl

theorem cell23_6341133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6341133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341133 prefixEnd_6341133 := by exact prefixLift 6341133
  have htrace : WordTrace (prefixWord ++ tailWord_6341133) baseStart_6341133 baseEnd_6341133 := by
    simpa [prefixWord, tailWord_6341133, baseEnd_6341133] using wordTrace_append hprefix tailTrace_6341133
  have hstable : (prefixWord ++ tailWord_6341133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341133).length < 2 ^ (prefixWord ++ tailWord_6341133).sum := by decide
  have hdescent : baseEnd_6341133 < baseStart_6341133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341148 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6341148 : Nat := 118140960795 + 6341148 * 2 ^ 59
def prefixEnd_6341148 : Nat := 4983230072969 + 3 ^ 40 * 6341148 * 2
def baseEnd_6341148 : Nat := 1085352275098887154329199

theorem tailTrace_6341148 : CollatzResearch.WordTrace tailWord_6341148 prefixEnd_6341148 1085352275098887154329199 := by
  unfold tailWord_6341148
  simp only [CollatzResearch.WordTrace]
  refine ⟨115640334015555626351460049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154187112020740835135280065 115640334015555626351460049)
  ·
    refine ⟨86730250511666719763595037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115640334015555626351460049 86730250511666719763595037)
    ·
      refine ⟨32523843941875019911348139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86730250511666719763595037 32523843941875019911348139)
      ·
        refine ⟨48785765912812529867022209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32523843941875019911348139 48785765912812529867022209)
        ·
          refine ⟨36589324434609397400266657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48785765912812529867022209 36589324434609397400266657)
          ·
            refine ⟨27441993325957048050199993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36589324434609397400266657 27441993325957048050199993)
            ·
              refine ⟨20581494994467786037649995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27441993325957048050199993 20581494994467786037649995)
              ·
                refine ⟨30872242491701679056474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20581494994467786037649995 30872242491701679056474993)
                ·
                  refine ⟨23154181868776259292356245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30872242491701679056474993 23154181868776259292356245)
                  ·
                    refine ⟨1085352275098887154329199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23154181868776259292356245 1085352275098887154329199)
                    ·
                      rfl

theorem cell23_6341148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6341148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341148 prefixEnd_6341148 := by exact prefixLift 6341148
  have htrace : WordTrace (prefixWord ++ tailWord_6341148) baseStart_6341148 baseEnd_6341148 := by
    simpa [prefixWord, tailWord_6341148, baseEnd_6341148] using wordTrace_append hprefix tailTrace_6341148
  have hstable : (prefixWord ++ tailWord_6341148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341148).length < 2 ^ (prefixWord ++ tailWord_6341148).sum := by decide
  have hdescent : baseEnd_6341148 < baseStart_6341148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341149 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_6341149 : Nat := 118140960795 + 6341149 * 2 ^ 59
def prefixEnd_6341149 : Nat := 4983230072969 + 3 ^ 40 * 6341149 * 2
def baseEnd_6341149 : Nat := 3256057338777315959075093

theorem tailTrace_6341149 : CollatzResearch.WordTrace tailWord_6341149 prefixEnd_6341149 3256057338777315959075093 := by
  unfold tailWord_6341149
  simp only [CollatzResearch.WordTrace]
  refine ⟨231280704504107629873706501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154187136336071753249137667 231280704504107629873706501)
  ·
    refine ⟨43365132094520180601319969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231280704504107629873706501 43365132094520180601319969)
    ·
      refine ⟨32523849070890135450989977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43365132094520180601319969 32523849070890135450989977)
      ·
        refine ⟨24392886803167601588242483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32523849070890135450989977 24392886803167601588242483)
        ·
          refine ⟨36589330204751402382363725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24392886803167601588242483 36589330204751402382363725)
          ·
            refine ⟨13720998826781775893386397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36589330204751402382363725 13720998826781775893386397)
            ·
              refine ⟨5145374560043165960019899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13720998826781775893386397 5145374560043165960019899)
              ·
                refine ⟨7718061840064748940029849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145374560043165960019899 7718061840064748940029849)
                ·
                  refine ⟨5788546380048561705022387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7718061840064748940029849 5788546380048561705022387)
                  ·
                    refine ⟨8682819570072842557533581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788546380048561705022387 8682819570072842557533581)
                    ·
                      refine ⟨3256057338777315959075093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8682819570072842557533581 3256057338777315959075093)
                      ·
                        rfl

theorem cell23_6341149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_6341149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341149 prefixEnd_6341149 := by exact prefixLift 6341149
  have htrace : WordTrace (prefixWord ++ tailWord_6341149) baseStart_6341149 baseEnd_6341149 := by
    simpa [prefixWord, tailWord_6341149, baseEnd_6341149] using wordTrace_append hprefix tailTrace_6341149
  have hstable : (prefixWord ++ tailWord_6341149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341149).length < 2 ^ (prefixWord ++ tailWord_6341149).sum := by decide
  have hdescent : baseEnd_6341149 < baseStart_6341149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341228 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_6341228 : Nat := 118140960795 + 6341228 * 2 ^ 59
def prefixEnd_6341228 : Nat := 4983230072969 + 3 ^ 40 * 6341228 * 2
def baseEnd_6341228 : Nat := 3256097903749021149987229

theorem tailTrace_6341228 : CollatzResearch.WordTrace tailWord_6341228 prefixEnd_6341228 3256097903749021149987229 := by
  unfold tailWord_6341228
  simp only [CollatzResearch.WordTrace]
  refine ⟨115641792935410713182916169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154189057247214284243888225 115641792935410713182916169)
  ·
    refine ⟨86731344701558034887187127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115641792935410713182916169 86731344701558034887187127)
    ·
      refine ⟨130097017052337052330780691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86731344701558034887187127 130097017052337052330780691)
      ·
        refine ⟨195145525578505578496171037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130097017052337052330780691 195145525578505578496171037)
        ·
          refine ⟨73179572091939591936064139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195145525578505578496171037 73179572091939591936064139)
          ·
            refine ⟨109769358137909387904096209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73179572091939591936064139 109769358137909387904096209)
            ·
              refine ⟨82327018603432040928072157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109769358137909387904096209 82327018603432040928072157)
              ·
                refine ⟨30872631976287015348027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82327018603432040928072157 30872631976287015348027059)
                ·
                  refine ⟨46308947964430523022040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30872631976287015348027059 46308947964430523022040589)
                  ·
                    refine ⟨17365855486661446133265221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46308947964430523022040589 17365855486661446133265221)
                    ·
                      refine ⟨3256097903749021149987229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17365855486661446133265221 3256097903749021149987229)
                      ·
                        rfl

theorem cell23_6341228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_6341228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341228 prefixEnd_6341228 := by exact prefixLift 6341228
  have htrace : WordTrace (prefixWord ++ tailWord_6341228) baseStart_6341228 baseEnd_6341228 := by
    simpa [prefixWord, tailWord_6341228, baseEnd_6341228] using wordTrace_append hprefix tailTrace_6341228
  have hstable : (prefixWord ++ tailWord_6341228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341228).length < 2 ^ (prefixWord ++ tailWord_6341228).sum := by decide
  have hdescent : baseEnd_6341228 < baseStart_6341228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341255 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 3, 4]
def baseStart_6341255 : Nat := 118140960795 + 6341255 * 2 ^ 59
def prefixEnd_6341255 : Nat := 4983230072969 + 3 ^ 40 * 6341255 * 2
def baseEnd_6341255 : Nat := 1085370589242230848116535

theorem tailTrace_6341255 : CollatzResearch.WordTrace tailWord_6341255 prefixEnd_6341255 1085370589242230848116535 := by
  unfold tailWord_6341255
  simp only [CollatzResearch.WordTrace]
  refine ⟨231284570641723609977065219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154189713761149073318043479 231284570641723609977065219)
  ·
    refine ⟨346926855962585414965597829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231284570641723609977065219 346926855962585414965597829)
    ·
      refine ⟨65048785492984765306049593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346926855962585414965597829 65048785492984765306049593)
      ·
        refine ⟨48786589119738573979537195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65048785492984765306049593 48786589119738573979537195)
        ·
          refine ⟨73179883679607860969305793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48786589119738573979537195 73179883679607860969305793)
          ·
            refine ⟨54884912759705895726979345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73179883679607860969305793 54884912759705895726979345)
            ·
              refine ⟨41163684569779421795234509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54884912759705895726979345 41163684569779421795234509)
              ·
                refine ⟨15436381713667283173212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41163684569779421795234509 15436381713667283173212941)
                ·
                  refine ⟨5788643142625231189954853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15436381713667283173212941 5788643142625231189954853)
                  ·
                    refine ⟨1085370589242230848116535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788643142625231189954853 1085370589242230848116535)
                    ·
                      rfl

theorem cell23_6341255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_6341255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341255 prefixEnd_6341255 := by exact prefixLift 6341255
  have htrace : WordTrace (prefixWord ++ tailWord_6341255) baseStart_6341255 baseEnd_6341255 := by
    simpa [prefixWord, tailWord_6341255, baseEnd_6341255] using wordTrace_append hprefix tailTrace_6341255
  have hstable : (prefixWord ++ tailWord_6341255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341255).length < 2 ^ (prefixWord ++ tailWord_6341255).sum := by decide
  have hdescent : baseEnd_6341255 < baseStart_6341255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341262 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6341262 : Nat := 118140960795 + 6341262 * 2 ^ 59
def prefixEnd_6341262 : Nat := 4983230072969 + 3 ^ 40 * 6341262 * 2
def baseEnd_6341262 : Nat := 3256115362091274016962073

theorem tailTrace_6341262 : CollatzResearch.WordTrace tailWord_6341262 prefixEnd_6341262 3256115362091274016962073 := by
  unfold tailWord_6341262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28910603244087281271571255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154189883968465500115046693 28910603244087281271571255)
  ·
    refine ⟨43365904866130921907356883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28910603244087281271571255 43365904866130921907356883)
    ·
      refine ⟨65048857299196382861035325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43365904866130921907356883 65048857299196382861035325)
      ·
        refine ⟨24393321487198643572888247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65048857299196382861035325 24393321487198643572888247)
        ·
          refine ⟨36589982230797965359332371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24393321487198643572888247 36589982230797965359332371)
          ·
            refine ⟨54884973346196948038998557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36589982230797965359332371 54884973346196948038998557)
            ·
              refine ⟨20581865004823855514624459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54884973346196948038998557 20581865004823855514624459)
              ·
                refine ⟨30872797507235783271936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20581865004823855514624459 30872797507235783271936689)
                ·
                  refine ⟨23154598130426837453952517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30872797507235783271936689 23154598130426837453952517)
                  ·
                    refine ⟨4341487149455032022616097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23154598130426837453952517 4341487149455032022616097)
                    ·
                      refine ⟨3256115362091274016962073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341487149455032022616097 3256115362091274016962073)
                      ·
                        rfl

theorem cell23_6341262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6341262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341262 prefixEnd_6341262 := by exact prefixLift 6341262
  have htrace : WordTrace (prefixWord ++ tailWord_6341262) baseStart_6341262 baseEnd_6341262 := by
    simpa [prefixWord, tailWord_6341262, baseEnd_6341262] using wordTrace_append hprefix tailTrace_6341262
  have hstable : (prefixWord ++ tailWord_6341262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341262).length < 2 ^ (prefixWord ++ tailWord_6341262).sum := by decide
  have hdescent : baseEnd_6341262 < baseStart_6341262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341312 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_6341312 : Nat := 118140960795 + 6341312 * 2 ^ 59
def prefixEnd_6341312 : Nat := 4983230072969 + 3 ^ 40 * 6341312 * 2
def baseEnd_6341312 : Nat := 3256141036123998821336843

theorem tailTrace_6341312 : CollatzResearch.WordTrace tailWord_6341312 prefixEnd_6341312 3256141036123998821336843 := by
  unfold tailWord_6341312
  simp only [CollatzResearch.WordTrace]
  refine ⟨115643324801258554355945095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154191099735011405807926793 115643324801258554355945095)
  ·
    refine ⟨173464987201887831533917643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115643324801258554355945095 173464987201887831533917643)
    ·
      refine ⟨260197480802831747300876465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173464987201887831533917643 260197480802831747300876465)
      ·
        refine ⟨195148110602123810475657349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260197480802831747300876465 195148110602123810475657349)
        ·
          refine ⟨36590270737898214464185753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195148110602123810475657349 36590270737898214464185753)
          ·
            refine ⟨27442703053423660848139315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36590270737898214464185753 27442703053423660848139315)
            ·
              refine ⟨41164054580135491272208973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27442703053423660848139315 41164054580135491272208973)
              ·
                refine ⟨15436520467550809227078365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41164054580135491272208973 15436520467550809227078365)
                ·
                  refine ⟨5788695175331553460154387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15436520467550809227078365 5788695175331553460154387)
                  ·
                    refine ⟨8683042762997330190231581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788695175331553460154387 8683042762997330190231581)
                    ·
                      refine ⟨3256141036123998821336843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683042762997330190231581 3256141036123998821336843)
                      ·
                        rfl

theorem cell23_6341312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_6341312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341312 prefixEnd_6341312 := by exact prefixLift 6341312
  have htrace : WordTrace (prefixWord ++ tailWord_6341312) baseStart_6341312 baseEnd_6341312 := by
    simpa [prefixWord, tailWord_6341312, baseEnd_6341312] using wordTrace_append hprefix tailTrace_6341312
  have hstable : (prefixWord ++ tailWord_6341312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341312).length < 2 ^ (prefixWord ++ tailWord_6341312).sum := by decide
  have hdescent : baseEnd_6341312 < baseStart_6341312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341322 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_6341322 : Nat := 118140960795 + 6341322 * 2 ^ 59
def prefixEnd_6341322 : Nat := 4983230072969 + 3 ^ 40 * 6341322 * 2
def baseEnd_6341322 : Nat := 3256146170930543782211797

theorem tailTrace_6341322 : CollatzResearch.WordTrace tailWord_6341322 prefixEnd_6341322 3256146170930543782211797 := by
  unfold tailWord_6341322
  simp only [CollatzResearch.WordTrace]
  refine ⟨57821753583120220104938555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154191342888320586946502813 57821753583120220104938555)
  ·
    refine ⟨86732630374680330157407833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57821753583120220104938555 86732630374680330157407833)
    ·
      refine ⟨65049472781010247618055875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86732630374680330157407833 65049472781010247618055875)
      ·
        refine ⟨97574209171515371427083813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65049472781010247618055875 97574209171515371427083813)
        ·
          refine ⟨18295164219659132142578215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97574209171515371427083813 18295164219659132142578215)
          ·
            refine ⟨27442746329488698213867323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295164219659132142578215 27442746329488698213867323)
            ·
              refine ⟨41164119494233047320800985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27442746329488698213867323 41164119494233047320800985)
              ·
                refine ⟨30873089620674785490600739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41164119494233047320800985 30873089620674785490600739)
                ·
                  refine ⟨46309634431012178235901109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30873089620674785490600739 46309634431012178235901109)
                  ·
                    refine ⟨4341528227907391709615729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46309634431012178235901109 4341528227907391709615729)
                    ·
                      refine ⟨3256146170930543782211797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341528227907391709615729 3256146170930543782211797)
                      ·
                        rfl

theorem cell23_6341322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_6341322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341322 prefixEnd_6341322 := by exact prefixLift 6341322
  have htrace : WordTrace (prefixWord ++ tailWord_6341322) baseStart_6341322 baseEnd_6341322 := by
    simpa [prefixWord, tailWord_6341322, baseEnd_6341322] using wordTrace_append hprefix tailTrace_6341322
  have hstable : (prefixWord ++ tailWord_6341322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341322).length < 2 ^ (prefixWord ++ tailWord_6341322).sum := by decide
  have hdescent : baseEnd_6341322 < baseStart_6341322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341355 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3]
def baseStart_6341355 : Nat := 118140960795 + 6341355 * 2 ^ 59
def prefixEnd_6341355 : Nat := 4983230072969 + 3 ^ 40 * 6341355 * 2
def baseEnd_6341355 : Nat := 3256163115792142153099145

theorem tailTrace_6341355 : CollatzResearch.WordTrace tailWord_6341355 prefixEnd_6341355 3256163115792142153099145 := by
  unfold tailWord_6341355
  simp only [CollatzResearch.WordTrace]
  refine ⟨231288217941361327055705519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154192145294240884703803679 231288217941361327055705519)
  ·
    refine ⟨346932326912041990583558279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231288217941361327055705519 346932326912041990583558279)
    ·
      refine ⟨520398490368062985875337419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346932326912041990583558279 520398490368062985875337419)
      ·
        refine ⟨780597735552094478813006129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520398490368062985875337419 780597735552094478813006129)
        ·
          refine ⟨585448301664070859109754597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780597735552094478813006129 585448301664070859109754597)
          ·
            refine ⟨109771556562013286083078987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585448301664070859109754597 109771556562013286083078987)
            ·
              refine ⟨164657334843019929124618481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109771556562013286083078987 164657334843019929124618481)
              ·
                refine ⟨123493001132264946843463861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164657334843019929124618481 123493001132264946843463861)
                ·
                  refine ⟨11577468856149838766574737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123493001132264946843463861 11577468856149838766574737)
                  ·
                    refine ⟨8683101642112379074931053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11577468856149838766574737 8683101642112379074931053)
                    ·
                      refine ⟨3256163115792142153099145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683101642112379074931053 3256163115792142153099145)
                      ·
                        rfl

theorem cell23_6341355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].length) (baseStart_6341355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341355 prefixEnd_6341355 := by exact prefixLift 6341355
  have htrace : WordTrace (prefixWord ++ tailWord_6341355) baseStart_6341355 baseEnd_6341355 := by
    simpa [prefixWord, tailWord_6341355, baseEnd_6341355] using wordTrace_append hprefix tailTrace_6341355
  have hstable : (prefixWord ++ tailWord_6341355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341355).length < 2 ^ (prefixWord ++ tailWord_6341355).sum := by decide
  have hdescent : baseEnd_6341355 < baseStart_6341355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341362 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_6341362 : Nat := 118140960795 + 6341362 * 2 ^ 59
def prefixEnd_6341362 : Nat := 4983230072969 + 3 ^ 40 * 6341362 * 2
def baseEnd_6341362 : Nat := 1085388903385574541903871

theorem tailTrace_6341362 : CollatzResearch.WordTrace tailWord_6341362 prefixEnd_6341362 1085388903385574541903871 := by
  unfold tailWord_6341362
  simp only [CollatzResearch.WordTrace]
  refine ⟨57822118313083991812802585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154192315501557311500806893 57822118313083991812802585)
  ·
    refine ⟨43366588734812993859601939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57822118313083991812802585 43366588734812993859601939)
    ·
      refine ⟨65049883102219490789402909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43366588734812993859601939 65049883102219490789402909)
      ·
        refine ⟨24393706163332309046026091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65049883102219490789402909 24393706163332309046026091)
        ·
          refine ⟨36590559244998463569039137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24393706163332309046026091 36590559244998463569039137)
          ·
            refine ⟨27442919433748847676779353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36590559244998463569039137 27442919433748847676779353)
            ·
              refine ⟨20582189575311635757584515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27442919433748847676779353 20582189575311635757584515)
              ·
                refine ⟨30873284362967453636376773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20582189575311635757584515 30873284362967453636376773)
                ·
                  refine ⟨5788740818056397556820645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30873284362967453636376773 5788740818056397556820645)
                  ·
                    refine ⟨1085388903385574541903871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788740818056397556820645 1085388903385574541903871)
                    ·
                      rfl

theorem cell23_6341362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_6341362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341362 prefixEnd_6341362 := by exact prefixLift 6341362
  have htrace : WordTrace (prefixWord ++ tailWord_6341362) baseStart_6341362 baseEnd_6341362 := by
    simpa [prefixWord, tailWord_6341362, baseEnd_6341362] using wordTrace_append hprefix tailTrace_6341362
  have hstable : (prefixWord ++ tailWord_6341362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341362).length < 2 ^ (prefixWord ++ tailWord_6341362).sum := by decide
  have hdescent : baseEnd_6341362 < baseStart_6341362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341402 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_6341402 : Nat := 118140960795 + 6341402 * 2 ^ 59
def prefixEnd_6341402 : Nat := 4983230072969 + 3 ^ 40 * 6341402 * 2
def baseEnd_6341402 : Nat := 3256187249382903469211429

theorem tailTrace_6341402 : CollatzResearch.WordTrace tailWord_6341402 prefixEnd_6341402 3256187249382903469211429 := by
  unfold tailWord_6341402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57822483043047763520666615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154193288114794036055110973 57822483043047763520666615)
  ·
    refine ⟨86733724564571645280999923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57822483043047763520666615 86733724564571645280999923)
    ·
      refine ⟨130100586846857467921499885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86733724564571645280999923 130100586846857467921499885)
      ·
        refine ⟨48787720067571550470562457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130100586846857467921499885 48787720067571550470562457)
        ·
          refine ⟨36590790050678662852921843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48787720067571550470562457 36590790050678662852921843)
          ·
            refine ⟨54886185076017994279382765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36590790050678662852921843 54886185076017994279382765)
            ·
              refine ⟨20582319403506747854768537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54886185076017994279382765 20582319403506747854768537)
              ·
                refine ⟨15436739552630060891076403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20582319403506747854768537 15436739552630060891076403)
                ·
                  refine ⟨23155109328945091336614605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15436739552630060891076403 23155109328945091336614605)
                  ·
                    refine ⟨8683165998354409251230477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23155109328945091336614605 8683165998354409251230477)
                    ·
                      refine ⟨3256187249382903469211429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683165998354409251230477 3256187249382903469211429)
                      ·
                        rfl

theorem cell23_6341402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_6341402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341402 prefixEnd_6341402 := by exact prefixLift 6341402
  have htrace : WordTrace (prefixWord ++ tailWord_6341402) baseStart_6341402 baseEnd_6341402 := by
    simpa [prefixWord, tailWord_6341402, baseEnd_6341402] using wordTrace_append hprefix tailTrace_6341402
  have hstable : (prefixWord ++ tailWord_6341402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341402).length < 2 ^ (prefixWord ++ tailWord_6341402).sum := by decide
  have hdescent : baseEnd_6341402 < baseStart_6341402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341422 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6341422 : Nat := 118140960795 + 6341422 * 2 ^ 59
def prefixEnd_6341422 : Nat := 4983230072969 + 3 ^ 40 * 6341422 * 2
def baseEnd_6341422 : Nat := 1085399172998664463653779

theorem tailTrace_6341422 : CollatzResearch.WordTrace tailWord_6341422 prefixEnd_6341422 1085399172998664463653779 := by
  unfold tailWord_6341422
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911332704014824687299315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154193774421412398332263013 28911332704014824687299315)
  ·
    refine ⟨43366999056022237030948973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28911332704014824687299315 43366999056022237030948973)
    ·
      refine ⟨16262624646008338886605865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43366999056022237030948973 16262624646008338886605865)
      ·
        refine ⟨12196968484506254164954399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16262624646008338886605865 12196968484506254164954399)
        ·
          refine ⟨18295452726759381247431599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196968484506254164954399 18295452726759381247431599)
          ·
            refine ⟨27443179090139071871147399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295452726759381247431599 27443179090139071871147399)
            ·
              refine ⟨41164768635208607806721099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27443179090139071871147399 41164768635208607806721099)
              ·
                refine ⟨61747152952812911710081649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41164768635208607806721099 61747152952812911710081649)
                ·
                  refine ⟨46310364714609683782561237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61747152952812911710081649 46310364714609683782561237)
                  ·
                    refine ⟨1085399172998664463653779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46310364714609683782561237 1085399172998664463653779)
                    ·
                      rfl

theorem cell23_6341422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6341422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341422 prefixEnd_6341422 := by exact prefixLift 6341422
  have htrace : WordTrace (prefixWord ++ tailWord_6341422) baseStart_6341422 baseEnd_6341422 := by
    simpa [prefixWord, tailWord_6341422, baseEnd_6341422] using wordTrace_append hprefix tailTrace_6341422
  have hstable : (prefixWord ++ tailWord_6341422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341422).length < 2 ^ (prefixWord ++ tailWord_6341422).sum := by decide
  have hdescent : baseEnd_6341422 < baseStart_6341422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341425 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6341425 : Nat := 118140960795 + 6341425 * 2 ^ 59
def prefixEnd_6341425 : Nat := 4983230072969 + 3 ^ 40 * 6341425 * 2
def baseEnd_6341425 : Nat := 3256199059437956879223823

theorem tailTrace_6341425 : CollatzResearch.WordTrace tailWord_6341425 prefixEnd_6341425 3256199059437956879223823 := by
  unfold tailWord_6341425
  simp only [CollatzResearch.WordTrace]
  refine ⟨231290771051107729010753729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154193847367405152673835819 231290771051107729010753729)
  ·
    refine ⟨173468078288330796758065297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231290771051107729010753729 173468078288330796758065297)
    ·
      refine ⟨130101058716248097568548973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173468078288330796758065297 130101058716248097568548973)
      ·
        refine ⟨48787897018593036588205865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130101058716248097568548973 48787897018593036588205865)
        ·
          refine ⟨36590922763944777441154399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48787897018593036588205865 36590922763944777441154399)
          ·
            refine ⟨54886384145917166161731599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36590922763944777441154399 54886384145917166161731599)
            ·
              refine ⟨82329576218875749242597399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54886384145917166161731599 82329576218875749242597399)
              ·
                refine ⟨123494364328313623863896099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82329576218875749242597399 123494364328313623863896099)
                ·
                  refine ⟨185241546492470435795844149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123494364328313623863896099 185241546492470435795844149)
                  ·
                    refine ⟨17366394983669103355860389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185241546492470435795844149 17366394983669103355860389)
                    ·
                      refine ⟨3256199059437956879223823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17366394983669103355860389 3256199059437956879223823)
                      ·
                        rfl

theorem cell23_6341425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6341425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341425 prefixEnd_6341425 := by exact prefixLift 6341425
  have htrace : WordTrace (prefixWord ++ tailWord_6341425) baseStart_6341425 baseEnd_6341425 := by
    simpa [prefixWord, tailWord_6341425, baseEnd_6341425] using wordTrace_append hprefix tailTrace_6341425
  have hstable : (prefixWord ++ tailWord_6341425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341425).length < 2 ^ (prefixWord ++ tailWord_6341425).sum := by decide
  have hdescent : baseEnd_6341425 < baseStart_6341425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341429 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6341429 : Nat := 118140960795 + 6341429 * 2 ^ 59
def prefixEnd_6341429 : Nat := 4983230072969 + 3 ^ 40 * 6341429 * 2
def baseEnd_6341429 : Nat := 3256201113360574863573805

theorem tailTrace_6341429 : CollatzResearch.WordTrace tailWord_6341429 prefixEnd_6341429 3256201113360574863573805 := by
  unfold tailWord_6341429
  simp only [CollatzResearch.WordTrace]
  refine ⟨231290916943093237693899341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154193944628728825129266227 231290916943093237693899341)
  ·
    refine ⟨86734093853659964135212253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231290916943093237693899341 86734093853659964135212253)
    ·
      refine ⟨32525285195122486550704595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86734093853659964135212253 32525285195122486550704595)
      ·
        refine ⟨48787927792683729826056893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32525285195122486550704595 48787927792683729826056893)
        ·
          refine ⟨18295472922256398684771335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48787927792683729826056893 18295472922256398684771335)
          ·
            refine ⟨27443209383384598027157003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295472922256398684771335 27443209383384598027157003)
            ·
              refine ⟨41164814075076897040735505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27443209383384598027157003 41164814075076897040735505)
              ·
                refine ⟨30873610556307672780551629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41164814075076897040735505 30873610556307672780551629)
                ·
                  refine ⟨11577603958615377292706861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30873610556307672780551629 11577603958615377292706861)
                  ·
                    refine ⟨4341601484480766484765073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11577603958615377292706861 4341601484480766484765073)
                    ·
                      refine ⟨3256201113360574863573805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341601484480766484765073 3256201113360574863573805)
                      ·
                        rfl

theorem cell23_6341429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6341429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341429 prefixEnd_6341429 := by exact prefixLift 6341429
  have htrace : WordTrace (prefixWord ++ tailWord_6341429) baseStart_6341429 baseEnd_6341429 := by
    simpa [prefixWord, tailWord_6341429, baseEnd_6341429] using wordTrace_append hprefix tailTrace_6341429
  have hstable : (prefixWord ++ tailWord_6341429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341429).length < 2 ^ (prefixWord ++ tailWord_6341429).sum := by decide
  have hdescent : baseEnd_6341429 < baseStart_6341429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341445 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_6341445 : Nat := 118140960795 + 6341445 * 2 ^ 59
def prefixEnd_6341445 : Nat := 4983230072969 + 3 ^ 40 * 6341445 * 2
def baseEnd_6341445 : Nat := 3256209329051046800973731

theorem tailTrace_6341445 : CollatzResearch.WordTrace tailWord_6341445 prefixEnd_6341445 3256209329051046800973731 := by
  unfold tailWord_6341445
  simp only [CollatzResearch.WordTrace]
  refine ⟨231291500511035272426481789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154194333674023514950987859 231291500511035272426481789)
  ·
    refine ⟨86734312691638227159930671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231291500511035272426481789 86734312691638227159930671)
    ·
      refine ⟨130101469037457340739896007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86734312691638227159930671 130101469037457340739896007)
      ·
        refine ⟨195152203556186011109844011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130101469037457340739896007 195152203556186011109844011)
        ·
          refine ⟨292728305334279016664766017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195152203556186011109844011 292728305334279016664766017)
          ·
            refine ⟨219546229000709262498574513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292728305334279016664766017 219546229000709262498574513)
            ·
              refine ⟨164659671750531946873930885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219546229000709262498574513 164659671750531946873930885)
              ·
                refine ⟨30873688453224740038862041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164659671750531946873930885 30873688453224740038862041)
                ·
                  refine ⟨23155266339918555029146531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30873688453224740038862041 23155266339918555029146531)
                  ·
                    refine ⟨34732899509877832543719797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23155266339918555029146531 34732899509877832543719797)
                    ·
                      refine ⟨3256209329051046800973731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34732899509877832543719797 3256209329051046800973731)
                      ·
                        rfl

theorem cell23_6341445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_6341445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341445 prefixEnd_6341445 := by exact prefixLift 6341445
  have htrace : WordTrace (prefixWord ++ tailWord_6341445) baseStart_6341445 baseEnd_6341445 := by
    simpa [prefixWord, tailWord_6341445, baseEnd_6341445] using wordTrace_append hprefix tailTrace_6341445
  have hstable : (prefixWord ++ tailWord_6341445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341445).length < 2 ^ (prefixWord ++ tailWord_6341445).sum := by decide
  have hdescent : baseEnd_6341445 < baseStart_6341445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341463 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 1, 3, 2]
def baseStart_6341463 : Nat := 118140960795 + 6341463 * 2 ^ 59
def prefixEnd_6341463 : Nat := 4983230072969 + 3 ^ 40 * 6341463 * 2
def baseEnd_6341463 : Nat := 3256218571702827730548649

theorem tailTrace_6341463 : CollatzResearch.WordTrace tailWord_6341463 prefixEnd_6341463 3256218571702827730548649 := by
  unfold tailWord_6341463
  simp only [CollatzResearch.WordTrace]
  refine ⟨231292157024970061500637043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154194771349980041000424695 231292157024970061500637043)
  ·
    refine ⟨346938235537455092250955565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231292157024970061500637043 346938235537455092250955565)
    ·
      refine ⟨130101838326545659594108337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 346938235537455092250955565 130101838326545659594108337)
      ·
        refine ⟨97576378744909244695581253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130101838326545659594108337 97576378744909244695581253)
        ·
          refine ⟨18295571014670483380421485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97576378744909244695581253 18295571014670483380421485)
          ·
            refine ⟨6860839130501431267658057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18295571014670483380421485 6860839130501431267658057)
            ·
              refine ⟨5145629347876073450743543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860839130501431267658057 5145629347876073450743543)
              ·
                refine ⟨7718444021814110176115315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145629347876073450743543 7718444021814110176115315)
                ·
                  refine ⟨11577666032721165264172973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718444021814110176115315 11577666032721165264172973)
                  ·
                    refine ⟨4341624762270436974064865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11577666032721165264172973 4341624762270436974064865)
                    ·
                      refine ⟨3256218571702827730548649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341624762270436974064865 3256218571702827730548649)
                      ·
                        rfl

theorem cell23_6341463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_6341463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341463 prefixEnd_6341463 := by exact prefixLift 6341463
  have htrace : WordTrace (prefixWord ++ tailWord_6341463) baseStart_6341463 baseEnd_6341463 := by
    simpa [prefixWord, tailWord_6341463, baseEnd_6341463] using wordTrace_append hprefix tailTrace_6341463
  have hstable : (prefixWord ++ tailWord_6341463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341463).length < 2 ^ (prefixWord ++ tailWord_6341463).sum := by decide
  have hdescent : baseEnd_6341463 < baseStart_6341463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341476 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_6341476 : Nat := 118140960795 + 6341476 * 2 ^ 59
def prefixEnd_6341476 : Nat := 4983230072969 + 3 ^ 40 * 6341476 * 2
def baseEnd_6341476 : Nat := 3256225246951336179686089

theorem tailTrace_6341476 : CollatzResearch.WordTrace tailWord_6341476 prefixEnd_6341476 3256225246951336179686089 := by
  unfold tailWord_6341476
  simp only [CollatzResearch.WordTrace]
  refine ⟨115646315586961482360430141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154195087449281976480573521 115646315586961482360430141)
  ·
    refine ⟨43367368345110555885161303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115646315586961482360430141 43367368345110555885161303)
    ·
      refine ⟨65051052517665833827741955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43367368345110555885161303 65051052517665833827741955)
      ·
        refine ⟨97576578776498750741612933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65051052517665833827741955 97576578776498750741612933)
        ·
          refine ⟨18295608520593515764052425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97576578776498750741612933 18295608520593515764052425)
          ·
            refine ⟨13721706390445136823039319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18295608520593515764052425 13721706390445136823039319)
            ·
              refine ⟨20582559585667705234558979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13721706390445136823039319 20582559585667705234558979)
              ·
                refine ⟨30873839378501557851838469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20582559585667705234558979 30873839378501557851838469)
                ·
                  refine ⟨5788844883469042097219713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30873839378501557851838469 5788844883469042097219713)
                  ·
                    refine ⟨4341633662601781572914785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788844883469042097219713 4341633662601781572914785)
                    ·
                      refine ⟨3256225246951336179686089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341633662601781572914785 3256225246951336179686089)
                      ·
                        rfl

theorem cell23_6341476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_6341476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341476 prefixEnd_6341476 := by exact prefixLift 6341476
  have htrace : WordTrace (prefixWord ++ tailWord_6341476) baseStart_6341476 baseEnd_6341476 := by
    simpa [prefixWord, tailWord_6341476, baseEnd_6341476] using wordTrace_append hprefix tailTrace_6341476
  have hstable : (prefixWord ++ tailWord_6341476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341476).length < 2 ^ (prefixWord ++ tailWord_6341476).sum := by decide
  have hdescent : baseEnd_6341476 < baseStart_6341476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341512 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_6341512 : Nat := 118140960795 + 6341512 * 2 ^ 59
def prefixEnd_6341512 : Nat := 4983230072969 + 3 ^ 40 * 6341512 * 2
def baseEnd_6341512 : Nat := 1085414577418299346278641

theorem tailTrace_6341512 : CollatzResearch.WordTrace tailWord_6341512 prefixEnd_6341512 1085414577418299346278641 := by
  unfold tailWord_6341512
  simp only [CollatzResearch.WordTrace]
  refine ⟨115646972100896271434585395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154195962801195028579447193 115646972100896271434585395)
  ·
    refine ⟨173470458151344407151878093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115646972100896271434585395 173470458151344407151878093)
    ·
      refine ⟨65051421806754152681954285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173470458151344407151878093 65051421806754152681954285)
      ·
        refine ⟨24394283177532807255732857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65051421806754152681954285 24394283177532807255732857)
        ·
          refine ⟨18295712383149605441799643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24394283177532807255732857 18295712383149605441799643)
          ·
            refine ⟨27443568574724408162699465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295712383149605441799643 27443568574724408162699465)
            ·
              refine ⟨20582676431043306122024599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27443568574724408162699465 20582676431043306122024599)
              ·
                refine ⟨30874014646564959183036899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20582676431043306122024599 30874014646564959183036899)
                ·
                  refine ⟨46311021969847438774555349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30874014646564959183036899 46311021969847438774555349)
                  ·
                    refine ⟨1085414577418299346278641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46311021969847438774555349 1085414577418299346278641)
                    ·
                      rfl

theorem cell23_6341512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_6341512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341512 prefixEnd_6341512 := by exact prefixLift 6341512
  have htrace : WordTrace (prefixWord ++ tailWord_6341512) baseStart_6341512 baseEnd_6341512 := by
    simpa [prefixWord, tailWord_6341512, baseEnd_6341512] using wordTrace_append hprefix tailTrace_6341512
  have hstable : (prefixWord ++ tailWord_6341512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341512).length < 2 ^ (prefixWord ++ tailWord_6341512).sum := by decide
  have hdescent : baseEnd_6341512 < baseStart_6341512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341555 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 10]
def baseStart_6341555 : Nat := 118140960795 + 6341555 * 2 ^ 59
def prefixEnd_6341555 : Nat := 4983230072969 + 3 ^ 40 * 6341555 * 2
def baseEnd_6341555 : Nat := 361807312435893485622025

theorem tailTrace_6341555 : CollatzResearch.WordTrace tailWord_6341555 prefixEnd_6341555 361807312435893485622025 := by
  unfold tailWord_6341555
  simp only [CollatzResearch.WordTrace]
  refine ⟨231295512540636761212986119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154197008360424507475324079 231295512540636761212986119)
  ·
    refine ⟨346943268810955141819479179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231295512540636761212986119 346943268810955141819479179)
    ·
      refine ⟨520414903216432712729218769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346943268810955141819479179 520414903216432712729218769)
      ·
        refine ⟨390311177412324534546914077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520414903216432712729218769 390311177412324534546914077)
        ·
          refine ⟨146366691529621700455092779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390311177412324534546914077 146366691529621700455092779)
          ·
            refine ⟨219550037294432550682639169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146366691529621700455092779 219550037294432550682639169)
            ·
              refine ⟨164662527970824413011979377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219550037294432550682639169 164662527970824413011979377)
              ·
                refine ⟨123496895978118309758984533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164662527970824413011979377 123496895978118309758984533)
                ·
                  refine ⟨361807312435893485622025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123496895978118309758984533 361807312435893485622025)
                  ·
                    rfl

theorem cell23_6341555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 10].length) (baseStart_6341555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341555 prefixEnd_6341555 := by exact prefixLift 6341555
  have htrace : WordTrace (prefixWord ++ tailWord_6341555) baseStart_6341555 baseEnd_6341555 := by
    simpa [prefixWord, tailWord_6341555, baseEnd_6341555] using wordTrace_append hprefix tailTrace_6341555
  have hstable : (prefixWord ++ tailWord_6341555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341555).length < 2 ^ (prefixWord ++ tailWord_6341555).sum := by decide
  have hdescent : baseEnd_6341555 < baseStart_6341555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341586 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6341586 : Nat := 118140960795 + 6341586 * 2 ^ 59
def prefixEnd_6341586 : Nat := 4983230072969 + 3 ^ 40 * 6341586 * 2
def baseEnd_6341586 : Nat := 3256281729823330749310583

theorem tailTrace_6341586 : CollatzResearch.WordTrace tailWord_6341586 prefixEnd_6341586 3256281729823330749310583 := by
  unfold tailWord_6341586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57824160800881113376841153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154197762135682969004909741 57824160800881113376841153)
  ·
    refine ⟨43368120600660835032630865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57824160800881113376841153 43368120600660835032630865)
    ·
      refine ⟨32526090450495626274473149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43368120600660835032630865 32526090450495626274473149)
      ·
        refine ⟨12197283918935859852927431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32526090450495626274473149 12197283918935859852927431)
        ·
          refine ⟨18295925878403789779391147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12197283918935859852927431 18295925878403789779391147)
          ·
            refine ⟨27443888817605684669086721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295925878403789779391147 27443888817605684669086721)
            ·
              refine ⟨20582916613204263501815041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27443888817605684669086721 20582916613204263501815041)
              ·
                refine ⟨15437187459903197626361281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20582916613204263501815041 15437187459903197626361281)
                ·
                  refine ⟨11577890594927398219770961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15437187459903197626361281 11577890594927398219770961)
                  ·
                    refine ⟨8683417946195548664828221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11577890594927398219770961 8683417946195548664828221)
                    ·
                      refine ⟨3256281729823330749310583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683417946195548664828221 3256281729823330749310583)
                      ·
                        rfl

theorem cell23_6341586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6341586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341586 prefixEnd_6341586 := by exact prefixLift 6341586
  have htrace : WordTrace (prefixWord ++ tailWord_6341586) baseStart_6341586 baseEnd_6341586 := by
    simpa [prefixWord, tailWord_6341586, baseEnd_6341586] using wordTrace_append hprefix tailTrace_6341586
  have hstable : (prefixWord ++ tailWord_6341586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341586).length < 2 ^ (prefixWord ++ tailWord_6341586).sum := by decide
  have hdescent : baseEnd_6341586 < baseStart_6341586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341593 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 1, 4]
def baseStart_6341593 : Nat := 118140960795 + 6341593 * 2 ^ 59
def prefixEnd_6341593 : Nat := 4983230072969 + 3 ^ 40 * 6341593 * 2
def baseEnd_6341593 : Nat := 1085428441395970740641017

theorem tailTrace_6341593 : CollatzResearch.WordTrace tailWord_6341593 prefixEnd_6341593 1085428441395970740641017 := by
  unfold tailWord_6341593
  simp only [CollatzResearch.WordTrace]
  refine ⟨231296898514499093702869433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154197932342999395801912955 231296898514499093702869433)
  ·
    refine ⟨173472673885874320277152075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231296898514499093702869433 173472673885874320277152075)
    ·
      refine ⟨260209010828811480415728113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173472673885874320277152075 260209010828811480415728113)
      ·
        refine ⟨195156758121608610311796085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260209010828811480415728113 195156758121608610311796085)
        ·
          refine ⟨18295946073900807216730883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195156758121608610311796085 18295946073900807216730883)
          ·
            refine ⟨27443919110851210825096325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295946073900807216730883 27443919110851210825096325)
            ·
              refine ⟨5145734833284602029705561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27443919110851210825096325 5145734833284602029705561)
              ·
                refine ⟨3859301124963451522279171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145734833284602029705561 3859301124963451522279171)
                ·
                  refine ⟨5788951687445177283418757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859301124963451522279171 5788951687445177283418757)
                  ·
                    refine ⟨1085428441395970740641017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5788951687445177283418757 1085428441395970740641017)
                    ·
                      rfl

theorem cell23_6341593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_6341593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341593 prefixEnd_6341593 := by exact prefixLift 6341593
  have htrace : WordTrace (prefixWord ++ tailWord_6341593) baseStart_6341593 baseEnd_6341593 := by
    simpa [prefixWord, tailWord_6341593, baseEnd_6341593] using wordTrace_append hprefix tailTrace_6341593
  have hstable : (prefixWord ++ tailWord_6341593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341593).length < 2 ^ (prefixWord ++ tailWord_6341593).sum := by decide
  have hdescent : baseEnd_6341593 < baseStart_6341593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341633 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6341633 : Nat := 118140960795 + 6341633 * 2 ^ 59
def prefixEnd_6341633 : Nat := 4983230072969 + 3 ^ 40 * 6341633 * 2
def baseEnd_6341633 : Nat := 3256305863414092065422867

theorem tailTrace_6341633 : CollatzResearch.WordTrace tailWord_6341633 prefixEnd_6341633 3256305863414092065422867 := by
  unfold tailWord_6341633
  simp only [CollatzResearch.WordTrace]
  refine ⟨231298357434354180534325553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154198904956236120356217035 231298357434354180534325553)
  ·
    refine ⟨173473768075765635400744165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231298357434354180534325553 173473768075765635400744165)
    ·
      refine ⟨32526331514206056637639531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173473768075765635400744165 32526331514206056637639531)
      ·
        refine ⟨48789497271309084956459297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32526331514206056637639531 48789497271309084956459297)
        ·
          refine ⟨36592122953481813717344473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48789497271309084956459297 36592122953481813717344473)
          ·
            refine ⟨27444092215111360288008355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36592122953481813717344473 27444092215111360288008355)
            ·
              refine ⟨41166138322667040432012533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27444092215111360288008355 41166138322667040432012533)
              ·
                refine ⟨3859325467750035040501175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41166138322667040432012533 3859325467750035040501175)
                ·
                  refine ⟨5788988201625052560751763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859325467750035040501175 5788988201625052560751763)
                  ·
                    refine ⟨8683482302437578841127645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788988201625052560751763 8683482302437578841127645)
                    ·
                      refine ⟨3256305863414092065422867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683482302437578841127645 3256305863414092065422867)
                      ·
                        rfl

theorem cell23_6341633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6341633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341633 prefixEnd_6341633 := by exact prefixLift 6341633
  have htrace : WordTrace (prefixWord ++ tailWord_6341633) baseStart_6341633 baseEnd_6341633 := by
    simpa [prefixWord, tailWord_6341633, baseEnd_6341633] using wordTrace_append hprefix tailTrace_6341633
  have hstable : (prefixWord ++ tailWord_6341633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341633).length < 2 ^ (prefixWord ++ tailWord_6341633).sum := by decide
  have hdescent : baseEnd_6341633 < baseStart_6341633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341666 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6341666 : Nat := 118140960795 + 6341666 * 2 ^ 59
def prefixEnd_6341666 : Nat := 4983230072969 + 3 ^ 40 * 6341666 * 2
def baseEnd_6341666 : Nat := 1085440936091896812103405

theorem tailTrace_6341666 : CollatzResearch.WordTrace tailWord_6341666 prefixEnd_6341666 1085440936091896812103405 := by
  unfold tailWord_6341666
  simp only [CollatzResearch.WordTrace]
  refine ⟨57824890260808656792569213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154199707362156418113517901 57824890260808656792569213)
  ·
    refine ⟨21684333847803246297213455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57824890260808656792569213 21684333847803246297213455)
    ·
      refine ⟨32526500771704869445820183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21684333847803246297213455 32526500771704869445820183)
      ·
        refine ⟨48789751157557304168730275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32526500771704869445820183 48789751157557304168730275)
        ·
          refine ⟨73184626736335956253095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48789751157557304168730275 73184626736335956253095413)
          ·
            refine ⟨6861058756531495898727695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73184626736335956253095413 6861058756531495898727695)
            ·
              refine ⟨10291588134797243848091543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861058756531495898727695 10291588134797243848091543)
              ·
                refine ⟨15437382202195865772137315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10291588134797243848091543 15437382202195865772137315)
                ·
                  refine ⟨23156073303293798658205973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15437382202195865772137315 23156073303293798658205973)
                  ·
                    refine ⟨1085440936091896812103405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23156073303293798658205973 1085440936091896812103405)
                    ·
                      rfl

theorem cell23_6341666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6341666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341666 prefixEnd_6341666 := by exact prefixLift 6341666
  have htrace : WordTrace (prefixWord ++ tailWord_6341666) baseStart_6341666 baseEnd_6341666 := by
    simpa [prefixWord, tailWord_6341666, baseEnd_6341666] using wordTrace_append hprefix tailTrace_6341666
  have hstable : (prefixWord ++ tailWord_6341666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341666).length < 2 ^ (prefixWord ++ tailWord_6341666).sum := by decide
  have hdescent : baseEnd_6341666 < baseStart_6341666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341676 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_6341676 : Nat := 118140960795 + 6341676 * 2 ^ 59
def prefixEnd_6341676 : Nat := 4983230072969 + 3 ^ 40 * 6341676 * 2
def baseEnd_6341676 : Nat := 3256327943082235397185169

theorem tailTrace_6341676 : CollatzResearch.WordTrace tailWord_6341676 prefixEnd_6341676 3256327943082235397185169 := by
  unfold tailWord_6341676
  simp only [CollatzResearch.WordTrace]
  refine ⟨115649962886599199439070441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154199950515465599252093921 115649962886599199439070441)
  ·
    refine ⟨86737472164949399579302831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115649962886599199439070441 86737472164949399579302831)
    ·
      refine ⟨130106208247424099368954247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86737472164949399579302831 130106208247424099368954247)
      ·
        refine ⟨195159312371136149053431371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130106208247424099368954247 195159312371136149053431371)
        ·
          refine ⟨292738968556704223580147057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195159312371136149053431371 292738968556704223580147057)
          ·
            refine ⟨219554226417528167685110293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292738968556704223580147057 219554226417528167685110293)
            ·
              refine ⟨10291604363321632860239545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219554226417528167685110293 10291604363321632860239545)
              ·
                refine ⟨7718703272491224645179659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10291604363321632860239545 7718703272491224645179659)
                ·
                  refine ⟨11578054908736836967769489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718703272491224645179659 11578054908736836967769489)
                  ·
                    refine ⟨8683541181552627725827117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11578054908736836967769489 8683541181552627725827117)
                    ·
                      refine ⟨3256327943082235397185169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683541181552627725827117 3256327943082235397185169)
                      ·
                        rfl

theorem cell23_6341676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_6341676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341676 prefixEnd_6341676 := by exact prefixLift 6341676
  have htrace : WordTrace (prefixWord ++ tailWord_6341676) baseStart_6341676 baseEnd_6341676 := by
    simpa [prefixWord, tailWord_6341676, baseEnd_6341676] using wordTrace_append hprefix tailTrace_6341676
  have hstable : (prefixWord ++ tailWord_6341676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341676).length < 2 ^ (prefixWord ++ tailWord_6341676).sum := by decide
  have hdescent : baseEnd_6341676 < baseStart_6341676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341690 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_6341690 : Nat := 118140960795 + 6341690 * 2 ^ 59
def prefixEnd_6341690 : Nat := 4983230072969 + 3 ^ 40 * 6341690 * 2
def baseEnd_6341690 : Nat := 3256335131811398342410105

theorem tailTrace_6341690 : CollatzResearch.WordTrace tailWord_6341690 prefixEnd_6341690 3256335131811398342410105 := by
  unfold tailWord_6341690
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825109098786919817287631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154200290930098452846100349 57825109098786919817287631)
  ·
    refine ⟨86737663648180379725931447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825109098786919817287631 86737663648180379725931447)
    ·
      refine ⟨130106495472270569588897171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86737663648180379725931447 130106495472270569588897171)
      ·
        refine ⟨195159743208405854383345757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130106495472270569588897171 195159743208405854383345757)
        ·
          refine ⟨73184903703152195393754659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195159743208405854383345757 73184903703152195393754659)
          ·
            refine ⟨109777355554728293090631989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73184903703152195393754659 109777355554728293090631989)
            ·
              refine ⟨10291627083255777477246749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109777355554728293090631989 10291627083255777477246749)
              ·
                refine ⟨3859360156220916553967531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10291627083255777477246749 3859360156220916553967531)
                ·
                  refine ⟨5789040234331374830951297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859360156220916553967531 5789040234331374830951297)
                  ·
                    refine ⟨4341780175748531123213473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789040234331374830951297 4341780175748531123213473)
                    ·
                      refine ⟨3256335131811398342410105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341780175748531123213473 3256335131811398342410105)
                      ·
                        rfl

theorem cell23_6341690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_6341690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341690 prefixEnd_6341690 := by exact prefixLift 6341690
  have htrace : WordTrace (prefixWord ++ tailWord_6341690) baseStart_6341690 baseEnd_6341690 := by
    simpa [prefixWord, tailWord_6341690, baseEnd_6341690] using wordTrace_append hprefix tailTrace_6341690
  have hstable : (prefixWord ++ tailWord_6341690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341690).length < 2 ^ (prefixWord ++ tailWord_6341690).sum := by decide
  have hdescent : baseEnd_6341690 < baseStart_6341690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341706 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_6341706 : Nat := 118140960795 + 6341706 * 2 ^ 59
def prefixEnd_6341706 : Nat := 4983230072969 + 3 ^ 40 * 6341706 * 2
def baseEnd_6341706 : Nat := 3256343347501870279810031

theorem tailTrace_6341706 : CollatzResearch.WordTrace tailWord_6341706 prefixEnd_6341706 3256343347501870279810031 := by
  unfold tailWord_6341706
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825254990772428500433243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154200679975393142667821981 57825254990772428500433243)
  ·
    refine ⟨86737882486158642750649865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825254990772428500433243 86737882486158642750649865)
    ·
      refine ⟨65053411864618982062987399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86737882486158642750649865 65053411864618982062987399)
      ·
        refine ⟨97580117796928473094481099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65053411864618982062987399 97580117796928473094481099)
        ·
          refine ⟨146370176695392709641721649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97580117796928473094481099 146370176695392709641721649)
          ·
            refine ⟨109777632521544532231291237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146370176695392709641721649 109777632521544532231291237)
            ·
              refine ⟨20583306097789599793367107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109777632521544532231291237 20583306097789599793367107)
              ·
                refine ⟨30874959146684399690050661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583306097789599793367107 30874959146684399690050661)
                ·
                  refine ⟨5789054840003324941884499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30874959146684399690050661 5789054840003324941884499)
                  ·
                    refine ⟨8683582260004987412826749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789054840003324941884499 8683582260004987412826749)
                    ·
                      refine ⟨3256343347501870279810031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683582260004987412826749 3256343347501870279810031)
                      ·
                        rfl

theorem cell23_6341706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_6341706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341706 prefixEnd_6341706 := by exact prefixLift 6341706
  have htrace : WordTrace (prefixWord ++ tailWord_6341706) baseStart_6341706 baseEnd_6341706 := by
    simpa [prefixWord, tailWord_6341706, baseEnd_6341706] using wordTrace_append hprefix tailTrace_6341706
  have hstable : (prefixWord ++ tailWord_6341706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341706).length < 2 ^ (prefixWord ++ tailWord_6341706).sum := by decide
  have hdescent : baseEnd_6341706 < baseStart_6341706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341779 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3]
def baseStart_6341779 : Nat := 118140960795 + 6341779 * 2 ^ 59
def prefixEnd_6341779 : Nat := 4983230072969 + 3 ^ 40 * 6341779 * 2
def baseEnd_6341779 : Nat := 3256380831589648494197195

theorem tailTrace_6341779 : CollatzResearch.WordTrace tailWord_6341779 prefixEnd_6341779 3256380831589648494197195 := by
  unfold tailWord_6341779
  simp only [CollatzResearch.WordTrace]
  refine ⟨231303682491825247469140391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154202454994550164979426927 231303682491825247469140391)
  ·
    refine ⟨346955523737737871203710587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231303682491825247469140391 346955523737737871203710587)
    ·
      refine ⟨520433285606606806805565881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346955523737737871203710587 520433285606606806805565881)
      ·
        refine ⟨390324964204955105104174411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520433285606606806805565881 390324964204955105104174411)
        ·
          refine ⟨585487446307432657656261617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390324964204955105104174411 585487446307432657656261617)
          ·
            refine ⟨439115584730574493242196213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585487446307432657656261617 439115584730574493242196213)
            ·
              refine ⟨41167086068491358741455895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439115584730574493242196213 41167086068491358741455895)
              ·
                refine ⟨61750629102737038112183843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41167086068491358741455895 61750629102737038112183843)
                ·
                  refine ⟨92625943654105557168275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61750629102737038112183843 92625943654105557168275765)
                  ·
                    refine ⟨8683682217572395984525853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92625943654105557168275765 8683682217572395984525853)
                    ·
                      refine ⟨3256380831589648494197195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683682217572395984525853 3256380831589648494197195)
                      ·
                        rfl

theorem cell23_6341779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_6341779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341779 prefixEnd_6341779 := by exact prefixLift 6341779
  have htrace : WordTrace (prefixWord ++ tailWord_6341779) baseStart_6341779 baseEnd_6341779 := by
    simpa [prefixWord, tailWord_6341779, baseEnd_6341779] using wordTrace_append hprefix tailTrace_6341779
  have hstable : (prefixWord ++ tailWord_6341779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341779).length < 2 ^ (prefixWord ++ tailWord_6341779).sum := by decide
  have hdescent : baseEnd_6341779 < baseStart_6341779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341786 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_6341786 : Nat := 118140960795 + 6341786 * 2 ^ 59
def prefixEnd_6341786 : Nat := 4983230072969 + 3 ^ 40 * 6341786 * 2
def baseEnd_6341786 : Nat := 361820491772692218534407

theorem tailTrace_6341786 : CollatzResearch.WordTrace tailWord_6341786 prefixEnd_6341786 361820491772692218534407 := by
  unfold tailWord_6341786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825984450699971916161303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154202625201866591776430141 57825984450699971916161303)
  ·
    refine ⟨86738976676049957874241955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825984450699971916161303 86738976676049957874241955)
    ·
      refine ⟨130108465014074936811362933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86738976676049957874241955 130108465014074936811362933)
      ·
        refine ⟨12197668595069525326065275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130108465014074936811362933 12197668595069525326065275)
        ·
          refine ⟨18296502892604287989097913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12197668595069525326065275 18296502892604287989097913)
          ·
            refine ⟨13722377169453215991823435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18296502892604287989097913 13722377169453215991823435)
            ·
              refine ⟨20583565754179823987735153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13722377169453215991823435 20583565754179823987735153)
              ·
                refine ⟨15437674315634867990801365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20583565754179823987735153 15437674315634867990801365)
                ·
                  refine ⟨361820491772692218534407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15437674315634867990801365 361820491772692218534407)
                  ·
                    rfl

theorem cell23_6341786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_6341786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341786 prefixEnd_6341786 := by exact prefixLift 6341786
  have htrace : WordTrace (prefixWord ++ tailWord_6341786) baseStart_6341786 baseEnd_6341786 := by
    simpa [prefixWord, tailWord_6341786, baseEnd_6341786] using wordTrace_append hprefix tailTrace_6341786
  have hstable : (prefixWord ++ tailWord_6341786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341786).length < 2 ^ (prefixWord ++ tailWord_6341786).sum := by decide
  have hdescent : baseEnd_6341786 < baseStart_6341786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341814 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6341814 : Nat := 118140960795 + 6341814 * 2 ^ 59
def prefixEnd_6341814 : Nat := 4983230072969 + 3 ^ 40 * 6341814 * 2
def baseEnd_6341814 : Nat := 3256398803412555857259535

theorem tailTrace_6341814 : CollatzResearch.WordTrace tailWord_6341814 prefixEnd_6341814 3256398803412555857259535 := by
  unfold tailWord_6341814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456559940418653027916531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154203306031132298964442997 14456559940418653027916531)
  ·
    refine ⟨21684839910627979541874797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14456559940418653027916531 21684839910627979541874797)
    ·
      refine ⟨8131814966485492328203049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21684839910627979541874797 8131814966485492328203049)
      ·
        refine ⟨6098861224864119246152287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8131814966485492328203049 6098861224864119246152287)
        ·
          refine ⟨9148291837296178869228431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098861224864119246152287 9148291837296178869228431)
          ·
            refine ⟨13722437755944268303842647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148291837296178869228431 13722437755944268303842647)
            ·
              refine ⟨20583656633916402455763971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13722437755944268303842647 20583656633916402455763971)
              ·
                refine ⟨30875484950874603683645957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583656633916402455763971 30875484950874603683645957)
                ·
                  refine ⟨5789153428288988190683617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30875484950874603683645957 5789153428288988190683617)
                  ·
                    refine ⟨4341865071216741143012713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789153428288988190683617 4341865071216741143012713)
                    ·
                      refine ⟨3256398803412555857259535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341865071216741143012713 3256398803412555857259535)
                      ·
                        rfl

theorem cell23_6341814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6341814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341814 prefixEnd_6341814 := by exact prefixLift 6341814
  have htrace : WordTrace (prefixWord ++ tailWord_6341814) baseStart_6341814 baseEnd_6341814 := by
    simpa [prefixWord, tailWord_6341814, baseEnd_6341814] using wordTrace_append hprefix tailTrace_6341814
  have hstable : (prefixWord ++ tailWord_6341814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341814).length < 2 ^ (prefixWord ++ tailWord_6341814).sum := by decide
  have hdescent : baseEnd_6341814 < baseStart_6341814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341849 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_6341849 : Nat := 118140960795 + 6341849 * 2 ^ 59
def prefixEnd_6341849 : Nat := 4983230072969 + 3 ^ 40 * 6341849 * 2
def baseEnd_6341849 : Nat := 3256416775235463220321873

theorem tailTrace_6341849 : CollatzResearch.WordTrace tailWord_6341849 prefixEnd_6341849 3256416775235463220321873 := by
  unfold tailWord_6341849
  simp only [CollatzResearch.WordTrace]
  refine ⟨231306235601571649424188601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154204157067714432949459067 231306235601571649424188601)
  ·
    refine ⟨173479676701178737068141451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231306235601571649424188601 173479676701178737068141451)
    ·
      refine ⟨260219515051768105602212177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173479676701178737068141451 260219515051768105602212177)
      ·
        refine ⟨195164636288826079201659133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260219515051768105602212177 195164636288826079201659133)
        ·
          refine ⟨73186738608309779700622175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195164636288826079201659133 73186738608309779700622175)
          ·
            refine ⟨109780107912464669550933263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73186738608309779700622175 109780107912464669550933263)
            ·
              refine ⟨164670161868697004326399895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109780107912464669550933263 164670161868697004326399895)
              ·
                refine ⟨247005242803045506489599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164670161868697004326399895 247005242803045506489599843)
                ·
                  refine ⟨370507864204568259734399765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247005242803045506489599843 370507864204568259734399765)
                  ·
                    refine ⟨17367556134589137175049989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 370507864204568259734399765 17367556134589137175049989)
                    ·
                      refine ⟨3256416775235463220321873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17367556134589137175049989 3256416775235463220321873)
                      ·
                        rfl

theorem cell23_6341849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_6341849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341849 prefixEnd_6341849 := by exact prefixLift 6341849
  have htrace : WordTrace (prefixWord ++ tailWord_6341849) baseStart_6341849 baseEnd_6341849 := by
    simpa [prefixWord, tailWord_6341849, baseEnd_6341849] using wordTrace_append hprefix tailTrace_6341849
  have hstable : (prefixWord ++ tailWord_6341849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341849).length < 2 ^ (prefixWord ++ tailWord_6341849).sum := by decide
  have hdescent : baseEnd_6341849 < baseStart_6341849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341856 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_6341856 : Nat := 118140960795 + 6341856 * 2 ^ 59
def prefixEnd_6341856 : Nat := 4983230072969 + 3 ^ 40 * 6341856 * 2
def baseEnd_6341856 : Nat := 3256420369600044692934341

theorem tailTrace_6341856 : CollatzResearch.WordTrace tailWord_6341856 prefixEnd_6341856 3256420369600044692934341 := by
  unfold tailWord_6341856
  simp only [CollatzResearch.WordTrace]
  refine ⟨115653245456273144809846711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154204327275030859746462281 115653245456273144809846711)
  ·
    refine ⟨173479868184409717214770067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115653245456273144809846711 173479868184409717214770067)
    ·
      refine ⟨260219802276614575822155101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173479868184409717214770067 260219802276614575822155101)
      ·
        refine ⟨97582425853730465933308163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260219802276614575822155101 97582425853730465933308163)
        ·
          refine ⟨146373638780595698899962245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97582425853730465933308163 146373638780595698899962245)
          ·
            refine ⟨27445057271361693543742921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146373638780595698899962245 27445057271361693543742921)
            ·
              refine ⟨20583792953521270157807191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27445057271361693543742921 20583792953521270157807191)
              ·
                refine ⟨30875689430281905236710787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583792953521270157807191 30875689430281905236710787)
                ·
                  refine ⟨46313534145422857855066181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30875689430281905236710787 46313534145422857855066181)
                  ·
                    refine ⟨8683787652266785847824909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46313534145422857855066181 8683787652266785847824909)
                    ·
                      refine ⟨3256420369600044692934341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683787652266785847824909 3256420369600044692934341)
                      ·
                        rfl

theorem cell23_6341856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_6341856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341856 prefixEnd_6341856 := by exact prefixLift 6341856
  have htrace : WordTrace (prefixWord ++ tailWord_6341856) baseStart_6341856 baseEnd_6341856 := by
    simpa [prefixWord, tailWord_6341856, baseEnd_6341856] using wordTrace_append hprefix tailTrace_6341856
  have hstable : (prefixWord ++ tailWord_6341856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341856).length < 2 ^ (prefixWord ++ tailWord_6341856).sum := by decide
  have hdescent : baseEnd_6341856 < baseStart_6341856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341937 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_6341937 : Nat := 118140960795 + 6341937 * 2 ^ 59
def prefixEnd_6341937 : Nat := 4983230072969 + 3 ^ 40 * 6341937 * 2
def baseEnd_6341937 : Nat := 3256461961533058876021469

theorem tailTrace_6341937 : CollatzResearch.WordTrace tailWord_6341937 prefixEnd_6341937 3256461961533058876021469 := by
  unfold tailWord_6341937
  simp only [CollatzResearch.WordTrace]
  refine ⟨231309445225252840453392065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154206296816835226968928043 231309445225252840453392065)
  ·
    refine ⟨173482083918939630340044049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231309445225252840453392065 173482083918939630340044049)
    ·
      refine ⟨130111562939204722755033037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173482083918939630340044049 130111562939204722755033037)
      ·
        refine ⟨48791836102201771033137389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130111562939204722755033037 48791836102201771033137389)
        ·
          refine ⟨18296938538325664137426521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48791836102201771033137389 18296938538325664137426521)
          ·
            refine ⟨13722703903744248103069891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18296938538325664137426521 13722703903744248103069891)
            ·
              refine ⟨20584055855616372154604837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13722703903744248103069891 20584055855616372154604837)
              ·
                refine ⟨3859510472928069778988407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20584055855616372154604837 3859510472928069778988407)
                ·
                  refine ⟨5789265709392104668482611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859510472928069778988407 5789265709392104668482611)
                  ·
                    refine ⟨8683898564088157002723917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789265709392104668482611 8683898564088157002723917)
                    ·
                      refine ⟨3256461961533058876021469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8683898564088157002723917 3256461961533058876021469)
                      ·
                        rfl

theorem cell23_6341937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_6341937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341937 prefixEnd_6341937 := by exact prefixLift 6341937
  have htrace : WordTrace (prefixWord ++ tailWord_6341937) baseStart_6341937 baseEnd_6341937 := by
    simpa [prefixWord, tailWord_6341937, baseEnd_6341937] using wordTrace_append hprefix tailTrace_6341937
  have hstable : (prefixWord ++ tailWord_6341937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341937).length < 2 ^ (prefixWord ++ tailWord_6341937).sum := by decide
  have hdescent : baseEnd_6341937 < baseStart_6341937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341946 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_6341946 : Nat := 118140960795 + 6341946 * 2 ^ 59
def prefixEnd_6341946 : Nat := 4983230072969 + 3 ^ 40 * 6341946 * 2
def baseEnd_6341946 : Nat := 3256466582858949340808927

theorem tailTrace_6341946 : CollatzResearch.WordTrace tailWord_6341946 prefixEnd_6341946 3256466582858949340808927 := by
  unfold tailWord_6341946
  simp only [CollatzResearch.WordTrace]
  refine ⟨57827443370555058747617423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154206515654813489993646461 57827443370555058747617423)
  ·
    refine ⟨86741165055832588121426135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57827443370555058747617423 86741165055832588121426135)
    ·
      refine ⟨130111747583748882182139203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86741165055832588121426135 130111747583748882182139203)
      ·
        refine ⟨195167621375623323273208805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130111747583748882182139203 195167621375623323273208805)
        ·
          refine ⟨36593929007929373113726651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195167621375623323273208805 36593929007929373113726651)
          ·
            refine ⟨54890893511894059670589977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36593929007929373113726651 54890893511894059670589977)
            ·
              refine ⟨41168170133920544752942483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54890893511894059670589977 41168170133920544752942483)
              ·
                refine ⟨61752255200880817129413725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41168170133920544752942483 61752255200880817129413725)
                ·
                  refine ⟨23157095700330306423530147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61752255200880817129413725 23157095700330306423530147)
                  ·
                    refine ⟨34735643550495459635295221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23157095700330306423530147 34735643550495459635295221)
                    ·
                      refine ⟨3256466582858949340808927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34735643550495459635295221 3256466582858949340808927)
                      ·
                        rfl

theorem cell23_6341946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_6341946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341946 prefixEnd_6341946 := by exact prefixLift 6341946
  have htrace : WordTrace (prefixWord ++ tailWord_6341946) baseStart_6341946 baseEnd_6341946 := by
    simpa [prefixWord, tailWord_6341946, baseEnd_6341946] using wordTrace_append hprefix tailTrace_6341946
  have hstable : (prefixWord ++ tailWord_6341946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341946).length < 2 ^ (prefixWord ++ tailWord_6341946).sum := by decide
  have hdescent : baseEnd_6341946 < baseStart_6341946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341953 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6341953 : Nat := 118140960795 + 6341953 * 2 ^ 59
def prefixEnd_6341953 : Nat := 4983230072969 + 3 ^ 40 * 6341953 * 2
def baseEnd_6341953 : Nat := 1085490059074510271140465

theorem tailTrace_6341953 : CollatzResearch.WordTrace tailWord_6341953 prefixEnd_6341953 1085490059074510271140465 := by
  unfold tailWord_6341953
  simp only [CollatzResearch.WordTrace]
  refine ⟨231310028793194875185974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154206685862129916790649675 231310028793194875185974513)
  ·
    refine ⟨173482521594896156389480885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231310028793194875185974513 173482521594896156389480885)
    ·
      refine ⟨16263986399521514661513833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173482521594896156389480885 16263986399521514661513833)
      ·
        refine ⟨12197989799641135996135375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16263986399521514661513833 12197989799641135996135375)
        ·
          refine ⟨18296984699461703994203063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12197989799641135996135375 18296984699461703994203063)
          ·
            refine ⟨27445477049192555991304595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18296984699461703994203063 27445477049192555991304595)
            ·
              refine ⟨41168215573788833986956893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27445477049192555991304595 41168215573788833986956893)
              ·
                refine ⟨15438080840170812745108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41168215573788833986956893 15438080840170812745108835)
                ·
                  refine ⟨23157121260256219117663253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15438080840170812745108835 23157121260256219117663253)
                  ·
                    refine ⟨1085490059074510271140465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23157121260256219117663253 1085490059074510271140465)
                    ·
                      rfl

theorem cell23_6341953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6341953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341953 prefixEnd_6341953 := by exact prefixLift 6341953
  have htrace : WordTrace (prefixWord ++ tailWord_6341953) baseStart_6341953 baseEnd_6341953 := by
    simpa [prefixWord, tailWord_6341953, baseEnd_6341953] using wordTrace_append hprefix tailTrace_6341953
  have hstable : (prefixWord ++ tailWord_6341953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341953).length < 2 ^ (prefixWord ++ tailWord_6341953).sum := by decide
  have hdescent : baseEnd_6341953 < baseStart_6341953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341973 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6341973 : Nat := 118140960795 + 6341973 * 2 ^ 59
def prefixEnd_6341973 : Nat := 4983230072969 + 3 ^ 40 * 6341973 * 2
def baseEnd_6341973 : Nat := 3256480446836620735171303

theorem tailTrace_6341973 : CollatzResearch.WordTrace tailWord_6341973 prefixEnd_6341973 3256480446836620735171303 := by
  unfold tailWord_6341973
  simp only [CollatzResearch.WordTrace]
  refine ⟨231310758253122418601702573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154207172168748279067801715 231310758253122418601702573)
  ·
    refine ⟨86741534344920906975638465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231310758253122418601702573 86741534344920906975638465)
    ·
      refine ⟨65056150758690680231728849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86741534344920906975638465 65056150758690680231728849)
      ·
        refine ⟨48792113069018010173796637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65056150758690680231728849 48792113069018010173796637)
        ·
          refine ⟨18297042400881753815173739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48792113069018010173796637 18297042400881753815173739)
          ·
            refine ⟨27445563601322630722760609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18297042400881753815173739 27445563601322630722760609)
            ·
              refine ⟨20584172700991973042070457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27445563601322630722760609 20584172700991973042070457)
              ·
                refine ⟨15438129525743979781552843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20584172700991973042070457 15438129525743979781552843)
                ·
                  refine ⟨23157194288615969672329265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15438129525743979781552843 23157194288615969672329265)
                  ·
                    refine ⟨17367895716461977254246949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23157194288615969672329265 17367895716461977254246949)
                    ·
                      refine ⟨3256480446836620735171303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17367895716461977254246949 3256480446836620735171303)
                      ·
                        rfl

theorem cell23_6341973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6341973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341973 prefixEnd_6341973 := by exact prefixLift 6341973
  have htrace : WordTrace (prefixWord ++ tailWord_6341973) baseStart_6341973 baseEnd_6341973 := by
    simpa [prefixWord, tailWord_6341973, baseEnd_6341973] using wordTrace_append hprefix tailTrace_6341973
  have hstable : (prefixWord ++ tailWord_6341973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341973).length < 2 ^ (prefixWord ++ tailWord_6341973).sum := by decide
  have hdescent : baseEnd_6341973 < baseStart_6341973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341977 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 1, 2, 2]
def baseStart_6341977 : Nat := 118140960795 + 6341977 * 2 ^ 59
def prefixEnd_6341977 : Nat := 4983230072969 + 3 ^ 40 * 6341977 * 2
def baseEnd_6341977 : Nat := 3256482500759238719521285

theorem tailTrace_6341977 : CollatzResearch.WordTrace tailWord_6341977 prefixEnd_6341977 3256482500759238719521285 := by
  unfold tailWord_6341977
  simp only [CollatzResearch.WordTrace]
  refine ⟨231310904145107927284848185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154207269430071951523232123 231310904145107927284848185)
  ·
    refine ⟨173483178108830945463636139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231310904145107927284848185 173483178108830945463636139)
    ·
      refine ⟨260224767163246418195454209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173483178108830945463636139 260224767163246418195454209)
      ·
        refine ⟨195168575372434813646590657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260224767163246418195454209 195168575372434813646590657)
        ·
          refine ⟨146376431529326110234942993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195168575372434813646590657 146376431529326110234942993)
          ·
            refine ⟨109782323646994582676207245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146376431529326110234942993 109782323646994582676207245)
            ·
              refine ⟨41168371367622968503577717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109782323646994582676207245 41168371367622968503577717)
              ·
                refine ⟨3859534815714653297210411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41168371367622968503577717 3859534815714653297210411)
                ·
                  refine ⟨5789302223571979945815617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859534815714653297210411 5789302223571979945815617)
                  ·
                    refine ⟨4341976667678984959361713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789302223571979945815617 4341976667678984959361713)
                    ·
                      refine ⟨3256482500759238719521285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341976667678984959361713 3256482500759238719521285)
                      ·
                        rfl

theorem cell23_6341977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_6341977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341977 prefixEnd_6341977 := by exact prefixLift 6341977
  have htrace : WordTrace (prefixWord ++ tailWord_6341977) baseStart_6341977 baseEnd_6341977 := by
    simpa [prefixWord, tailWord_6341977, baseEnd_6341977] using wordTrace_append hprefix tailTrace_6341977
  have hstable : (prefixWord ++ tailWord_6341977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341977).length < 2 ^ (prefixWord ++ tailWord_6341977).sum := by decide
  have hdescent : baseEnd_6341977 < baseStart_6341977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6341994 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6341994 : Nat := 118140960795 + 6341994 * 2 ^ 59
def prefixEnd_6341994 : Nat := 4983230072969 + 3 ^ 40 * 6341994 * 2
def baseEnd_6341994 : Nat := 3256491229930365153008707

theorem tailTrace_6341994 : CollatzResearch.WordTrace tailWord_6341994 prefixEnd_6341994 3256491229930365153008707 := by
  unfold tailWord_6341994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57827881046511584797054259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154207682790697559458811357 57827881046511584797054259)
  ·
    refine ⟨86741821569767377195581389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57827881046511584797054259 86741821569767377195581389)
    ·
      refine ⟨32528183088662766448343021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86741821569767377195581389 32528183088662766448343021)
      ·
        refine ⟨12198068658248537418128633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32528183088662766448343021 12198068658248537418128633)
        ·
          refine ⟨9148551493686403063596475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12198068658248537418128633 9148551493686403063596475)
          ·
            refine ⟨13722827240529604595394713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148551493686403063596475 13722827240529604595394713)
            ·
              refine ⟨10292120430397203446546035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13722827240529604595394713 10292120430397203446546035)
              ·
                refine ⟨15438180645595805169819053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292120430397203446546035 15438180645595805169819053)
                ·
                  refine ⟨5789317742098426938682145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15438180645595805169819053 5789317742098426938682145)
                  ·
                    refine ⟨4341988306573820204011609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789317742098426938682145 4341988306573820204011609)
                    ·
                      refine ⟨3256491229930365153008707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4341988306573820204011609 3256491229930365153008707)
                      ·
                        rfl

theorem cell23_6341994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6341994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6341994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6341994 prefixEnd_6341994 := by exact prefixLift 6341994
  have htrace : WordTrace (prefixWord ++ tailWord_6341994) baseStart_6341994 baseEnd_6341994 := by
    simpa [prefixWord, tailWord_6341994, baseEnd_6341994] using wordTrace_append hprefix tailTrace_6341994
  have hstable : (prefixWord ++ tailWord_6341994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6341994).length < 2 ^ (prefixWord ++ tailWord_6341994).sum := by decide
  have hdescent : baseEnd_6341994 < baseStart_6341994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6341994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342016 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_6342016 : Nat := 118140960795 + 6342016 * 2 ^ 59
def prefixEnd_6342016 : Nat := 4983230072969 + 3 ^ 40 * 6342016 * 2
def baseEnd_6342016 : Nat := 3256502526504764066933605

theorem tailTrace_6342016 : CollatzResearch.WordTrace tailWord_6342016 prefixEnd_6342016 3256502526504764066933605 := by
  unfold tailWord_6342016
  simp only [CollatzResearch.WordTrace]
  refine ⟨115656163295983318472758951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154208217727977757963678601 115656163295983318472758951)
  ·
    refine ⟨173484244943974977709138427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115656163295983318472758951 173484244943974977709138427)
    ·
      refine ⟨260226367415962466563707641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173484244943974977709138427 260226367415962466563707641)
      ·
        refine ⟨195169775561971849922780731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260226367415962466563707641 195169775561971849922780731)
        ·
          refine ⟨292754663342957774884171097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195169775561971849922780731 292754663342957774884171097)
          ·
            refine ⟨219565997507218331163128323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292754663342957774884171097 219565997507218331163128323)
            ·
              refine ⟨329348996260827496744692485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219565997507218331163128323 329348996260827496744692485)
              ·
                refine ⟨61752936798905155639629841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329348996260827496744692485 61752936798905155639629841)
                ·
                  refine ⟨46314702599178866729722381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61752936798905155639629841 46314702599178866729722381)
                  ·
                    refine ⟨17368013474692075023645893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46314702599178866729722381 17368013474692075023645893)
                    ·
                      refine ⟨3256502526504764066933605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17368013474692075023645893 3256502526504764066933605)
                      ·
                        rfl

theorem cell23_6342016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_6342016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342016 prefixEnd_6342016 := by exact prefixLift 6342016
  have htrace : WordTrace (prefixWord ++ tailWord_6342016) baseStart_6342016 baseEnd_6342016 := by
    simpa [prefixWord, tailWord_6342016, baseEnd_6342016] using wordTrace_append hprefix tailTrace_6342016
  have hstable : (prefixWord ++ tailWord_6342016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342016).length < 2 ^ (prefixWord ++ tailWord_6342016).sum := by decide
  have hdescent : baseEnd_6342016 < baseStart_6342016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342017 : List Nat := [1, 2, 4, 3, 3, 1, 2, 7]
def baseStart_6342017 : Nat := 118140960795 + 6342017 * 2 ^ 59
def prefixEnd_6342017 : Nat := 4983230072969 + 3 ^ 40 * 6342017 * 2
def baseEnd_6342017 : Nat := 120611223703163650482263

theorem tailTrace_6342017 : CollatzResearch.WordTrace tailWord_6342017 prefixEnd_6342017 120611223703163650482263 := by
  unfold tailWord_6342017
  simp only [CollatzResearch.WordTrace]
  refine ⟨231312363064963014116304305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154208242043308676077536203 231312363064963014116304305)
  ·
    refine ⟨173484272298722260587228229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231312363064963014116304305 173484272298722260587228229)
    ·
      refine ⟨32528301056010423860105293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173484272298722260587228229 32528301056010423860105293)
      ·
        refine ⟨12198112896003908947539485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32528301056010423860105293 12198112896003908947539485)
        ·
          refine ⟨4574292336001465855327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12198112896003908947539485 4574292336001465855327307)
          ·
            refine ⟨6861438504002198782990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574292336001465855327307 6861438504002198782990961)
            ·
              refine ⟨5146078878001649087243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6861438504002198782990961 5146078878001649087243221)
              ·
                refine ⟨120611223703163650482263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5146078878001649087243221 120611223703163650482263)
                ·
                  rfl

theorem cell23_6342017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 7].length) (baseStart_6342017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342017 prefixEnd_6342017 := by exact prefixLift 6342017
  have htrace : WordTrace (prefixWord ++ tailWord_6342017) baseStart_6342017 baseEnd_6342017 := by
    simpa [prefixWord, tailWord_6342017, baseEnd_6342017] using wordTrace_append hprefix tailTrace_6342017
  have hstable : (prefixWord ++ tailWord_6342017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342017).length < 2 ^ (prefixWord ++ tailWord_6342017).sum := by decide
  have hdescent : baseEnd_6342017 < baseStart_6342017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342061 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6342061 : Nat := 118140960795 + 6342061 * 2 ^ 59
def prefixEnd_6342061 : Nat := 4983230072969 + 3 ^ 40 * 6342061 * 2
def baseEnd_6342061 : Nat := 3256525633134216390870899

theorem tailTrace_6342061 : CollatzResearch.WordTrace tailWord_6342061 prefixEnd_6342061 3256525633134216390870899 := by
  unfold tailWord_6342061
  simp only [CollatzResearch.WordTrace]
  refine ⟨231313967876803609630906037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154209311917869073087270691 231313967876803609630906037)
  ·
    refine ⟨21685684488450338402897441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231313967876803609630906037 21685684488450338402897441)
    ·
      refine ⟨16264263366337753802173081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21685684488450338402897441 16264263366337753802173081)
      ·
        refine ⟨12198197524753315351629811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16264263366337753802173081 12198197524753315351629811)
        ·
          refine ⟨18297296287129973027444717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198197524753315351629811 18297296287129973027444717)
          ·
            refine ⟨6861486107673739885291769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18297296287129973027444717 6861486107673739885291769)
            ·
              refine ⟨5146114580755304913968827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6861486107673739885291769 5146114580755304913968827)
              ·
                refine ⟨7719171871132957370953241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146114580755304913968827 7719171871132957370953241)
                ·
                  refine ⟨5789378903349718028214931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7719171871132957370953241 5789378903349718028214931)
                  ·
                    refine ⟨8684068355024577042322397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789378903349718028214931 8684068355024577042322397)
                    ·
                      refine ⟨3256525633134216390870899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684068355024577042322397 3256525633134216390870899)
                      ·
                        rfl

theorem cell23_6342061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6342061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342061 prefixEnd_6342061 := by exact prefixLift 6342061
  have htrace : WordTrace (prefixWord ++ tailWord_6342061) baseStart_6342061 baseEnd_6342061 := by
    simpa [prefixWord, tailWord_6342061, baseEnd_6342061] using wordTrace_append hprefix tailTrace_6342061
  have hstable : (prefixWord ++ tailWord_6342061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342061).length < 2 ^ (prefixWord ++ tailWord_6342061).sum := by decide
  have hdescent : baseEnd_6342061 < baseStart_6342061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342096 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_6342096 : Nat := 118140960795 + 6342096 * 2 ^ 59
def prefixEnd_6342096 : Nat := 4983230072969 + 3 ^ 40 * 6342096 * 2
def baseEnd_6342096 : Nat := 3256543604957123753933237

theorem tailTrace_6342096 : CollatzResearch.WordTrace tailWord_6342096 prefixEnd_6342096 3256543604957123753933237 := by
  unfold tailWord_6342096
  simp only [CollatzResearch.WordTrace]
  refine ⟨115657622215838405304215071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154210162954451207072286761 115657622215838405304215071)
  ·
    refine ⟨173486433323757607956322607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115657622215838405304215071 173486433323757607956322607)
    ·
      refine ⟨260229649985636411934483911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173486433323757607956322607 260229649985636411934483911)
      ·
        refine ⟨390344474978454617901725867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260229649985636411934483911 390344474978454617901725867)
        ·
          refine ⟨585516712467681926852588801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390344474978454617901725867 585516712467681926852588801)
          ·
            refine ⟨439137534350761445139441601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585516712467681926852588801 439137534350761445139441601)
            ·
              refine ⟨329353150763071083854581201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439137534350761445139441601 329353150763071083854581201)
              ·
                refine ⟨247014863072303312890935901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329353150763071083854581201 247014863072303312890935901)
                ·
                  refine ⟨92630573652113742334100963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247014863072303312890935901 92630573652113742334100963)
                  ·
                    refine ⟨138945860478170613501151445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92630573652113742334100963 138945860478170613501151445)
                    ·
                      refine ⟨3256543604957123753933237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138945860478170613501151445 3256543604957123753933237)
                      ·
                        rfl

theorem cell23_6342096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_6342096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342096 prefixEnd_6342096 := by exact prefixLift 6342096
  have htrace : WordTrace (prefixWord ++ tailWord_6342096) baseStart_6342096 baseEnd_6342096 := by
    simpa [prefixWord, tailWord_6342096, baseEnd_6342096] using wordTrace_append hprefix tailTrace_6342096
  have hstable : (prefixWord ++ tailWord_6342096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342096).length < 2 ^ (prefixWord ++ tailWord_6342096).sum := by decide
  have hdescent : baseEnd_6342096 < baseStart_6342096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342113 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_6342113 : Nat := 118140960795 + 6342113 * 2 ^ 59
def prefixEnd_6342113 : Nat := 4983230072969 + 3 ^ 40 * 6342113 * 2
def baseEnd_6342113 : Nat := 3256552334128250187420659

theorem tailTrace_6342113 : CollatzResearch.WordTrace tailWord_6342113 prefixEnd_6342113 3256552334128250187420659 := by
  unfold tailWord_6342113
  simp only [CollatzResearch.WordTrace]
  refine ⟨231315864472615222511798993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154210576315076815007865995 231315864472615222511798993)
  ·
    refine ⟨173486898354461416883849245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231315864472615222511798993 173486898354461416883849245)
    ·
      refine ⟨65057586882923031331443467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173486898354461416883849245 65057586882923031331443467)
      ·
        refine ⟨97586380324384546997165201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65057586882923031331443467 97586380324384546997165201)
        ·
          refine ⟨73189785243288410247873901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97586380324384546997165201 73189785243288410247873901)
          ·
            refine ⟨27446169466233153842952713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73189785243288410247873901 27446169466233153842952713)
            ·
              refine ⟨20584627099674865382214535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27446169466233153842952713 20584627099674865382214535)
              ·
                refine ⟨30876940649512298073321803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20584627099674865382214535 30876940649512298073321803)
                ·
                  refine ⟨46315410974268447109982705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30876940649512298073321803 46315410974268447109982705)
                  ·
                    refine ⟨34736558230701335332487029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46315410974268447109982705 34736558230701335332487029)
                    ·
                      refine ⟨3256552334128250187420659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34736558230701335332487029 3256552334128250187420659)
                      ·
                        rfl

theorem cell23_6342113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_6342113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342113 prefixEnd_6342113 := by exact prefixLift 6342113
  have htrace : WordTrace (prefixWord ++ tailWord_6342113) baseStart_6342113 baseEnd_6342113 := by
    simpa [prefixWord, tailWord_6342113, baseEnd_6342113] using wordTrace_append hprefix tailTrace_6342113
  have hstable : (prefixWord ++ tailWord_6342113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342113).length < 2 ^ (prefixWord ++ tailWord_6342113).sum := by decide
  have hdescent : baseEnd_6342113 < baseStart_6342113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342140 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_6342140 : Nat := 118140960795 + 6342140 * 2 ^ 59
def prefixEnd_6342140 : Nat := 4983230072969 + 3 ^ 40 * 6342140 * 2
def baseEnd_6342140 : Nat := 3256566198105921581783035

theorem tailTrace_6342140 : CollatzResearch.WordTrace tailWord_6342140 prefixEnd_6342140 3256566198105921581783035 := by
  unfold tailWord_6342140
  simp only [CollatzResearch.WordTrace]
  refine ⟨115658424621758703061515937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154211232829011604082021249 115658424621758703061515937)
  ·
    refine ⟨86743818466319027296136953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115658424621758703061515937 86743818466319027296136953)
    ·
      refine ⟨65057863849739270472102715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86743818466319027296136953 65057863849739270472102715)
      ·
        refine ⟨97586795774608905708154073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65057863849739270472102715 97586795774608905708154073)
        ·
          refine ⟨73190096830956679281115555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97586795774608905708154073 73190096830956679281115555)
          ·
            refine ⟨109785145246435018921673333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73190096830956679281115555 109785145246435018921673333)
            ·
              refine ⟨10292357366853283023906875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109785145246435018921673333 10292357366853283023906875)
              ·
                refine ⟨15438536050279924535860313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292357366853283023906875 15438536050279924535860313)
                ·
                  refine ⟨11578902037709943401895235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15438536050279924535860313 11578902037709943401895235)
                  ·
                    refine ⟨17368353056564915102842853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11578902037709943401895235 17368353056564915102842853)
                    ·
                      refine ⟨3256566198105921581783035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17368353056564915102842853 3256566198105921581783035)
                      ·
                        rfl

theorem cell23_6342140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_6342140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342140 prefixEnd_6342140 := by exact prefixLift 6342140
  have htrace : WordTrace (prefixWord ++ tailWord_6342140) baseStart_6342140 baseEnd_6342140 := by
    simpa [prefixWord, tailWord_6342140, baseEnd_6342140] using wordTrace_append hprefix tailTrace_6342140
  have hstable : (prefixWord ++ tailWord_6342140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342140).length < 2 ^ (prefixWord ++ tailWord_6342140).sum := by decide
  have hdescent : baseEnd_6342140 < baseStart_6342140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342163 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 8]
def baseStart_6342163 : Nat := 118140960795 + 6342163 * 2 ^ 59
def prefixEnd_6342163 : Nat := 4983230072969 + 3 ^ 40 * 6342163 * 2
def baseEnd_6342163 : Nat := 361842000906774999088381

theorem tailTrace_6342163 : CollatzResearch.WordTrace tailWord_6342163 prefixEnd_6342163 361842000906774999088381 := by
  unfold tailWord_6342163
  simp only [CollatzResearch.WordTrace]
  refine ⟨231317688122434081051119143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154211792081622720700746095 231317688122434081051119143)
  ·
    refine ⟨346976532183651121576678715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231317688122434081051119143 346976532183651121576678715)
    ·
      refine ⟨520464798275476682365018073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346976532183651121576678715 520464798275476682365018073)
      ·
        refine ⟨390348598706607511773763555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520464798275476682365018073 390348598706607511773763555)
        ·
          refine ⟨585522898059911267660645333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390348598706607511773763555 585522898059911267660645333)
          ·
            refine ⟨13723192923279170335796375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 585522898059911267660645333 13723192923279170335796375)
            ·
              refine ⟨20584789384918755503694563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13723192923279170335796375 20584789384918755503694563)
              ·
                refine ⟨30877184077378133255541845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20584789384918755503694563 30877184077378133255541845)
                ·
                  refine ⟨361842000906774999088381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30877184077378133255541845 361842000906774999088381)
                  ·
                    rfl

theorem cell23_6342163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 8].length) (baseStart_6342163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342163 prefixEnd_6342163 := by exact prefixLift 6342163
  have htrace : WordTrace (prefixWord ++ tailWord_6342163) baseStart_6342163 baseEnd_6342163 := by
    simpa [prefixWord, tailWord_6342163, baseEnd_6342163] using wordTrace_append hprefix tailTrace_6342163
  have hstable : (prefixWord ++ tailWord_6342163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342163).length < 2 ^ (prefixWord ++ tailWord_6342163).sum := by decide
  have hdescent : baseEnd_6342163 < baseStart_6342163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342247 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_6342247 : Nat := 118140960795 + 6342247 * 2 ^ 59
def prefixEnd_6342247 : Nat := 4983230072969 + 3 ^ 40 * 6342247 * 2
def baseEnd_6342247 : Nat := 3256621140535952663145043

theorem tailTrace_6342247 : CollatzResearch.WordTrace tailWord_6342247 prefixEnd_6342247 3256621140535952663145043 := by
  unfold tailWord_6342247
  simp only [CollatzResearch.WordTrace]
  refine ⟨231320751854129763397176995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154213834569419842264784663 231320751854129763397176995)
  ·
    refine ⟨346981127781194645095765493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231320751854129763397176995 346981127781194645095765493)
    ·
      refine ⟨32529480729486997977728015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 346981127781194645095765493 32529480729486997977728015)
      ·
        refine ⟨48794221094230496966592023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32529480729486997977728015 48794221094230496966592023)
        ·
          refine ⟨73191331641345745449888035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48794221094230496966592023 73191331641345745449888035)
          ·
            refine ⟨109786997462018618174832053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73191331641345745449888035 109786997462018618174832053)
            ·
              refine ⟨10292531012064245453890505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109786997462018618174832053 10292531012064245453890505)
              ·
                refine ⟨7719398259048184090417879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10292531012064245453890505 7719398259048184090417879)
                ·
                  refine ⟨11579097388572276135626819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7719398259048184090417879 11579097388572276135626819)
                  ·
                    refine ⟨17368646082858414203440229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11579097388572276135626819 17368646082858414203440229)
                    ·
                      refine ⟨3256621140535952663145043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17368646082858414203440229 3256621140535952663145043)
                      ·
                        rfl

theorem cell23_6342247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_6342247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342247 prefixEnd_6342247 := by exact prefixLift 6342247
  have htrace : WordTrace (prefixWord ++ tailWord_6342247) baseStart_6342247 baseEnd_6342247 := by
    simpa [prefixWord, tailWord_6342247, baseEnd_6342247] using wordTrace_append hprefix tailTrace_6342247
  have hstable : (prefixWord ++ tailWord_6342247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342247).length < 2 ^ (prefixWord ++ tailWord_6342247).sum := by decide
  have hdescent : baseEnd_6342247 < baseStart_6342247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342283 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 9]
def baseStart_6342283 : Nat := 118140960795 + 6342283 * 2 ^ 59
def prefixEnd_6342283 : Nat := 4983230072969 + 3 ^ 40 * 6342283 * 2
def baseEnd_6342283 : Nat := 1085546541946504840764959

theorem tailTrace_6342283 : CollatzResearch.WordTrace tailWord_6342283 prefixEnd_6342283 1085546541946504840764959 := by
  unfold tailWord_6342283
  simp only [CollatzResearch.WordTrace]
  refine ⟨231322064881999341545487503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154214709921332894363658335 231322064881999341545487503)
  ·
    refine ⟨346983097322999012318231255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231322064881999341545487503 346983097322999012318231255)
    ·
      refine ⟨520474645984498518477346883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346983097322999012318231255 520474645984498518477346883)
      ·
        refine ⟨780711968976747777716020325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520474645984498518477346883 780711968976747777716020325)
        ·
          refine ⟨146383494183140208321753811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 780711968976747777716020325 146383494183140208321753811)
          ·
            refine ⟨219575241274710312482630717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146383494183140208321753811 219575241274710312482630717)
            ·
              refine ⟨82340715478016367180986519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219575241274710312482630717 82340715478016367180986519)
              ·
                refine ⟨123511073217024550771479779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82340715478016367180986519 123511073217024550771479779)
                ·
                  refine ⟨185266609825536826157219669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123511073217024550771479779 185266609825536826157219669)
                  ·
                    refine ⟨1085546541946504840764959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 185266609825536826157219669 1085546541946504840764959)
                    ·
                      rfl

theorem cell23_6342283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_6342283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342283 prefixEnd_6342283 := by exact prefixLift 6342283
  have htrace : WordTrace (prefixWord ++ tailWord_6342283) baseStart_6342283 baseEnd_6342283 := by
    simpa [prefixWord, tailWord_6342283, baseEnd_6342283] using wordTrace_append hprefix tailTrace_6342283
  have hstable : (prefixWord ++ tailWord_6342283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342283).length < 2 ^ (prefixWord ++ tailWord_6342283).sum := by decide
  have hdescent : baseEnd_6342283 < baseStart_6342283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342307 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 3, 3, 2]
def baseStart_6342307 : Nat := 118140960795 + 6342307 * 2 ^ 59
def prefixEnd_6342307 : Nat := 4983230072969 + 3 ^ 40 * 6342307 * 2
def baseEnd_6342307 : Nat := 3256651949375222428394767

theorem tailTrace_6342307 : CollatzResearch.WordTrace tailWord_6342307 prefixEnd_6342307 3256651949375222428394767 := by
  unfold tailWord_6342307
  simp only [CollatzResearch.WordTrace]
  refine ⟨231322940233912393644361175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154215293489274929096240783 231322940233912393644361175)
  ·
    refine ⟨346984410350868590466541763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231322940233912393644361175 346984410350868590466541763)
    ·
      refine ⟨520476615526302885699812645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346984410350868590466541763 520476615526302885699812645)
      ·
        refine ⟨97589365411181791068714871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 520476615526302885699812645 97589365411181791068714871)
        ·
          refine ⟨146384048116772686603072307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97589365411181791068714871 146384048116772686603072307)
          ·
            refine ⟨219576072175159029904608461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146384048116772686603072307 219576072175159029904608461)
            ·
              refine ⟨82341027065684636214228173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219576072175159029904608461 82341027065684636214228173)
              ·
                refine ⟨30877885149631738580335565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82341027065684636214228173 30877885149631738580335565)
                ·
                  refine ⟨11579206931111901967625837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30877885149631738580335565 11579206931111901967625837)
                  ·
                    refine ⟨4342202599166963237859689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11579206931111901967625837 4342202599166963237859689)
                    ·
                      refine ⟨3256651949375222428394767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342202599166963237859689 3256651949375222428394767)
                      ·
                        rfl

theorem cell23_6342307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_6342307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342307 prefixEnd_6342307 := by exact prefixLift 6342307
  have htrace : WordTrace (prefixWord ++ tailWord_6342307) baseStart_6342307 baseEnd_6342307 := by
    simpa [prefixWord, tailWord_6342307, baseEnd_6342307] using wordTrace_append hprefix tailTrace_6342307
  have hstable : (prefixWord ++ tailWord_6342307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342307).length < 2 ^ (prefixWord ++ tailWord_6342307).sum := by decide
  have hdescent : baseEnd_6342307 < baseStart_6342307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342330 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_6342330 : Nat := 118140960795 + 6342330 * 2 ^ 59
def prefixEnd_6342330 : Nat := 4983230072969 + 3 ^ 40 * 6342330 * 2
def baseEnd_6342330 : Nat := 1085554586476758612802387

theorem tailTrace_6342330 : CollatzResearch.WordTrace tailWord_6342330 prefixEnd_6342330 1085554586476758612802387 := by
  unfold tailWord_6342330
  simp only [CollatzResearch.WordTrace]
  refine ⟨57830944778207267143112111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154215852741886045714965629 57830944778207267143112111)
  ·
    refine ⟨86746417167310900714668167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57830944778207267143112111 86746417167310900714668167)
    ·
      refine ⟨130119625750966351072002251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86746417167310900714668167 130119625750966351072002251)
      ·
        refine ⟨195179438626449526608003377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130119625750966351072002251 195179438626449526608003377)
        ·
          refine ⟨146384578969837144956002533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195179438626449526608003377 146384578969837144956002533)
          ·
            refine ⟨27447108556844464679250475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146384578969837144956002533 27447108556844464679250475)
            ·
              refine ⟨41170662835266697018875713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27447108556844464679250475 41170662835266697018875713)
              ·
                refine ⟨30877997126450022764156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41170662835266697018875713 30877997126450022764156785)
                ·
                  refine ⟨23158497844837517073117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30877997126450022764156785 23158497844837517073117589)
                  ·
                    refine ⟨1085554586476758612802387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23158497844837517073117589 1085554586476758612802387)
                    ·
                      rfl

theorem cell23_6342330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_6342330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342330 prefixEnd_6342330 := by exact prefixLift 6342330
  have htrace : WordTrace (prefixWord ++ tailWord_6342330) baseStart_6342330 baseEnd_6342330 := by
    simpa [prefixWord, tailWord_6342330, baseEnd_6342330] using wordTrace_append hprefix tailTrace_6342330
  have hstable : (prefixWord ++ tailWord_6342330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342330).length < 2 ^ (prefixWord ++ tailWord_6342330).sum := by decide
  have hdescent : baseEnd_6342330 < baseStart_6342330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342348 : List Nat := [2, 2, 1, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6342348 : Nat := 118140960795 + 6342348 * 2 ^ 59
def prefixEnd_6342348 : Nat := 4983230072969 + 3 ^ 40 * 6342348 * 2
def baseEnd_6342348 : Nat := 3256673002082056767982079

theorem tailTrace_6342348 : CollatzResearch.WordTrace tailWord_6342348 prefixEnd_6342348 3256673002082056767982079 := by
  unfold tailWord_6342348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115662217813381928823301849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154216290417842571764402465 115662217813381928823301849)
  ·
    refine ⟨86746663360036446617476387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115662217813381928823301849 86746663360036446617476387)
    ·
      refine ⟨130119995040054669926214581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86746663360036446617476387 130119995040054669926214581)
      ·
        refine ⟨12198749535005125305582617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130119995040054669926214581 12198749535005125305582617)
        ·
          refine ⟨9149062151253843979186963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12198749535005125305582617 9149062151253843979186963)
          ·
            refine ⟨13723593226880765968780445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149062151253843979186963 13723593226880765968780445)
            ·
              refine ⟨5146347460080287238292667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13723593226880765968780445 5146347460080287238292667)
              ·
                refine ⟨7719521190120430857439001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146347460080287238292667 7719521190120430857439001)
                ·
                  refine ⟨5789640892590323143079251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7719521190120430857439001 5789640892590323143079251)
                  ·
                    refine ⟨8684461338885484714618877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789640892590323143079251 8684461338885484714618877)
                    ·
                      refine ⟨3256673002082056767982079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684461338885484714618877 3256673002082056767982079)
                      ·
                        rfl

theorem cell23_6342348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6342348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342348 prefixEnd_6342348 := by exact prefixLift 6342348
  have htrace : WordTrace (prefixWord ++ tailWord_6342348) baseStart_6342348 baseEnd_6342348 := by
    simpa [prefixWord, tailWord_6342348, baseEnd_6342348] using wordTrace_append hprefix tailTrace_6342348
  have hstable : (prefixWord ++ tailWord_6342348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342348).length < 2 ^ (prefixWord ++ tailWord_6342348).sum := by decide
  have hdescent : baseEnd_6342348 < baseStart_6342348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342360 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 7]
def baseStart_6342360 : Nat := 118140960795 + 6342360 * 2 ^ 59
def prefixEnd_6342360 : Nat := 4983230072969 + 3 ^ 40 * 6342360 * 2
def baseEnd_6342360 : Nat := 361853240427767857892447

theorem tailTrace_6342360 : CollatzResearch.WordTrace tailWord_6342360 prefixEnd_6342360 361853240427767857892447 := by
  unfold tailWord_6342360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115662436651360191848020267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154216582201813589130693689 115662436651360191848020267)
  ·
    refine ⟨173493654977040287772030401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115662436651360191848020267 173493654977040287772030401)
    ·
      refine ⟨130120241232780215829022801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173493654977040287772030401 130120241232780215829022801)
      ·
        refine ⟨97590180924585161871767101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130120241232780215829022801 97590180924585161871767101)
        ·
          refine ⟨36596317846719435701912663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97590180924585161871767101 36596317846719435701912663)
          ·
            refine ⟨54894476770079153552868995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36596317846719435701912663 54894476770079153552868995)
            ·
              refine ⟨82341715155118730329303493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54894476770079153552868995 82341715155118730329303493)
              ·
                refine ⟨15439071591584761936744405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82341715155118730329303493 15439071591584761936744405)
                ·
                  refine ⟨361853240427767857892447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15439071591584761936744405 361853240427767857892447)
                  ·
                    rfl

theorem cell23_6342360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_6342360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342360 prefixEnd_6342360 := by exact prefixLift 6342360
  have htrace : WordTrace (prefixWord ++ tailWord_6342360) baseStart_6342360 baseEnd_6342360 := by
    simpa [prefixWord, tailWord_6342360, baseEnd_6342360] using wordTrace_append hprefix tailTrace_6342360
  have hstable : (prefixWord ++ tailWord_6342360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342360).length < 2 ^ (prefixWord ++ tailWord_6342360).sum := by decide
  have hdescent : baseEnd_6342360 < baseStart_6342360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342400 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_6342400 : Nat := 118140960795 + 6342400 * 2 ^ 59
def prefixEnd_6342400 : Nat := 4983230072969 + 3 ^ 40 * 6342400 * 2
def baseEnd_6342400 : Nat := 3256699703076090564531839

theorem tailTrace_6342400 : CollatzResearch.WordTrace tailWord_6342400 prefixEnd_6342400 3256699703076090564531839 := by
  unfold tailWord_6342400
  simp only [CollatzResearch.WordTrace]
  refine ⟨115663166111287735263748327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154217554815050313684997769 115663166111287735263748327)
  ·
    refine ⟨173494749166931602895622491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115663166111287735263748327 173494749166931602895622491)
    ·
      refine ⟨260242123750397404343433737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173494749166931602895622491 260242123750397404343433737)
      ·
        refine ⟨195181592812798053257575303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260242123750397404343433737 195181592812798053257575303)
        ·
          refine ⟨292772389219197079886362955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195181592812798053257575303 292772389219197079886362955)
          ·
            refine ⟨439158583828795619829544433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292772389219197079886362955 439158583828795619829544433)
            ·
              refine ⟨329368937871596714872158325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439158583828795619829544433 329368937871596714872158325)
              ·
                refine ⟨30878337925462192019264843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329368937871596714872158325 30878337925462192019264843)
                ·
                  refine ⟨46317506888193288028897265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30878337925462192019264843 46317506888193288028897265)
                  ·
                    refine ⟨34738130166144966021672949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46317506888193288028897265 34738130166144966021672949)
                    ·
                      refine ⟨3256699703076090564531839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34738130166144966021672949 3256699703076090564531839)
                      ·
                        rfl

theorem cell23_6342400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_6342400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342400 prefixEnd_6342400 := by exact prefixLift 6342400
  have htrace : WordTrace (prefixWord ++ tailWord_6342400) baseStart_6342400 baseEnd_6342400 := by
    simpa [prefixWord, tailWord_6342400, baseEnd_6342400] using wordTrace_append hprefix tailTrace_6342400
  have hstable : (prefixWord ++ tailWord_6342400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342400).length < 2 ^ (prefixWord ++ tailWord_6342400).sum := by decide
  have hdescent : baseEnd_6342400 < baseStart_6342400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342427 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 6, 2]
def baseStart_6342427 : Nat := 118140960795 + 6342427 * 2 ^ 59
def prefixEnd_6342427 : Nat := 4983230072969 + 3 ^ 40 * 6342427 * 2
def baseEnd_6342427 : Nat := 3256713567053761958894215

theorem tailTrace_6342427 : CollatzResearch.WordTrace tailWord_6342427 prefixEnd_6342427 3256713567053761958894215 := by
  unfold tailWord_6342427
  simp only [CollatzResearch.WordTrace]
  refine ⟨231327316993477654138729535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154218211328985102759153023 231327316993477654138729535)
  ·
    refine ⟨346990975490216481208094303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231327316993477654138729535 346990975490216481208094303)
    ·
      refine ⟨520486463235324721812141455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346990975490216481208094303 520486463235324721812141455)
      ·
        refine ⟨780729694852987082718212183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520486463235324721812141455 780729694852987082718212183)
        ·
          refine ⟨1171094542279480624077318275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780729694852987082718212183 1171094542279480624077318275)
          ·
            refine ⟨1756641813419220936115977413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171094542279480624077318275 1756641813419220936115977413)
            ·
              refine ⟨329370340016103925521745765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1756641813419220936115977413 329370340016103925521745765)
              ·
                refine ⟨61756938753019486035327331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329370340016103925521745765 61756938753019486035327331)
                ·
                  refine ⟨92635408129529229052990997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61756938753019486035327331 92635408129529229052990997)
                  ·
                    refine ⟨4342284756071682611858953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92635408129529229052990997 4342284756071682611858953)
                    ·
                      refine ⟨3256713567053761958894215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342284756071682611858953 3256713567053761958894215)
                      ·
                        rfl

theorem cell23_6342427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 6, 2].length) (baseStart_6342427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342427 prefixEnd_6342427 := by exact prefixLift 6342427
  have htrace : WordTrace (prefixWord ++ tailWord_6342427) baseStart_6342427 baseEnd_6342427 := by
    simpa [prefixWord, tailWord_6342427, baseEnd_6342427] using wordTrace_append hprefix tailTrace_6342427
  have hstable : (prefixWord ++ tailWord_6342427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342427).length < 2 ^ (prefixWord ++ tailWord_6342427).sum := by decide
  have hdescent : baseEnd_6342427 < baseStart_6342427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342461 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_6342461 : Nat := 118140960795 + 6342461 * 2 ^ 59
def prefixEnd_6342461 : Nat := 4983230072969 + 3 ^ 40 * 6342461 * 2
def baseEnd_6342461 : Nat := 3256731025396014825869059

theorem tailTrace_6342461 : CollatzResearch.WordTrace tailWord_6342461 prefixEnd_6342461 3256731025396014825869059 := by
  unfold tailWord_6342461
  simp only [CollatzResearch.WordTrace]
  refine ⟨231328557075354477945467237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154219038050236318630311491 231328557075354477945467237)
  ·
    refine ⟨43374104451628964614775107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231328557075354477945467237 43374104451628964614775107)
    ·
      refine ⟨65061156677443446922162661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43374104451628964614775107 65061156677443446922162661)
      ·
        refine ⟨12198966877020646297905499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65061156677443446922162661 12198966877020646297905499)
        ·
          refine ⟨18298450315530969446858249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198966877020646297905499 18298450315530969446858249)
          ·
            refine ⟨13723837736648227085143687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18298450315530969446858249 13723837736648227085143687)
            ·
              refine ⟨20585756604972340627715531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13723837736648227085143687 20585756604972340627715531)
              ·
                refine ⟨30878634907458510941573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20585756604972340627715531 30878634907458510941573297)
                ·
                  refine ⟨23158976180593883206179973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30878634907458510941573297 23158976180593883206179973)
                  ·
                    refine ⟨4342308033861353101158745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23158976180593883206179973 4342308033861353101158745)
                    ·
                      refine ⟨3256731025396014825869059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342308033861353101158745 3256731025396014825869059)
                      ·
                        rfl

theorem cell23_6342461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_6342461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342461 prefixEnd_6342461 := by exact prefixLift 6342461
  have htrace : WordTrace (prefixWord ++ tailWord_6342461) baseStart_6342461 baseEnd_6342461 := by
    simpa [prefixWord, tailWord_6342461, baseEnd_6342461] using wordTrace_append hprefix tailTrace_6342461
  have hstable : (prefixWord ++ tailWord_6342461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342461).length < 2 ^ (prefixWord ++ tailWord_6342461).sum := by decide
  have hdescent : baseEnd_6342461 < baseStart_6342461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342467 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 6]
def baseStart_6342467 : Nat := 118140960795 + 6342467 * 2 ^ 59
def prefixEnd_6342467 : Nat := 4983230072969 + 3 ^ 40 * 6342467 * 2
def baseEnd_6342467 : Nat := 361859345142215755821559

theorem tailTrace_6342467 : CollatzResearch.WordTrace tailWord_6342467 prefixEnd_6342467 361859345142215755821559 := by
  unfold tailWord_6342467
  simp only [CollatzResearch.WordTrace]
  refine ⟨231328775913332740970185655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154219183942221827313457103 231328775913332740970185655)
  ·
    refine ⟨346993163869999111455278483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231328775913332740970185655 346993163869999111455278483)
    ·
      refine ⟨520489745804998667182917725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346993163869999111455278483 520489745804998667182917725)
      ·
        refine ⟨195183654676874500193594147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520489745804998667182917725 195183654676874500193594147)
        ·
          refine ⟨292775482015311750290391221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195183654676874500193594147 292775482015311750290391221)
          ·
            refine ⟨27447701438935476589724177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292775482015311750290391221 27447701438935476589724177)
            ·
              refine ⟨20585776079201607442293133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27447701438935476589724177 20585776079201607442293133)
              ·
                refine ⟨7719666029700602790859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20585776079201607442293133 7719666029700602790859925)
                ·
                  refine ⟨361859345142215755821559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7719666029700602790859925 361859345142215755821559)
                  ·
                    rfl

theorem cell23_6342467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 6].length) (baseStart_6342467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342467 prefixEnd_6342467 := by exact prefixLift 6342467
  have htrace : WordTrace (prefixWord ++ tailWord_6342467) baseStart_6342467 baseEnd_6342467 := by
    simpa [prefixWord, tailWord_6342467, baseEnd_6342467] using wordTrace_append hprefix tailTrace_6342467
  have hstable : (prefixWord ++ tailWord_6342467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342467).length < 2 ^ (prefixWord ++ tailWord_6342467).sum := by decide
  have hdescent : baseEnd_6342467 < baseStart_6342467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342481 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_6342481 : Nat := 118140960795 + 6342481 * 2 ^ 59
def prefixEnd_6342481 : Nat := 4983230072969 + 3 ^ 40 * 6342481 * 2
def baseEnd_6342481 : Nat := 3256741295009104747618967

theorem tailTrace_6342481 : CollatzResearch.WordTrace tailWord_6342481 prefixEnd_6342481 3256741295009104747618967 := by
  unfold tailWord_6342481
  simp only [CollatzResearch.WordTrace]
  refine ⟨231329286535282021361195297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154219524356854680907463531 231329286535282021361195297)
  ·
    refine ⟨173496964901461516020896473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231329286535282021361195297 173496964901461516020896473)
    ·
      refine ⟨130122723676096137015672355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173496964901461516020896473 130122723676096137015672355)
      ·
        refine ⟨195184085514144205523508533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130122723676096137015672355 195184085514144205523508533)
        ·
          refine ⟨18298508016951019267828925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195184085514144205523508533 18298508016951019267828925)
          ·
            refine ⟨6861940506356632225435847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18298508016951019267828925 6861940506356632225435847)
            ·
              refine ⟨10292910759534948338153771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861940506356632225435847 10292910759534948338153771)
              ·
                refine ⟨15439366139302422507230657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292910759534948338153771 15439366139302422507230657)
                ·
                  refine ⟨11579524604476816880422993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15439366139302422507230657 11579524604476816880422993)
                  ·
                    refine ⟨8684643453357612660317245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11579524604476816880422993 8684643453357612660317245)
                    ·
                      refine ⟨3256741295009104747618967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684643453357612660317245 3256741295009104747618967)
                      ·
                        rfl

theorem cell23_6342481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_6342481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342481 prefixEnd_6342481 := by exact prefixLift 6342481
  have htrace : WordTrace (prefixWord ++ tailWord_6342481) baseStart_6342481 baseEnd_6342481 := by
    simpa [prefixWord, tailWord_6342481, baseEnd_6342481] using wordTrace_append hprefix tailTrace_6342481
  have hstable : (prefixWord ++ tailWord_6342481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342481).length < 2 ^ (prefixWord ++ tailWord_6342481).sum := by decide
  have hdescent : baseEnd_6342481 < baseStart_6342481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342518 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_6342518 : Nat := 118140960795 + 6342518 * 2 ^ 59
def prefixEnd_6342518 : Nat := 4983230072969 + 3 ^ 40 * 6342518 * 2
def baseEnd_6342518 : Nat := 361862254865924566984033

theorem tailTrace_6342518 : CollatzResearch.WordTrace tailWord_6342518 prefixEnd_6342518 361862254865924566984033 := by
  unfold tailWord_6342518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458164752259248542518263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154220424024098651120194805 14458164752259248542518263)
  ·
    refine ⟨21687247128388872813777395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14458164752259248542518263 21687247128388872813777395)
    ·
      refine ⟨32530870692583309220666093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21687247128388872813777395 32530870692583309220666093)
      ·
        refine ⟨12199076509718740957749785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32530870692583309220666093 12199076509718740957749785)
        ·
          refine ⟨9149307382289055718312339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12199076509718740957749785 9149307382289055718312339)
          ·
            refine ⟨13723961073433583577468509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149307382289055718312339 13723961073433583577468509)
            ·
              refine ⟨5146485402537593841550691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13723961073433583577468509 5146485402537593841550691)
              ·
                refine ⟨7719728103806390762326037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146485402537593841550691 7719728103806390762326037)
                ·
                  refine ⟨361862254865924566984033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7719728103806390762326037 361862254865924566984033)
                  ·
                    rfl

theorem cell23_6342518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_6342518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342518 prefixEnd_6342518 := by exact prefixLift 6342518
  have htrace : WordTrace (prefixWord ++ tailWord_6342518) baseStart_6342518 baseEnd_6342518 := by
    simpa [prefixWord, tailWord_6342518, baseEnd_6342518] using wordTrace_append hprefix tailTrace_6342518
  have hstable : (prefixWord ++ tailWord_6342518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342518).length < 2 ^ (prefixWord ++ tailWord_6342518).sum := by decide
  have hdescent : baseEnd_6342518 < baseStart_6342518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342537 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_6342537 : Nat := 118140960795 + 6342537 * 2 ^ 59
def prefixEnd_6342537 : Nat := 4983230072969 + 3 ^ 40 * 6342537 * 2
def baseEnd_6342537 : Nat := 3256770049925756528518709

theorem tailTrace_6342537 : CollatzResearch.WordTrace tailWord_6342537 prefixEnd_6342537 3256770049925756528518709 := by
  unfold tailWord_6342537
  simp only [CollatzResearch.WordTrace]
  refine ⟨231331329023079142925233865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154220886015386095283489243 231331329023079142925233865)
  ·
    refine ⟨173498496767309357193925399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231331329023079142925233865 173498496767309357193925399)
    ·
      refine ⟨260247745150964035790888099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173498496767309357193925399 260247745150964035790888099)
      ·
        refine ⟨390371617726446053686332149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260247745150964035790888099 390371617726446053686332149)
        ·
          refine ⟨36597339161854317533093639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390371617726446053686332149 36597339161854317533093639)
          ·
            refine ⟨54896008742781476299640459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36597339161854317533093639 54896008742781476299640459)
            ·
              refine ⟨82344013114172214449460689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54896008742781476299640459 82344013114172214449460689)
              ·
                refine ⟨61758009835629160837095517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82344013114172214449460689 61758009835629160837095517)
                ·
                  refine ⟨23159253688360935313910819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61758009835629160837095517 23159253688360935313910819)
                  ·
                    refine ⟨34738880532541402970866229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23159253688360935313910819 34738880532541402970866229)
                    ·
                      refine ⟨3256770049925756528518709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34738880532541402970866229 3256770049925756528518709)
                      ·
                        rfl

theorem cell23_6342537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_6342537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342537 prefixEnd_6342537 := by exact prefixLift 6342537
  have htrace : WordTrace (prefixWord ++ tailWord_6342537) baseStart_6342537 baseEnd_6342537 := by
    simpa [prefixWord, tailWord_6342537, baseEnd_6342537] using wordTrace_append hprefix tailTrace_6342537
  have hstable : (prefixWord ++ tailWord_6342537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342537).length < 2 ^ (prefixWord ++ tailWord_6342537).sum := by decide
  have hdescent : baseEnd_6342537 < baseStart_6342537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342554 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6342554 : Nat := 118140960795 + 6342554 * 2 ^ 59
def prefixEnd_6342554 : Nat := 4983230072969 + 3 ^ 40 * 6342554 * 2
def baseEnd_6342554 : Nat := 3256778779096882962006131

theorem tailTrace_6342554 : CollatzResearch.WordTrace tailWord_6342554 prefixEnd_6342554 3256778779096882962006131 := by
  unfold tailWord_6342554
  simp only [CollatzResearch.WordTrace]
  refine ⟨57832987266004388707150679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154221299376011703219068477 57832987266004388707150679)
  ·
    refine ⟨86749480899006583060726019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57832987266004388707150679 86749480899006583060726019)
    ·
      refine ⟨130124221348509874591089029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86749480899006583060726019 130124221348509874591089029)
      ·
        refine ⟨24398291502845601485829193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130124221348509874591089029 24398291502845601485829193)
        ·
          refine ⟨18298718627134201114371895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24398291502845601485829193 18298718627134201114371895)
          ·
            refine ⟨27448077940701301671557843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18298718627134201114371895 27448077940701301671557843)
            ·
              refine ⟨41172116911051952507336765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27448077940701301671557843 41172116911051952507336765)
              ·
                refine ⟨15439543841644482190251287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41172116911051952507336765 15439543841644482190251287)
                ·
                  refine ⟨23159315762466723285376931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15439543841644482190251287 23159315762466723285376931)
                  ·
                    refine ⟨34738973643700084928065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23159315762466723285376931 34738973643700084928065397)
                    ·
                      refine ⟨3256778779096882962006131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34738973643700084928065397 3256778779096882962006131)
                      ·
                        rfl

theorem cell23_6342554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6342554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342554 prefixEnd_6342554 := by exact prefixLift 6342554
  have htrace : WordTrace (prefixWord ++ tailWord_6342554) baseStart_6342554 baseEnd_6342554 := by
    simpa [prefixWord, tailWord_6342554, baseEnd_6342554] using wordTrace_append hprefix tailTrace_6342554
  have hstable : (prefixWord ++ tailWord_6342554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342554).length < 2 ^ (prefixWord ++ tailWord_6342554).sum := by decide
  have hdescent : baseEnd_6342554 < baseStart_6342554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342557 : List Nat := [1, 4, 2, 1, 2, 2, 11]
def baseStart_6342557 : Nat := 118140960795 + 6342557 * 2 ^ 59
def prefixEnd_6342557 : Nat := 4983230072969 + 3 ^ 40 * 6342557 * 2
def baseEnd_6342557 : Nat := 40207164438751190744057

theorem tailTrace_6342557 : CollatzResearch.WordTrace tailWord_6342557 prefixEnd_6342557 40207164438751190744057 := by
  unfold tailWord_6342557
  simp only [CollatzResearch.WordTrace]
  refine ⟨231332058483006686340961925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154221372322004457560641283 231332058483006686340961925)
  ·
    refine ⟨43374760965563753688930361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231332058483006686340961925 43374760965563753688930361)
    ·
      refine ⟨32531070724172815266697771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43374760965563753688930361 32531070724172815266697771)
      ·
        refine ⟨48796606086259222900046657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32531070724172815266697771 48796606086259222900046657)
        ·
          refine ⟨36597454564694417175034993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48796606086259222900046657 36597454564694417175034993)
          ·
            refine ⟨27448090923520812881276245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36597454564694417175034993 27448090923520812881276245)
            ·
              refine ⟨40207164438751190744057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27448090923520812881276245 40207164438751190744057)
              ·
                rfl

theorem cell23_6342557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 11].length) (baseStart_6342557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342557 prefixEnd_6342557 := by exact prefixLift 6342557
  have htrace : WordTrace (prefixWord ++ tailWord_6342557) baseStart_6342557 baseEnd_6342557 := by
    simpa [prefixWord, tailWord_6342557, baseEnd_6342557] using wordTrace_append hprefix tailTrace_6342557
  have hstable : (prefixWord ++ tailWord_6342557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342557).length < 2 ^ (prefixWord ++ tailWord_6342557).sum := by decide
  have hdescent : baseEnd_6342557 < baseStart_6342557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342562 : List Nat := [3, 3, 1, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_6342562 : Nat := 118140960795 + 6342562 * 2 ^ 59
def prefixEnd_6342562 : Nat := 4983230072969 + 3 ^ 40 * 6342562 * 2
def baseEnd_6342562 : Nat := 3256782886942118930706095

theorem tailTrace_6342562 : CollatzResearch.WordTrace tailWord_6342562 prefixEnd_6342562 3256782886942118930706095 := by
  unfold tailWord_6342562
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833060211997143048723485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154221493898659048129929293 57833060211997143048723485)
  ·
    refine ⟨21687397579498928643271307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57833060211997143048723485 21687397579498928643271307)
    ·
      refine ⟨32531096369248392964906961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21687397579498928643271307 32531096369248392964906961)
      ·
        refine ⟨24398322276936294723680221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32531096369248392964906961 24398322276936294723680221)
        ·
          refine ⟨9149370853851110521380083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24398322276936294723680221 9149370853851110521380083)
          ·
            refine ⟨13724056280776665782070125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149370853851110521380083 13724056280776665782070125)
            ·
              refine ⟨5146521105291249668276297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13724056280776665782070125 5146521105291249668276297)
              ·
                refine ⟨3859890828968437251207223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146521105291249668276297 3859890828968437251207223)
                ·
                  refine ⟨5789836243452655876810835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859890828968437251207223 5789836243452655876810835)
                  ·
                    refine ⟨8684754365178983815216253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5789836243452655876810835 8684754365178983815216253)
                    ·
                      refine ⟨3256782886942118930706095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684754365178983815216253 3256782886942118930706095)
                      ·
                        rfl

theorem cell23_6342562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_6342562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342562 prefixEnd_6342562 := by exact prefixLift 6342562
  have htrace : WordTrace (prefixWord ++ tailWord_6342562) baseStart_6342562 baseEnd_6342562 := by
    simpa [prefixWord, tailWord_6342562, baseEnd_6342562] using wordTrace_append hprefix tailTrace_6342562
  have hstable : (prefixWord ++ tailWord_6342562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342562).length < 2 ^ (prefixWord ++ tailWord_6342562).sum := by decide
  have hdescent : baseEnd_6342562 < baseStart_6342562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342584 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_6342584 : Nat := 118140960795 + 6342584 * 2 ^ 59
def prefixEnd_6342584 : Nat := 4983230072969 + 3 ^ 40 * 6342584 * 2
def baseEnd_6342584 : Nat := 3256794183516517844630993

theorem tailTrace_6342584 : CollatzResearch.WordTrace tailWord_6342584 prefixEnd_6342584 3256794183516517844630993 := by
  unfold tailWord_6342584
  simp only [CollatzResearch.WordTrace]
  refine ⟨115666521626954434976097403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154222028835939246634796537 115666521626954434976097403)
  ·
    refine ⟨173499782440431652464146105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115666521626954434976097403 173499782440431652464146105)
    ·
      refine ⟨130124836830323739348109579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173499782440431652464146105 130124836830323739348109579)
      ·
        refine ⟨195187255245485609022164369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130124836830323739348109579 195187255245485609022164369)
        ·
          refine ⟨146390441434114206766623277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195187255245485609022164369 146390441434114206766623277)
          ·
            refine ⟨54896415537792827537483729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146390441434114206766623277 54896415537792827537483729)
            ·
              refine ⟨41172311653344620653112797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54896415537792827537483729 41172311653344620653112797)
              ·
                refine ⟨15439616870004232744917299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41172311653344620653112797 15439616870004232744917299)
                ·
                  refine ⟨23159425305006349117375949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15439616870004232744917299 23159425305006349117375949)
                  ·
                    refine ⟨8684784489377380919015981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23159425305006349117375949 8684784489377380919015981)
                    ·
                      refine ⟨3256794183516517844630993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684784489377380919015981 3256794183516517844630993)
                      ·
                        rfl

theorem cell23_6342584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_6342584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342584 prefixEnd_6342584 := by exact prefixLift 6342584
  have htrace : WordTrace (prefixWord ++ tailWord_6342584) baseStart_6342584 baseEnd_6342584 := by
    simpa [prefixWord, tailWord_6342584, baseEnd_6342584] using wordTrace_append hprefix tailTrace_6342584
  have hstable : (prefixWord ++ tailWord_6342584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342584).length < 2 ^ (prefixWord ++ tailWord_6342584).sum := by decide
  have hdescent : baseEnd_6342584 < baseStart_6342584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342588 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6342588 : Nat := 118140960795 + 6342588 * 2 ^ 59
def prefixEnd_6342588 : Nat := 4983230072969 + 3 ^ 40 * 6342588 * 2
def baseEnd_6342588 : Nat := 3256796237439135828980975

theorem tailTrace_6342588 : CollatzResearch.WordTrace tailWord_6342588 prefixEnd_6342588 3256796237439135828980975 := by
  unfold tailWord_6342588
  simp only [CollatzResearch.WordTrace]
  refine ⟨115666594572947189317670209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154222126097262919090226945 115666594572947189317670209)
  ·
    refine ⟨86749945929710391988252657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115666594572947189317670209 86749945929710391988252657)
    ·
      refine ⟨65062459447282793991189493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86749945929710391988252657 65062459447282793991189493)
      ·
        refine ⟨6099605573182761936674015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65062459447282793991189493 6099605573182761936674015)
        ·
          refine ⟨9149408359774142905011023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099605573182761936674015 9149408359774142905011023)
          ·
            refine ⟨13724112539661214357516535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149408359774142905011023 13724112539661214357516535)
            ·
              refine ⟨20586168809491821536274803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13724112539661214357516535 20586168809491821536274803)
              ·
                refine ⟨30879253214237732304412205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20586168809491821536274803 30879253214237732304412205)
                ·
                  refine ⟨11579719955339149614154577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30879253214237732304412205 11579719955339149614154577)
                  ·
                    refine ⟨8684789966504362210615933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11579719955339149614154577 8684789966504362210615933)
                    ·
                      refine ⟨3256796237439135828980975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8684789966504362210615933 3256796237439135828980975)
                      ·
                        rfl

theorem cell23_6342588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6342588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342588 prefixEnd_6342588 := by exact prefixLift 6342588
  have htrace : WordTrace (prefixWord ++ tailWord_6342588) baseStart_6342588 baseEnd_6342588 := by
    simpa [prefixWord, tailWord_6342588, baseEnd_6342588] using wordTrace_append hprefix tailTrace_6342588
  have hstable : (prefixWord ++ tailWord_6342588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342588).length < 2 ^ (prefixWord ++ tailWord_6342588).sum := by decide
  have hdescent : baseEnd_6342588 < baseStart_6342588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342597 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_6342597 : Nat := 118140960795 + 6342597 * 2 ^ 59
def prefixEnd_6342597 : Nat := 4983230072969 + 3 ^ 40 * 6342597 * 2
def baseEnd_6342597 : Nat := 3256800858765026293768433

theorem tailTrace_6342597 : CollatzResearch.WordTrace tailWord_6342597 prefixEnd_6342597 3256800858765026293768433 := by
  unfold tailWord_6342597
  simp only [CollatzResearch.WordTrace]
  refine ⟨231333517402861773172418045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154222344935241182114945363 231333517402861773172418045)
  ·
    refine ⟨86750069026073164939656767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231333517402861773172418045 86750069026073164939656767)
    ·
      refine ⟨130125103539109747409485151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86750069026073164939656767 130125103539109747409485151)
      ·
        refine ⟨195187655308664621114227727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130125103539109747409485151 195187655308664621114227727)
        ·
          refine ⟨292781482962996931671341591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195187655308664621114227727 292781482962996931671341591)
          ·
            refine ⟨439172224444495397507012387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292781482962996931671341591 439172224444495397507012387)
            ·
              refine ⟨658758336666743096260518581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439172224444495397507012387 658758336666743096260518581)
              ·
                refine ⟨61758594062507165274423617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658758336666743096260518581 61758594062507165274423617)
                ·
                  refine ⟨46318945546880373955817713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61758594062507165274423617 46318945546880373955817713)
                  ·
                    refine ⟨34739209160160280466863285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46318945546880373955817713 34739209160160280466863285)
                    ·
                      refine ⟨3256800858765026293768433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34739209160160280466863285 3256800858765026293768433)
                      ·
                        rfl

theorem cell23_6342597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_6342597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342597 prefixEnd_6342597 := by exact prefixLift 6342597
  have htrace : WordTrace (prefixWord ++ tailWord_6342597) baseStart_6342597 baseEnd_6342597 := by
    simpa [prefixWord, tailWord_6342597, baseEnd_6342597] using wordTrace_append hprefix tailTrace_6342597
  have hstable : (prefixWord ++ tailWord_6342597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342597).length < 2 ^ (prefixWord ++ tailWord_6342597).sum := by decide
  have hdescent : baseEnd_6342597 < baseStart_6342597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342634 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_6342634 : Nat := 118140960795 + 6342634 * 2 ^ 59
def prefixEnd_6342634 : Nat := 4983230072969 + 3 ^ 40 * 6342634 * 2
def baseEnd_6342634 : Nat := 1085606619183080883001921

theorem tailTrace_6342634 : CollatzResearch.WordTrace tailWord_6342634 prefixEnd_6342634 1085606619183080883001921 := by
  unfold tailWord_6342634
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833716725931932122878739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154223244602485152327676637 57833716725931932122878739)
  ·
    refine ⟨86750575088897898184318109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57833716725931932122878739 86750575088897898184318109)
    ·
      refine ⟨32531465658336711819119291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86750575088897898184318109 32531465658336711819119291)
      ·
        refine ⟨48797198487505067728678937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32531465658336711819119291 48797198487505067728678937)
        ·
          refine ⟨36597898865628800796509203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48797198487505067728678937 36597898865628800796509203)
          ·
            refine ⟨54896848298443201194763805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36597898865628800796509203 54896848298443201194763805)
            ·
              refine ⟨20586318111916200448036427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54896848298443201194763805 20586318111916200448036427)
              ·
                refine ⟨30879477167874300672054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20586318111916200448036427 30879477167874300672054641)
                ·
                  refine ⟨23159607875905725504040981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30879477167874300672054641 23159607875905725504040981)
                  ·
                    refine ⟨1085606619183080883001921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23159607875905725504040981 1085606619183080883001921)
                    ·
                      rfl

theorem cell23_6342634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_6342634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342634 prefixEnd_6342634 := by exact prefixLift 6342634
  have htrace : WordTrace (prefixWord ++ tailWord_6342634) baseStart_6342634 baseEnd_6342634 := by
    simpa [prefixWord, tailWord_6342634, baseEnd_6342634] using wordTrace_append hprefix tailTrace_6342634
  have hstable : (prefixWord ++ tailWord_6342634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342634).length < 2 ^ (prefixWord ++ tailWord_6342634).sum := by decide
  have hdescent : baseEnd_6342634 < baseStart_6342634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342692 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6342692 : Nat := 118140960795 + 6342692 * 2 ^ 59
def prefixEnd_6342692 : Nat := 4983230072969 + 3 ^ 40 * 6342692 * 2
def baseEnd_6342692 : Nat := 3256849639427203422080497

theorem tailTrace_6342692 : CollatzResearch.WordTrace tailWord_6342692 prefixEnd_6342692 3256849639427203422080497 := by
  unfold tailWord_6342692
  simp only [CollatzResearch.WordTrace]
  refine ⟨115668491168758802198563165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154224654891678402931417553 115668491168758802198563165)
  ·
    refine ⟨43375684188284550824461187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115668491168758802198563165 43375684188284550824461187)
    ·
      refine ⟨65063526282426826236691781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43375684188284550824461187 65063526282426826236691781)
      ·
        refine ⟨12199411177955029919379709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65063526282426826236691781 12199411177955029919379709)
        ·
          refine ⟨4574779191733136219767391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12199411177955029919379709 4574779191733136219767391)
          ·
            refine ⟨6862168787599704329651087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574779191733136219767391 6862168787599704329651087)
            ·
              refine ⟨10293253181399556494476631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862168787599704329651087 10293253181399556494476631)
              ·
                refine ⟨15439879772099334741714947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10293253181399556494476631 15439879772099334741714947)
                ·
                  refine ⟨23159819658149002112572421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15439879772099334741714947 23159819658149002112572421)
                  ·
                    refine ⟨4342466185902937896107329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23159819658149002112572421 4342466185902937896107329)
                    ·
                      refine ⟨3256849639427203422080497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342466185902937896107329 3256849639427203422080497)
                      ·
                        rfl

theorem cell23_6342692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6342692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342692 prefixEnd_6342692 := by exact prefixLift 6342692
  have htrace : WordTrace (prefixWord ++ tailWord_6342692) baseStart_6342692 baseEnd_6342692 := by
    simpa [prefixWord, tailWord_6342692, baseEnd_6342692] using wordTrace_append hprefix tailTrace_6342692
  have hstable : (prefixWord ++ tailWord_6342692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342692).length < 2 ^ (prefixWord ++ tailWord_6342692).sum := by decide
  have hdescent : baseEnd_6342692 < baseStart_6342692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342768 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_6342768 : Nat := 118140960795 + 6342768 * 2 ^ 59
def prefixEnd_6342768 : Nat := 4983230072969 + 3 ^ 40 * 6342768 * 2
def baseEnd_6342768 : Nat := 3256888663956945124730147

theorem tailTrace_6342768 : CollatzResearch.WordTrace tailWord_6342768 prefixEnd_6342768 3256888663956945124730147 := by
  unfold tailWord_6342768
  simp only [CollatzResearch.WordTrace]
  refine ⟨115669877142621134688446479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154226502856828179584595305 115669877142621134688446479)
  ·
    refine ⟨173504815713931702032669719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115669877142621134688446479 173504815713931702032669719)
    ·
      refine ⟨260257223570897553049004579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173504815713931702032669719 260257223570897553049004579)
      ·
        refine ⟨390385835356346329573506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260257223570897553049004579 390385835356346329573506869)
        ·
          refine ⟨36598672064657468397516269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390385835356346329573506869 36598672064657468397516269)
          ·
            refine ⟨13724502024246550649068601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36598672064657468397516269 13724502024246550649068601)
            ·
              refine ⟨10293376518184912986801451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13724502024246550649068601 10293376518184912986801451)
              ·
                refine ⟨15440064777277369480202177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10293376518184912986801451 15440064777277369480202177)
                ·
                  refine ⟨11580048582958027110151633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15440064777277369480202177 11580048582958027110151633)
                  ·
                    refine ⟨8685036437218520332613725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11580048582958027110151633 8685036437218520332613725)
                    ·
                      refine ⟨3256888663956945124730147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685036437218520332613725 3256888663956945124730147)
                      ·
                        rfl

theorem cell23_6342768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_6342768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342768 prefixEnd_6342768 := by exact prefixLift 6342768
  have htrace : WordTrace (prefixWord ++ tailWord_6342768) baseStart_6342768 baseEnd_6342768 := by
    simpa [prefixWord, tailWord_6342768, baseEnd_6342768] using wordTrace_append hprefix tailTrace_6342768
  have hstable : (prefixWord ++ tailWord_6342768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342768).length < 2 ^ (prefixWord ++ tailWord_6342768).sum := by decide
  have hdescent : baseEnd_6342768 < baseStart_6342768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342792 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 1, 4]
def baseStart_6342792 : Nat := 118140960795 + 6342792 * 2 ^ 59
def prefixEnd_6342792 : Nat := 4983230072969 + 3 ^ 40 * 6342792 * 2
def baseEnd_6342792 : Nat := 1085633662497551010276679

theorem tailTrace_6342792 : CollatzResearch.WordTrace tailWord_6342792 prefixEnd_6342792 1085633662497551010276679 := by
  unfold tailWord_6342792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115670314818577660737883315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154227086424770214317177753 115670314818577660737883315)
  ·
    refine ⟨173505472227866491106824973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115670314818577660737883315 173505472227866491106824973)
    ·
      refine ⟨65064552085449934165059365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173505472227866491106824973 65064552085449934165059365)
      ·
        refine ⟨12199603516021862655948631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65064552085449934165059365 12199603516021862655948631)
        ·
          refine ⟨18299405274032793983922947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199603516021862655948631 18299405274032793983922947)
          ·
            refine ⟨27449107911049190975884421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18299405274032793983922947 27449107911049190975884421)
            ·
              refine ⟨5146707733321723307978329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27449107911049190975884421 5146707733321723307978329)
              ·
                refine ⟨3860030799991292480983747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146707733321723307978329 3860030799991292480983747)
                ·
                  refine ⟨5790046199986938721475621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860030799991292480983747 5790046199986938721475621)
                  ·
                    refine ⟨1085633662497551010276679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790046199986938721475621 1085633662497551010276679)
                    ·
                      rfl

theorem cell23_6342792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_6342792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342792 prefixEnd_6342792 := by exact prefixLift 6342792
  have htrace : WordTrace (prefixWord ++ tailWord_6342792) baseStart_6342792 baseEnd_6342792 := by
    simpa [prefixWord, tailWord_6342792, baseEnd_6342792] using wordTrace_append hprefix tailTrace_6342792
  have hstable : (prefixWord ++ tailWord_6342792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342792).length < 2 ^ (prefixWord ++ tailWord_6342792).sum := by decide
  have hdescent : baseEnd_6342792 < baseStart_6342792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342815 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6342815 : Nat := 118140960795 + 6342815 * 2 ^ 59
def prefixEnd_6342815 : Nat := 4983230072969 + 3 ^ 40 * 6342815 * 2
def baseEnd_6342815 : Nat := 3256912797547706440842431

theorem tailTrace_6342815 : CollatzResearch.WordTrace tailWord_6342815 prefixEnd_6342815 3256912797547706440842431 := by
  unfold tailWord_6342815
  simp only [CollatzResearch.WordTrace]
  refine ⟨231341468516071996403853899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154227645677381330935902599 231341468516071996403853899)
  ·
    refine ⟨347012202774107994605780849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231341468516071996403853899 347012202774107994605780849)
    ·
      refine ⟨260259152080580995954335637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347012202774107994605780849 260259152080580995954335637)
      ·
        refine ⟨12199647753777234185359483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260259152080580995954335637 12199647753777234185359483)
        ·
          refine ⟨18299471630665851278039225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199647753777234185359483 18299471630665851278039225)
          ·
            refine ⟨13724603722999388458529419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18299471630665851278039225 13724603722999388458529419)
            ·
              refine ⟨20586905584499082687794129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13724603722999388458529419 20586905584499082687794129)
              ·
                refine ⟨15440179188374312015845597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20586905584499082687794129 15440179188374312015845597)
                ·
                  refine ⟨5790067195640367005942099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15440179188374312015845597 5790067195640367005942099)
                  ·
                    refine ⟨8685100793460550508913149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790067195640367005942099 8685100793460550508913149)
                    ·
                      refine ⟨3256912797547706440842431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685100793460550508913149 3256912797547706440842431)
                      ·
                        rfl

theorem cell23_6342815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6342815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342815 prefixEnd_6342815 := by exact prefixLift 6342815
  have htrace : WordTrace (prefixWord ++ tailWord_6342815) baseStart_6342815 baseEnd_6342815 := by
    simpa [prefixWord, tailWord_6342815, baseEnd_6342815] using wordTrace_append hprefix tailTrace_6342815
  have hstable : (prefixWord ++ tailWord_6342815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342815).length < 2 ^ (prefixWord ++ tailWord_6342815).sum := by decide
  have hdescent : baseEnd_6342815 < baseStart_6342815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342818 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6342818 : Nat := 118140960795 + 6342818 * 2 ^ 59
def prefixEnd_6342818 : Nat := 4983230072969 + 3 ^ 40 * 6342818 * 2
def baseEnd_6342818 : Nat := 1085638112663223309701639

theorem tailTrace_6342818 : CollatzResearch.WordTrace tailWord_6342818 prefixEnd_6342818 1085638112663223309701639 := by
  unfold tailWord_6342818
  simp only [CollatzResearch.WordTrace]
  refine ⟨57835394483765281979053277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154227718623374085277475405 57835394483765281979053277)
  ·
    refine ⟨21688272931411980742144979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57835394483765281979053277 21688272931411980742144979)
    ·
      refine ⟨32532409397117971113217469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21688272931411980742144979 32532409397117971113217469)
      ·
        refine ⟨12199653523919239167456551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32532409397117971113217469 12199653523919239167456551)
        ·
          refine ⟨18299480285878858751184827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199653523919239167456551 18299480285878858751184827)
          ·
            refine ⟨27449220428818288126777241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18299480285878858751184827 27449220428818288126777241)
            ·
              refine ⟨20586915321613716095082931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27449220428818288126777241 20586915321613716095082931)
              ·
                refine ⟨30880372982420574142624397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20586915321613716095082931 30880372982420574142624397)
                ·
                  refine ⟨11580139868407715303484149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30880372982420574142624397 11580139868407715303484149)
                  ·
                    refine ⟨1085638112663223309701639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11580139868407715303484149 1085638112663223309701639)
                    ·
                      rfl

theorem cell23_6342818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6342818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342818 prefixEnd_6342818 := by exact prefixLift 6342818
  have htrace : WordTrace (prefixWord ++ tailWord_6342818) baseStart_6342818 baseEnd_6342818 := by
    simpa [prefixWord, tailWord_6342818, baseEnd_6342818] using wordTrace_append hprefix tailTrace_6342818
  have hstable : (prefixWord ++ tailWord_6342818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342818).length < 2 ^ (prefixWord ++ tailWord_6342818).sum := by decide
  have hdescent : baseEnd_6342818 < baseStart_6342818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342821 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_6342821 : Nat := 118140960795 + 6342821 * 2 ^ 59
def prefixEnd_6342821 : Nat := 4983230072969 + 3 ^ 40 * 6342821 * 2
def baseEnd_6342821 : Nat := 3256915878431633417367403

theorem tailTrace_6342821 : CollatzResearch.WordTrace tailWord_6342821 prefixEnd_6342821 3256915878431633417367403 := by
  unfold tailWord_6342821
  simp only [CollatzResearch.WordTrace]
  refine ⟨231341687354050259428572317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154227791569366839619048211 231341687354050259428572317)
  ·
    refine ⟨86753132757768847285714619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231341687354050259428572317 86753132757768847285714619)
    ·
      refine ⟨130129699136653270928571929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86753132757768847285714619 130129699136653270928571929)
      ·
        refine ⟨97597274352489953196428947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130129699136653270928571929 97597274352489953196428947)
        ·
          refine ⟨146395911528734929794643421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97597274352489953196428947 146395911528734929794643421)
          ·
            refine ⟨54898466823275598672991283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146395911528734929794643421 54898466823275598672991283)
            ·
              refine ⟨82347700234913398009486925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54898466823275598672991283 82347700234913398009486925)
              ·
                refine ⟨30880387588092524253557597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82347700234913398009486925 30880387588092524253557597)
                ·
                  refine ⟨11580145345534696595084099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30880387588092524253557597 11580145345534696595084099)
                  ·
                    refine ⟨17370218018302044892626149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11580145345534696595084099 17370218018302044892626149)
                    ·
                      refine ⟨3256915878431633417367403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17370218018302044892626149 3256915878431633417367403)
                      ·
                        rfl

theorem cell23_6342821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_6342821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342821 prefixEnd_6342821 := by exact prefixLift 6342821
  have htrace : WordTrace (prefixWord ++ tailWord_6342821) baseStart_6342821 baseEnd_6342821 := by
    simpa [prefixWord, tailWord_6342821, baseEnd_6342821] using wordTrace_append hprefix tailTrace_6342821
  have hstable : (prefixWord ++ tailWord_6342821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342821).length < 2 ^ (prefixWord ++ tailWord_6342821).sum := by decide
  have hdescent : baseEnd_6342821 < baseStart_6342821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342831 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 4, 4]
def baseStart_6342831 : Nat := 118140960795 + 6342831 * 2 ^ 59
def prefixEnd_6342831 : Nat := 4983230072969 + 3 ^ 40 * 6342831 * 2
def baseEnd_6342831 : Nat := 1085640337746059459414119

theorem tailTrace_6342831 : CollatzResearch.WordTrace tailWord_6342831 prefixEnd_6342831 1085640337746059459414119 := by
  unfold tailWord_6342831
  simp only [CollatzResearch.WordTrace]
  refine ⟨231342052084014031136436347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154228034722676020757624231 231342052084014031136436347)
  ·
    refine ⟨347013078126021046704654521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231342052084014031136436347 347013078126021046704654521)
    ·
      refine ⟨260259808594515785028490891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347013078126021046704654521 260259808594515785028490891)
      ·
        refine ⟨390389712891773677542736337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260259808594515785028490891 390389712891773677542736337)
        ·
          refine ⟨292792284668830258157052253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390389712891773677542736337 292792284668830258157052253)
          ·
            refine ⟨109797106750811346808894595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292792284668830258157052253 109797106750811346808894595)
            ·
              refine ⟨164695660126217020213341893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109797106750811346808894595 164695660126217020213341893)
              ·
                refine ⟨30880436273665691290001605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164695660126217020213341893 30880436273665691290001605)
                ·
                  refine ⟨5790081801312317116875301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30880436273665691290001605 5790081801312317116875301)
                  ·
                    refine ⟨1085640337746059459414119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790081801312317116875301 1085640337746059459414119)
                    ·
                      rfl

theorem cell23_6342831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_6342831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342831 prefixEnd_6342831 := by exact prefixLift 6342831
  have htrace : WordTrace (prefixWord ++ tailWord_6342831) baseStart_6342831 baseEnd_6342831 := by
    simpa [prefixWord, tailWord_6342831, baseEnd_6342831] using wordTrace_append hprefix tailTrace_6342831
  have hstable : (prefixWord ++ tailWord_6342831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342831).length < 2 ^ (prefixWord ++ tailWord_6342831).sum := by decide
  have hdescent : baseEnd_6342831 < baseStart_6342831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342841 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6342841 : Nat := 118140960795 + 6342841 * 2 ^ 59
def prefixEnd_6342841 : Nat := 4983230072969 + 3 ^ 40 * 6342841 * 2
def baseEnd_6342841 : Nat := 3256926148044723339117311

theorem tailTrace_6342841 : CollatzResearch.WordTrace tailWord_6342841 prefixEnd_6342841 3256926148044723339117311 := by
  unfold tailWord_6342841
  simp only [CollatzResearch.WordTrace]
  refine ⟨231342416813977802844300377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154228277875985201896200251 231342416813977802844300377)
  ·
    refine ⟨173506812610483352133225283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231342416813977802844300377 173506812610483352133225283)
    ·
      refine ⟨260260218915725028199837925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173506812610483352133225283 260260218915725028199837925)
      ·
        refine ⟨48798791046698442787469611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260260218915725028199837925 48798791046698442787469611)
        ·
          refine ⟨73198186570047664181204417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48798791046698442787469611 73198186570047664181204417)
          ·
            refine ⟨54898639927535748135903313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73198186570047664181204417 54898639927535748135903313)
            ·
              refine ⟨41173979945651811101927485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54898639927535748135903313 41173979945651811101927485)
              ·
                refine ⟨15440242479619429163222807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41173979945651811101927485 15440242479619429163222807)
                ·
                  refine ⟨23160363719429143744834211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15440242479619429163222807 23160363719429143744834211)
                  ·
                    refine ⟨34740545579143715617251317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23160363719429143744834211 34740545579143715617251317)
                    ·
                      refine ⟨3256926148044723339117311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34740545579143715617251317 3256926148044723339117311)
                      ·
                        rfl

theorem cell23_6342841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6342841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342841 prefixEnd_6342841 := by exact prefixLift 6342841
  have htrace : WordTrace (prefixWord ++ tailWord_6342841) baseStart_6342841 baseEnd_6342841 := by
    simpa [prefixWord, tailWord_6342841, baseEnd_6342841] using wordTrace_append hprefix tailTrace_6342841
  have hstable : (prefixWord ++ tailWord_6342841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342841).length < 2 ^ (prefixWord ++ tailWord_6342841).sum := by decide
  have hdescent : baseEnd_6342841 < baseStart_6342841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342848 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_6342848 : Nat := 118140960795 + 6342848 * 2 ^ 59
def prefixEnd_6342848 : Nat := 4983230072969 + 3 ^ 40 * 6342848 * 2
def baseEnd_6342848 : Nat := 1085643247469768270576593

theorem tailTrace_6342848 : CollatzResearch.WordTrace tailWord_6342848 prefixEnd_6342848 1085643247469768270576593 := by
  unfold tailWord_6342848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115671336062476221519902599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154228448083301628693203465 115671336062476221519902599)
  ·
    refine ⟨173507004093714332279853899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115671336062476221519902599 173507004093714332279853899)
    ·
      refine ⟨260260506140571498419780849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173507004093714332279853899 260260506140571498419780849)
      ·
        refine ⟨195195379605428623814835637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260260506140571498419780849 195195379605428623814835637)
        ·
          refine ⟨18299566838008933482640841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195195379605428623814835637 18299566838008933482640841)
          ·
            refine ⟨13724675128506700111980631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18299566838008933482640841 13724675128506700111980631)
            ·
              refine ⟨20587012692760050167970947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13724675128506700111980631 20587012692760050167970947)
              ·
                refine ⟨30880519039140075251956421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20587012692760050167970947 30880519039140075251956421)
                ·
                  refine ⟨5790097319838764109741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30880519039140075251956421 5790097319838764109741829)
                  ·
                    refine ⟨1085643247469768270576593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790097319838764109741829 1085643247469768270576593)
                    ·
                      rfl

theorem cell23_6342848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_6342848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342848 prefixEnd_6342848 := by exact prefixLift 6342848
  have htrace : WordTrace (prefixWord ++ tailWord_6342848) baseStart_6342848 baseEnd_6342848 := by
    simpa [prefixWord, tailWord_6342848, baseEnd_6342848] using wordTrace_append hprefix tailTrace_6342848
  have hstable : (prefixWord ++ tailWord_6342848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342848).length < 2 ^ (prefixWord ++ tailWord_6342848).sum := by decide
  have hdescent : baseEnd_6342848 < baseStart_6342848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342911 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_6342911 : Nat := 118140960795 + 6342911 * 2 ^ 59
def prefixEnd_6342911 : Nat := 4983230072969 + 3 ^ 40 * 6342911 * 2
def baseEnd_6342911 : Nat := 3256962091690538065241989

theorem tailTrace_6342911 : CollatzResearch.WordTrace tailWord_6342911 prefixEnd_6342911 3256962091690538065241989 := by
  unfold tailWord_6342911
  simp only [CollatzResearch.WordTrace]
  refine ⟨231344969923724204799348587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154229979949149469866232391 231344969923724204799348587)
  ·
    refine ⟨347017454885586307199022881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231344969923724204799348587 347017454885586307199022881)
    ·
      refine ⟨260263091164189730399267161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347017454885586307199022881 260263091164189730399267161)
      ·
        refine ⟨195197318373142297799450371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260263091164189730399267161 195197318373142297799450371)
        ·
          refine ⟨292795977559713446699175557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195197318373142297799450371 292795977559713446699175557)
          ·
            refine ⟨54899245792446271256095417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292795977559713446699175557 54899245792446271256095417)
            ·
              refine ⟨41174434344334703442071563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54899245792446271256095417 41174434344334703442071563)
              ·
                refine ⟨61761651516502055163107345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41174434344334703442071563 61761651516502055163107345)
                ·
                  refine ⟨46321238637376541372330509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61761651516502055163107345 46321238637376541372330509)
                  ·
                    refine ⟨17370464489016203014623941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46321238637376541372330509 17370464489016203014623941)
                    ·
                      refine ⟨3256962091690538065241989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17370464489016203014623941 3256962091690538065241989)
                      ·
                        rfl

theorem cell23_6342911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_6342911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342911 prefixEnd_6342911 := by exact prefixLift 6342911
  have htrace : WordTrace (prefixWord ++ tailWord_6342911) baseStart_6342911 baseEnd_6342911 := by
    simpa [prefixWord, tailWord_6342911, baseEnd_6342911] using wordTrace_append hprefix tailTrace_6342911
  have hstable : (prefixWord ++ tailWord_6342911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342911).length < 2 ^ (prefixWord ++ tailWord_6342911).sum := by decide
  have hdescent : baseEnd_6342911 < baseStart_6342911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342922 : List Nat := [3, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_6342922 : Nat := 118140960795 + 6342922 * 2 ^ 59
def prefixEnd_6342922 : Nat := 4983230072969 + 3 ^ 40 * 6342922 * 2
def baseEnd_6342922 : Nat := 3256967739977737522204439

theorem tailTrace_6342922 : CollatzResearch.WordTrace tailWord_6342922 prefixEnd_6342922 3256967739977737522204439 := by
  unfold tailWord_6342922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57836342781671088419499755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154230247417789569118666013 57836342781671088419499755)
  ·
    refine ⟨86754514172506632629249633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57836342781671088419499755 86754514172506632629249633)
    ·
      refine ⟨65065885629379974471937225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86754514172506632629249633 65065885629379974471937225)
      ·
        refine ⟨48799414222034980853952919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65065885629379974471937225 48799414222034980853952919)
        ·
          refine ⟨73199121333052471280929379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48799414222034980853952919 73199121333052471280929379)
          ·
            refine ⟨109798681999578706921394069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73199121333052471280929379 109798681999578706921394069)
            ·
              refine ⟨5146813218730251886940347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109798681999578706921394069 5146813218730251886940347)
              ·
                refine ⟨7720219828095377830410521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146813218730251886940347 7720219828095377830410521)
                ·
                  refine ⟨5790164871071533372807891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720219828095377830410521 5790164871071533372807891)
                  ·
                    refine ⟨8685247306607300059211837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790164871071533372807891 8685247306607300059211837)
                    ·
                      refine ⟨3256967739977737522204439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685247306607300059211837 3256967739977737522204439)
                      ·
                        rfl

theorem cell23_6342922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_6342922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342922 prefixEnd_6342922 := by exact prefixLift 6342922
  have htrace : WordTrace (prefixWord ++ tailWord_6342922) baseStart_6342922 baseEnd_6342922 := by
    simpa [prefixWord, tailWord_6342922, baseEnd_6342922] using wordTrace_append hprefix tailTrace_6342922
  have hstable : (prefixWord ++ tailWord_6342922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342922).length < 2 ^ (prefixWord ++ tailWord_6342922).sum := by decide
  have hdescent : baseEnd_6342922 < baseStart_6342922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342945 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6342945 : Nat := 118140960795 + 6342945 * 2 ^ 59
def prefixEnd_6342945 : Nat := 4983230072969 + 3 ^ 40 * 6342945 * 2
def baseEnd_6342945 : Nat := 3256979550032790932216833

theorem tailTrace_6342945 : CollatzResearch.WordTrace tailWord_6342945 prefixEnd_6342945 3256979550032790932216833 := by
  unfold tailWord_6342945
  simp only [CollatzResearch.WordTrace]
  refine ⟨231346210005601028606086289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154230806670400685737390859 231346210005601028606086289)
  ·
    refine ⟨173509657504200771454564717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231346210005601028606086289 173509657504200771454564717)
    ·
      refine ⟨65066121564075289295461769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173509657504200771454564717 65066121564075289295461769)
      ·
        refine ⟨48799591173056466971596327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65066121564075289295461769 48799591173056466971596327)
        ·
          refine ⟨73199386759584700457394491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48799591173056466971596327 73199386759584700457394491)
          ·
            refine ⟨109799080139377050686091737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73199386759584700457394491 109799080139377050686091737)
            ·
              refine ⟨82349310104532788014568803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109799080139377050686091737 82349310104532788014568803)
              ·
                refine ⟨123523965156799182021853205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82349310104532788014568803 123523965156799182021853205)
                ·
                  refine ⟨5790185866724961657274369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123523965156799182021853205 5790185866724961657274369)
                  ·
                    refine ⟨4342639400043721242955777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5790185866724961657274369 4342639400043721242955777)
                    ·
                      refine ⟨3256979550032790932216833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342639400043721242955777 3256979550032790932216833)
                      ·
                        rfl

theorem cell23_6342945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6342945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342945 prefixEnd_6342945 := by exact prefixLift 6342945
  have htrace : WordTrace (prefixWord ++ tailWord_6342945) baseStart_6342945 baseEnd_6342945 := by
    simpa [prefixWord, tailWord_6342945, baseEnd_6342945] using wordTrace_append hprefix tailTrace_6342945
  have hstable : (prefixWord ++ tailWord_6342945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342945).length < 2 ^ (prefixWord ++ tailWord_6342945).sum := by decide
  have hdescent : baseEnd_6342945 < baseStart_6342945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342948 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6342948 : Nat := 118140960795 + 6342948 * 2 ^ 59
def prefixEnd_6342948 : Nat := 4983230072969 + 3 ^ 40 * 6342948 * 2
def baseEnd_6342948 : Nat := 3256981090474754420479319

theorem tailTrace_6342948 : CollatzResearch.WordTrace tailWord_6342948 prefixEnd_6342948 3256981090474754420479319 := by
  unfold tailWord_6342948
  simp only [CollatzResearch.WordTrace]
  refine ⟨115673159712295080059222749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154230879616393440078963665 115673159712295080059222749)
  ·
    refine ⟨43377434892110655022208531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115673159712295080059222749 43377434892110655022208531)
    ·
      refine ⟨65066152338165982533312797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43377434892110655022208531 65066152338165982533312797)
      ·
        refine ⟨24399807126812243449992299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65066152338165982533312797 24399807126812243449992299)
        ·
          refine ⟨36599710690218365174988449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24399807126812243449992299 36599710690218365174988449)
          ·
            refine ⟨27449783017663773881241337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36599710690218365174988449 27449783017663773881241337)
            ·
              refine ⟨20587337263247830410931003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27449783017663773881241337 20587337263247830410931003)
              ·
                refine ⟨30881005894871745616396505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20587337263247830410931003 30881005894871745616396505)
                ·
                  refine ⟨23160754421153809212297379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30881005894871745616396505 23160754421153809212297379)
                  ·
                    refine ⟨34741131631730713818446069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23160754421153809212297379 34741131631730713818446069)
                    ·
                      refine ⟨3256981090474754420479319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34741131631730713818446069 3256981090474754420479319)
                      ·
                        rfl

theorem cell23_6342948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6342948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342948 prefixEnd_6342948 := by exact prefixLift 6342948
  have htrace : WordTrace (prefixWord ++ tailWord_6342948) baseStart_6342948 baseEnd_6342948 := by
    simpa [prefixWord, tailWord_6342948, baseEnd_6342948] using wordTrace_append hprefix tailTrace_6342948
  have hstable : (prefixWord ++ tailWord_6342948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342948).length < 2 ^ (prefixWord ++ tailWord_6342948).sum := by decide
  have hdescent : baseEnd_6342948 < baseStart_6342948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342949 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_6342949 : Nat := 118140960795 + 6342949 * 2 ^ 59
def prefixEnd_6342949 : Nat := 4983230072969 + 3 ^ 40 * 6342949 * 2
def baseEnd_6342949 : Nat := 3256981603955408916566815

theorem tailTrace_6342949 : CollatzResearch.WordTrace tailWord_6342949 prefixEnd_6342949 3256981603955408916566815 := by
  unfold tailWord_6342949
  simp only [CollatzResearch.WordTrace]
  refine ⟨231346355897586537289231901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154230903931724358192821267 231346355897586537289231901)
  ·
    refine ⟨86754883461594951483461963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231346355897586537289231901 86754883461594951483461963)
    ·
      refine ⟨130132325192392427225192945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86754883461594951483461963 130132325192392427225192945)
      ·
        refine ⟨97599243894294320418894709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130132325192392427225192945 97599243894294320418894709)
        ·
          refine ⟨9149929115090092539271379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97599243894294320418894709 9149929115090092539271379)
          ·
            refine ⟨13724893672635138808907069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149929115090092539271379 13724893672635138808907069)
            ·
              refine ⟨5146835127238177053340151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13724893672635138808907069 5146835127238177053340151)
              ·
                refine ⟨7720252690857265580010227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146835127238177053340151 7720252690857265580010227)
                ·
                  refine ⟨11580379036285898370015341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7720252690857265580010227 11580379036285898370015341)
                  ·
                    refine ⟨4342642138607211888755753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11580379036285898370015341 4342642138607211888755753)
                    ·
                      refine ⟨3256981603955408916566815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342642138607211888755753 3256981603955408916566815)
                      ·
                        rfl

theorem cell23_6342949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_6342949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342949 prefixEnd_6342949 := by exact prefixLift 6342949
  have htrace : WordTrace (prefixWord ++ tailWord_6342949) baseStart_6342949 baseEnd_6342949 := by
    simpa [prefixWord, tailWord_6342949, baseEnd_6342949] using wordTrace_append hprefix tailTrace_6342949
  have hstable : (prefixWord ++ tailWord_6342949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342949).length < 2 ^ (prefixWord ++ tailWord_6342949).sum := by decide
  have hdescent : baseEnd_6342949 < baseStart_6342949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6342991 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_6342991 : Nat := 118140960795 + 6342991 * 2 ^ 59
def prefixEnd_6342991 : Nat := 4983230072969 + 3 ^ 40 * 6342991 * 2
def baseEnd_6342991 : Nat := 3257003170142897752241621

theorem tailTrace_6342991 : CollatzResearch.WordTrace tailWord_6342991 prefixEnd_6342991 3257003170142897752241621 := by
  unfold tailWord_6342991
  simp only [CollatzResearch.WordTrace]
  refine ⟨231347887763434378462260827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154231925175622918974840551 231347887763434378462260827)
  ·
    refine ⟨347021831645151567693391241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231347887763434378462260827 347021831645151567693391241)
    ·
      refine ⟨260266373733863675770043431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347021831645151567693391241 260266373733863675770043431)
      ·
        refine ⟨390399560600795513655065147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260266373733863675770043431 390399560600795513655065147)
        ·
          refine ⟨585599340901193270482597721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390399560600795513655065147 585599340901193270482597721)
          ·
            refine ⟨439199505675894952861948291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585599340901193270482597721 439199505675894952861948291)
            ·
              refine ⟨658799258513842429292922437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439199505675894952861948291 658799258513842429292922437)
              ·
                refine ⟨123524860971345455492422957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658799258513842429292922437 123524860971345455492422957)
                ·
                  refine ⟨46321822864254545809658609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123524860971345455492422957 46321822864254545809658609)
                  ·
                    refine ⟨34741367148190909357243957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46321822864254545809658609 34741367148190909357243957)
                    ·
                      refine ⟨3257003170142897752241621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34741367148190909357243957 3257003170142897752241621)
                      ·
                        rfl

theorem cell23_6342991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_6342991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6342991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6342991 prefixEnd_6342991 := by exact prefixLift 6342991
  have htrace : WordTrace (prefixWord ++ tailWord_6342991) baseStart_6342991 baseEnd_6342991 := by
    simpa [prefixWord, tailWord_6342991, baseEnd_6342991] using wordTrace_append hprefix tailTrace_6342991
  have hstable : (prefixWord ++ tailWord_6342991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6342991).length < 2 ^ (prefixWord ++ tailWord_6342991).sum := by decide
  have hdescent : baseEnd_6342991 < baseStart_6342991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6342991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343035 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 4, 2]
def baseStart_6343035 : Nat := 118140960795 + 6343035 * 2 ^ 59
def prefixEnd_6343035 : Nat := 4983230072969 + 3 ^ 40 * 6343035 * 2
def baseEnd_6343035 : Nat := 3257025763291695580091419

theorem tailTrace_6343035 : CollatzResearch.WordTrace tailWord_6343035 prefixEnd_6343035 3257025763291695580091419 := by
  unfold tailWord_6343035
  simp only [CollatzResearch.WordTrace]
  refine ⟨231349492575274973976862559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154232995050183315984575039 231349492575274973976862559)
  ·
    refine ⟨347024238862912460965293839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231349492575274973976862559 347024238862912460965293839)
    ·
      refine ⟨520536358294368691447940759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347024238862912460965293839 520536358294368691447940759)
      ·
        refine ⟨780804537441553037171911139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520536358294368691447940759 780804537441553037171911139)
        ·
          refine ⟨1171206806162329555757866709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780804537441553037171911139 1171206806162329555757866709)
          ·
            refine ⟨27450159519429598963075001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1171206806162329555757866709 27450159519429598963075001)
            ·
              refine ⟨20587619639572199222306251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27450159519429598963075001 20587619639572199222306251)
              ·
                refine ⟨30881429459358298833459377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20587619639572199222306251 30881429459358298833459377)
                ·
                  refine ⟨23161072094518724125094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30881429459358298833459377 23161072094518724125094533)
                  ·
                    refine ⟨4342701017722260773455225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23161072094518724125094533 4342701017722260773455225)
                    ·
                      refine ⟨3257025763291695580091419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342701017722260773455225 3257025763291695580091419)
                      ·
                        rfl

theorem cell23_6343035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 4, 2].length) (baseStart_6343035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343035 prefixEnd_6343035 := by exact prefixLift 6343035
  have htrace : WordTrace (prefixWord ++ tailWord_6343035) baseStart_6343035 baseEnd_6343035 := by
    simpa [prefixWord, tailWord_6343035, baseEnd_6343035] using wordTrace_append hprefix tailTrace_6343035
  have hstable : (prefixWord ++ tailWord_6343035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343035).length < 2 ^ (prefixWord ++ tailWord_6343035).sum := by decide
  have hdescent : baseEnd_6343035 < baseStart_6343035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343048 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6343048 : Nat := 118140960795 + 6343048 * 2 ^ 59
def prefixEnd_6343048 : Nat := 4983230072969 + 3 ^ 40 * 6343048 * 2
def baseEnd_6343048 : Nat := 3257032438540204029228859

theorem tailTrace_6343048 : CollatzResearch.WordTrace tailWord_6343048 prefixEnd_6343048 3257032438540204029228859 := by
  unfold tailWord_6343048
  simp only [CollatzResearch.WordTrace]
  refine ⟨115674983362113938598542899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154233311149485251464723865 115674983362113938598542899)
  ·
    refine ⟨173512475043170907897814349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115674983362113938598542899 173512475043170907897814349)
    ·
      refine ⟨65067178141189090461680381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173512475043170907897814349 65067178141189090461680381)
      ·
        refine ⟨24400191802945908923130143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65067178141189090461680381 24400191802945908923130143)
        ·
          refine ⟨36600287704418863384695215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24400191802945908923130143 36600287704418863384695215)
          ·
            refine ⟨54900431556628295077042823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36600287704418863384695215 54900431556628295077042823)
            ·
              refine ⟨82350647334942442615564235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54900431556628295077042823 82350647334942442615564235)
              ·
                refine ⟨123525971002413663923346353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82350647334942442615564235 123525971002413663923346353)
                ·
                  refine ⟨92644478251810247942509765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123525971002413663923346353 92644478251810247942509765)
                  ·
                    refine ⟨17370839672214421489220581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92644478251810247942509765 17370839672214421489220581)
                    ·
                      refine ⟨3257032438540204029228859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17370839672214421489220581 3257032438540204029228859)
                      ·
                        rfl

theorem cell23_6343048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6343048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343048 prefixEnd_6343048 := by exact prefixLift 6343048
  have htrace : WordTrace (prefixWord ++ tailWord_6343048) baseStart_6343048 baseEnd_6343048 := by
    simpa [prefixWord, tailWord_6343048, baseEnd_6343048] using wordTrace_append hprefix tailTrace_6343048
  have hstable : (prefixWord ++ tailWord_6343048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343048).length < 2 ^ (prefixWord ++ tailWord_6343048).sum := by decide
  have hdescent : baseEnd_6343048 < baseStart_6343048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343102 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_6343102 : Nat := 118140960795 + 6343102 * 2 ^ 59
def prefixEnd_6343102 : Nat := 4983230072969 + 3 ^ 40 * 6343102 * 2
def baseEnd_6343102 : Nat := 3257060166495546817953611

theorem tailTrace_6343102 : CollatzResearch.WordTrace tailWord_6343102 prefixEnd_6343102 3257060166495546817953611 := by
  unfold tailWord_6343102
  simp only [CollatzResearch.WordTrace]
  refine ⟨28918992033254030552443945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154234624177354829613034373 28918992033254030552443945)
  ·
    refine ⟨21689244024940522914332959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28918992033254030552443945 21689244024940522914332959)
    ·
      refine ⟨32533866037410784371499439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21689244024940522914332959 32533866037410784371499439)
      ·
        refine ⟨48800799056116176557249159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32533866037410784371499439 48800799056116176557249159)
        ·
          refine ⟨73201198584174264835873739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48800799056116176557249159 73201198584174264835873739)
          ·
            refine ⟨109801797876261397253810609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73201198584174264835873739 109801797876261397253810609)
            ·
              refine ⟨82351348407196047940357957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109801797876261397253810609 82351348407196047940357957)
              ·
                refine ⟨15440877826349258988817117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82351348407196047940357957 15440877826349258988817117)
                ·
                  refine ⟨5790329184880972120806419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15440877826349258988817117 5790329184880972120806419)
                  ·
                    refine ⟨8685493777321458181209629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790329184880972120806419 8685493777321458181209629)
                    ·
                      refine ⟨3257060166495546817953611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685493777321458181209629 3257060166495546817953611)
                      ·
                        rfl

theorem cell23_6343102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_6343102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343102 prefixEnd_6343102 := by exact prefixLift 6343102
  have htrace : WordTrace (prefixWord ++ tailWord_6343102) baseStart_6343102 baseEnd_6343102 := by
    simpa [prefixWord, tailWord_6343102, baseEnd_6343102] using wordTrace_append hprefix tailTrace_6343102
  have hstable : (prefixWord ++ tailWord_6343102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343102).length < 2 ^ (prefixWord ++ tailWord_6343102).sum := by decide
  have hdescent : baseEnd_6343102 < baseStart_6343102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343112 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_6343112 : Nat := 118140960795 + 6343112 * 2 ^ 59
def prefixEnd_6343112 : Nat := 4983230072969 + 3 ^ 40 * 6343112 * 2
def baseEnd_6343112 : Nat := 3257065301302091778828565

theorem tailTrace_6343112 : CollatzResearch.WordTrace tailWord_6343112 prefixEnd_6343112 3257065301302091778828565 := by
  unfold tailWord_6343112
  simp only [CollatzResearch.WordTrace]
  refine ⟨115676150497998008063707795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154234867330664010751610393 115676150497998008063707795)
  ·
    refine ⟨173514225746997012095561693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115676150497998008063707795 173514225746997012095561693)
    ·
      refine ⟨65067834655123879535835635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173514225746997012095561693 65067834655123879535835635)
      ·
        refine ⟨97601751982685819303753453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65067834655123879535835635 97601751982685819303753453)
        ·
          refine ⟨36600656993507182238907545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97601751982685819303753453 36600656993507182238907545)
          ·
            refine ⟨27450492745130386679180659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36600656993507182238907545 27450492745130386679180659)
            ·
              refine ⟨41175739117695580018770989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27450492745130386679180659 41175739117695580018770989)
              ·
                refine ⟨15440902169135842507039121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41175739117695580018770989 15440902169135842507039121)
                ·
                  refine ⟨11580676626851881880279341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15440902169135842507039121 11580676626851881880279341)
                  ·
                    refine ⟨4342753735069455705104753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11580676626851881880279341 4342753735069455705104753)
                    ·
                      refine ⟨3257065301302091778828565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342753735069455705104753 3257065301302091778828565)
                      ·
                        rfl

theorem cell23_6343112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_6343112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343112 prefixEnd_6343112 := by exact prefixLift 6343112
  have htrace : WordTrace (prefixWord ++ tailWord_6343112) baseStart_6343112 baseEnd_6343112 := by
    simpa [prefixWord, tailWord_6343112, baseEnd_6343112] using wordTrace_append hprefix tailTrace_6343112
  have hstable : (prefixWord ++ tailWord_6343112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343112).length < 2 ^ (prefixWord ++ tailWord_6343112).sum := by decide
  have hdescent : baseEnd_6343112 < baseStart_6343112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343155 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4]
def baseStart_6343155 : Nat := 118140960795 + 6343155 * 2 ^ 59
def prefixEnd_6343155 : Nat := 4983230072969 + 3 ^ 40 * 6343155 * 2
def baseEnd_6343155 : Nat := 3257087380970235110590867

theorem tailTrace_6343155 : CollatzResearch.WordTrace tailWord_6343155 prefixEnd_6343155 3257087380970235110590867 := by
  unfold tailWord_6343155
  simp only [CollatzResearch.WordTrace]
  refine ⟨231353869334840234471230919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154235912889893489647487279 231353869334840234471230919)
  ·
    refine ⟨347030804002260351706846379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231353869334840234471230919 347030804002260351706846379)
    ·
      refine ⟨520546206003390527560269569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347030804002260351706846379 520546206003390527560269569)
      ·
        refine ⟨390409654502542895670202177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520546206003390527560269569 390409654502542895670202177)
        ·
          refine ⟨292807240876907171752651633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390409654502542895670202177 292807240876907171752651633)
          ·
            refine ⟨219605430657680378814488725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292807240876907171752651633 219605430657680378814488725)
            ·
              refine ⟨10294004562078767756929159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219605430657680378814488725 10294004562078767756929159)
              ·
                refine ⟨15441006843118151635393739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10294004562078767756929159 15441006843118151635393739)
                ·
                  refine ⟨23161510264677227453090609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15441006843118151635393739 23161510264677227453090609)
                  ·
                    refine ⟨17371132698507920589817957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23161510264677227453090609 17371132698507920589817957)
                    ·
                      refine ⟨3257087380970235110590867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17371132698507920589817957 3257087380970235110590867)
                      ·
                        rfl

theorem cell23_6343155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_6343155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343155 prefixEnd_6343155 := by exact prefixLift 6343155
  have htrace : WordTrace (prefixWord ++ tailWord_6343155) baseStart_6343155 baseEnd_6343155 := by
    simpa [prefixWord, tailWord_6343155, baseEnd_6343155] using wordTrace_append hprefix tailTrace_6343155
  have hstable : (prefixWord ++ tailWord_6343155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343155).length < 2 ^ (prefixWord ++ tailWord_6343155).sum := by decide
  have hdescent : baseEnd_6343155 < baseStart_6343155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343165 : List Nat := [1, 4, 1, 1, 1, 3, 5, 7]
def baseStart_6343165 : Nat := 118140960795 + 6343165 * 2 ^ 59
def prefixEnd_6343165 : Nat := 4983230072969 + 3 ^ 40 * 6343165 * 2
def baseEnd_6343165 : Nat := 120633056139880743387623

theorem tailTrace_6343165 : CollatzResearch.WordTrace tailWord_6343165 prefixEnd_6343165 120633056139880743387623 := by
  unfold tailWord_6343165
  simp only [CollatzResearch.WordTrace]
  refine ⟨231354234064804006179094949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154236156043202670786063299 231354234064804006179094949)
  ·
    refine ⟨43378918887150751158580303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231354234064804006179094949 43378918887150751158580303)
    ·
      refine ⟨65068378330726126737870455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43378918887150751158580303 65068378330726126737870455)
      ·
        refine ⟨97602567496089190106805683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65068378330726126737870455 97602567496089190106805683)
        ·
          refine ⟨146403851244133785160208525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97602567496089190106805683 146403851244133785160208525)
          ·
            refine ⟨54901444216550169435078197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146403851244133785160208525 54901444216550169435078197)
            ·
              refine ⟨5147010395301578384538581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54901444216550169435078197 5147010395301578384538581)
              ·
                refine ⟨120633056139880743387623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5147010395301578384538581 120633056139880743387623)
                ·
                  rfl

theorem cell23_6343165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 7].length) (baseStart_6343165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343165 prefixEnd_6343165 := by exact prefixLift 6343165
  have htrace : WordTrace (prefixWord ++ tailWord_6343165) baseStart_6343165 baseEnd_6343165 := by
    simpa [prefixWord, tailWord_6343165, baseEnd_6343165] using wordTrace_append hprefix tailTrace_6343165
  have hstable : (prefixWord ++ tailWord_6343165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343165).length < 2 ^ (prefixWord ++ tailWord_6343165).sum := by decide
  have hdescent : baseEnd_6343165 < baseStart_6343165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343172 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6343172 : Nat := 118140960795 + 6343172 * 2 ^ 59
def prefixEnd_6343172 : Nat := 4983230072969 + 3 ^ 40 * 6343172 * 2
def baseEnd_6343172 : Nat := 3257096110141361544078289

theorem tailTrace_6343172 : CollatzResearch.WordTrace tailWord_6343172 prefixEnd_6343172 3257096110141361544078289 := by
  unfold tailWord_6343172
  simp only [CollatzResearch.WordTrace]
  refine ⟨115677244687889323187299885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154236326250519097583066513 115677244687889323187299885)
  ·
    refine ⟨43378966757958496195237457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115677244687889323187299885 43378966757958496195237457)
    ·
      refine ⟨32534225068468872146428093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43378966757958496195237457 32534225068468872146428093)
      ·
        refine ⟨12200334400675827054910535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32534225068468872146428093 12200334400675827054910535)
        ·
          refine ⟨18300501601013740582365803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12200334400675827054910535 18300501601013740582365803)
          ·
            refine ⟨27450752401520610873548705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300501601013740582365803 27450752401520610873548705)
            ·
              refine ⟨20588064301140458155161529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27450752401520610873548705 20588064301140458155161529)
              ·
                refine ⟨15441048225855343616371147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20588064301140458155161529 15441048225855343616371147)
                ·
                  refine ⟨23161572338783015424556721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15441048225855343616371147 23161572338783015424556721)
                  ·
                    refine ⟨17371179254087261568417541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23161572338783015424556721 17371179254087261568417541)
                    ·
                      refine ⟨3257096110141361544078289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17371179254087261568417541 3257096110141361544078289)
                      ·
                        rfl

theorem cell23_6343172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6343172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343172 prefixEnd_6343172 := by exact prefixLift 6343172
  have htrace : WordTrace (prefixWord ++ tailWord_6343172) baseStart_6343172 baseEnd_6343172 := by
    simpa [prefixWord, tailWord_6343172, baseEnd_6343172] using wordTrace_append hprefix tailTrace_6343172
  have hstable : (prefixWord ++ tailWord_6343172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343172).length < 2 ^ (prefixWord ++ tailWord_6343172).sum := by decide
  have hdescent : baseEnd_6343172 < baseStart_6343172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343179 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 1, 2, 3]
def baseStart_6343179 : Nat := 118140960795 + 6343179 * 2 ^ 59
def prefixEnd_6343179 : Nat := 4983230072969 + 3 ^ 40 * 6343179 * 2
def baseEnd_6343179 : Nat := 3257099704505943016690757

theorem tailTrace_6343179 : CollatzResearch.WordTrace tailWord_6343179 prefixEnd_6343179 3257099704505943016690757 := by
  unfold tailWord_6343179
  simp only [CollatzResearch.WordTrace]
  refine ⟨231354744686753286570104591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154236496457835524380069727 231354744686753286570104591)
  ·
    refine ⟨347032117030129929855156887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231354744686753286570104591 347032117030129929855156887)
    ·
      refine ⟨520548175545194894782735331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347032117030129929855156887 520548175545194894782735331)
      ·
        refine ⟨780822263317792342174102997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520548175545194894782735331 780822263317792342174102997)
        ·
          refine ⟨18300521796510758019705539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 780822263317792342174102997 18300521796510758019705539)
          ·
            refine ⟨27450782694766137029558309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300521796510758019705539 27450782694766137029558309)
            ·
              refine ⟨5147021755268650693042183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27450782694766137029558309 5147021755268650693042183)
              ·
                refine ⟨7720532632902976039563275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147021755268650693042183 7720532632902976039563275)
                ·
                  refine ⟨11580798949354464059344913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7720532632902976039563275 11580798949354464059344913)
                  ·
                    refine ⟨8685599212015848044508685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11580798949354464059344913 8685599212015848044508685)
                    ·
                      refine ⟨3257099704505943016690757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685599212015848044508685 3257099704505943016690757)
                      ·
                        rfl

theorem cell23_6343179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 2, 3].length) (baseStart_6343179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343179 prefixEnd_6343179 := by exact prefixLift 6343179
  have htrace : WordTrace (prefixWord ++ tailWord_6343179) baseStart_6343179 baseEnd_6343179 := by
    simpa [prefixWord, tailWord_6343179, baseEnd_6343179] using wordTrace_append hprefix tailTrace_6343179
  have hstable : (prefixWord ++ tailWord_6343179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343179).length < 2 ^ (prefixWord ++ tailWord_6343179).sum := by decide
  have hdescent : baseEnd_6343179 < baseStart_6343179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343219 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 1, 3, 2]
def baseStart_6343219 : Nat := 118140960795 + 6343219 * 2 ^ 59
def prefixEnd_6343219 : Nat := 4983230072969 + 3 ^ 40 * 6343219 * 2
def baseEnd_6343219 : Nat := 3257120243732122860190573

theorem tailTrace_6343219 : CollatzResearch.WordTrace tailWord_6343219 prefixEnd_6343219 3257120243732122860190573 := by
  unfold tailWord_6343219
  simp only [CollatzResearch.WordTrace]
  refine ⟨231356203606608373401560711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154237469071072248934373807 231356203606608373401560711)
  ·
    refine ⟨347034305409912560102341067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231356203606608373401560711 347034305409912560102341067)
    ·
      refine ⟨520551458114868840153511601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347034305409912560102341067 520551458114868840153511601)
      ·
        refine ⟨390413593586151630115133701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520551458114868840153511601 390413593586151630115133701)
        ·
          refine ⟨73202548797403430646587569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390413593586151630115133701 73202548797403430646587569)
          ·
            refine ⟨54901911598052572984940677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73202548797403430646587569 54901911598052572984940677)
            ·
              refine ⟨10294108424634857434676377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54901911598052572984940677 10294108424634857434676377)
              ·
                refine ⟨7720581318476143076007283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10294108424634857434676377 7720581318476143076007283)
                ·
                  refine ⟨11580871977714214614010925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7720581318476143076007283 11580871977714214614010925)
                  ·
                    refine ⟨4342826991642830480254097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11580871977714214614010925 4342826991642830480254097)
                    ·
                      refine ⟨3257120243732122860190573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342826991642830480254097 3257120243732122860190573)
                      ·
                        rfl

theorem cell23_6343219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 3, 2].length) (baseStart_6343219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343219 prefixEnd_6343219 := by exact prefixLift 6343219
  have htrace : WordTrace (prefixWord ++ tailWord_6343219) baseStart_6343219 baseEnd_6343219 := by
    simpa [prefixWord, tailWord_6343219, baseEnd_6343219] using wordTrace_append hprefix tailTrace_6343219
  have hstable : (prefixWord ++ tailWord_6343219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343219).length < 2 ^ (prefixWord ++ tailWord_6343219).sum := by decide
  have hdescent : baseEnd_6343219 < baseStart_6343219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343222 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6343222 : Nat := 118140960795 + 6343222 * 2 ^ 59
def prefixEnd_6343222 : Nat := 4983230072969 + 3 ^ 40 * 6343222 * 2
def baseEnd_6343222 : Nat := 3257121784174086348453059

theorem tailTrace_6343222 : CollatzResearch.WordTrace tailWord_6343222 prefixEnd_6343222 3257121784174086348453059 := by
  unfold tailWord_6343222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459769564099844057119995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154237542017065003275946613 14459769564099844057119995)
  ·
    refine ⟨21689654346149766085679993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14459769564099844057119995 21689654346149766085679993)
    ·
      refine ⟨16267240759612324564259995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21689654346149766085679993 16267240759612324564259995)
      ·
        refine ⟨24400861139418486846389993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267240759612324564259995 24400861139418486846389993)
        ·
          refine ⟨18300645854563865134792495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24400861139418486846389993 18300645854563865134792495)
          ·
            refine ⟨27450968781845797702188743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300645854563865134792495 27450968781845797702188743)
            ·
              refine ⟨41176453172768696553283115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27450968781845797702188743 41176453172768696553283115)
              ·
                refine ⟨61764679759153044829924673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41176453172768696553283115 61764679759153044829924673)
                ·
                  refine ⟨46323509819364783622443505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61764679759153044829924673 46323509819364783622443505)
                  ·
                    refine ⟨34742632364523587716832629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46323509819364783622443505 34742632364523587716832629)
                    ·
                      refine ⟨3257121784174086348453059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34742632364523587716832629 3257121784174086348453059)
                      ·
                        rfl

theorem cell23_6343222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6343222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343222 prefixEnd_6343222 := by exact prefixLift 6343222
  have htrace : WordTrace (prefixWord ++ tailWord_6343222) baseStart_6343222 baseEnd_6343222 := by
    simpa [prefixWord, tailWord_6343222, baseEnd_6343222] using wordTrace_append hprefix tailTrace_6343222
  have hstable : (prefixWord ++ tailWord_6343222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343222).length < 2 ^ (prefixWord ++ tailWord_6343222).sum := by decide
  have hdescent : baseEnd_6343222 < baseStart_6343222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343232 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2]
def baseStart_6343232 : Nat := 118140960795 + 6343232 * 2 ^ 59
def prefixEnd_6343232 : Nat := 4983230072969 + 3 ^ 40 * 6343232 * 2
def baseEnd_6343232 : Nat := 3257126918980631309328013

theorem tailTrace_6343232 : CollatzResearch.WordTrace tailWord_6343232 prefixEnd_6343232 3257126918980631309328013 := by
  unfold tailWord_6343232
  simp only [CollatzResearch.WordTrace]
  refine ⟨115678338877780638310891975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154237785170374184414522633 115678338877780638310891975)
  ·
    refine ⟨173517508316670957466337963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115678338877780638310891975 173517508316670957466337963)
    ·
      refine ⟨260276262475006436199506945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173517508316670957466337963 260276262475006436199506945)
      ·
        refine ⟨195207196856254827149630209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260276262475006436199506945 195207196856254827149630209)
        ·
          refine ⟨146405397642191120362222657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195207196856254827149630209 146405397642191120362222657)
          ·
            refine ⟨109804048231643340271666993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146405397642191120362222657 109804048231643340271666993)
            ·
              refine ⟨82353036173732505203750245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109804048231643340271666993 82353036173732505203750245)
              ·
                refine ⟨15441194282574844725703171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82353036173732505203750245 15441194282574844725703171)
                ·
                  refine ⟨23161791423862267088554757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15441194282574844725703171 23161791423862267088554757)
                  ·
                    refine ⟨4342835891974175079104017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23161791423862267088554757 4342835891974175079104017)
                    ·
                      refine ⟨3257126918980631309328013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342835891974175079104017 3257126918980631309328013)
                      ·
                        rfl

theorem cell23_6343232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_6343232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343232 prefixEnd_6343232 := by exact prefixLift 6343232
  have htrace : WordTrace (prefixWord ++ tailWord_6343232) baseStart_6343232 baseEnd_6343232 := by
    simpa [prefixWord, tailWord_6343232, baseEnd_6343232] using wordTrace_append hprefix tailTrace_6343232
  have hstable : (prefixWord ++ tailWord_6343232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343232).length < 2 ^ (prefixWord ++ tailWord_6343232).sum := by decide
  have hdescent : baseEnd_6343232 < baseStart_6343232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343249 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_6343249 : Nat := 118140960795 + 6343249 * 2 ^ 59
def prefixEnd_6343249 : Nat := 4983230072969 + 3 ^ 40 * 6343249 * 2
def baseEnd_6343249 : Nat := 3257135648151757742815435

theorem tailTrace_6343249 : CollatzResearch.WordTrace tailWord_6343249 prefixEnd_6343249 3257135648151757742815435 := by
  unfold tailWord_6343249
  simp only [CollatzResearch.WordTrace]
  refine ⟨231357297796499688525152801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154238198530999792350101867 231357297796499688525152801)
  ·
    refine ⟨173517973347374766393864601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231357297796499688525152801 173517973347374766393864601)
    ·
      refine ⟨130138480010531074795398451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173517973347374766393864601 130138480010531074795398451)
      ·
        refine ⟨195207720015796612193097677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130138480010531074795398451 195207720015796612193097677)
        ·
          refine ⟨73202895005923729572411629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195207720015796612193097677 73202895005923729572411629)
          ·
            refine ⟨27451085627221398589654361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73202895005923729572411629 27451085627221398589654361)
            ·
              refine ⟨20588314220416048942240771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27451085627221398589654361 20588314220416048942240771)
              ·
                refine ⟨30882471330624073413361157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20588314220416048942240771 30882471330624073413361157)
                ·
                  refine ⟨5790463374492013765005217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30882471330624073413361157 5790463374492013765005217)
                  ·
                    refine ⟨4342847530869010323753913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5790463374492013765005217 4342847530869010323753913)
                    ·
                      refine ⟨3257135648151757742815435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4342847530869010323753913 3257135648151757742815435)
                      ·
                        rfl

theorem cell23_6343249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_6343249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343249 prefixEnd_6343249 := by exact prefixLift 6343249
  have htrace : WordTrace (prefixWord ++ tailWord_6343249) baseStart_6343249 baseEnd_6343249 := by
    simpa [prefixWord, tailWord_6343249, baseEnd_6343249] using wordTrace_append hprefix tailTrace_6343249
  have hstable : (prefixWord ++ tailWord_6343249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343249).length < 2 ^ (prefixWord ++ tailWord_6343249).sum := by decide
  have hdescent : baseEnd_6343249 < baseStart_6343249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343260 : List Nat := [2, 2, 4, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6343260 : Nat := 118140960795 + 6343260 * 2 ^ 59
def prefixEnd_6343260 : Nat := 4983230072969 + 3 ^ 40 * 6343260 * 2
def baseEnd_6343260 : Nat := 3257141296438957199777885

theorem tailTrace_6343260 : CollatzResearch.WordTrace tailWord_6343260 prefixEnd_6343260 3257141296438957199777885 := by
  unfold tailWord_6343260
  simp only [CollatzResearch.WordTrace]
  refine ⟨115678849499729918701901617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154238465999639891602535489 115678849499729918701901617)
  ·
    refine ⟨86759137124797439026426213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115678849499729918701901617 86759137124797439026426213)
    ·
      refine ⟨16267338210899519817454915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86759137124797439026426213 16267338210899519817454915)
      ·
        refine ⟨24401007316349279726182373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267338210899519817454915 24401007316349279726182373)
        ·
          refine ⟨4575188871815489948659195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24401007316349279726182373 4575188871815489948659195)
          ·
            refine ⟨6862783307723234922988793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575188871815489948659195 6862783307723234922988793)
            ·
              refine ⟨5147087480792426192241595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6862783307723234922988793 5147087480792426192241595)
              ·
                refine ⟨7720631221188639288362393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147087480792426192241595 7720631221188639288362393)
                ·
                  refine ⟨5790473415891479466271795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720631221188639288362393 5790473415891479466271795)
                  ·
                    refine ⟨8685710123837219199407693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790473415891479466271795 8685710123837219199407693)
                    ·
                      refine ⟨3257141296438957199777885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685710123837219199407693 3257141296438957199777885)
                      ·
                        rfl

theorem cell23_6343260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6343260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343260 prefixEnd_6343260 := by exact prefixLift 6343260
  have htrace : WordTrace (prefixWord ++ tailWord_6343260) baseStart_6343260 baseEnd_6343260 := by
    simpa [prefixWord, tailWord_6343260, baseEnd_6343260] using wordTrace_append hprefix tailTrace_6343260
  have hstable : (prefixWord ++ tailWord_6343260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343260).length < 2 ^ (prefixWord ++ tailWord_6343260).sum := by decide
  have hdescent : baseEnd_6343260 < baseStart_6343260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343305 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_6343305 : Nat := 118140960795 + 6343305 * 2 ^ 59
def prefixEnd_6343305 : Nat := 4983230072969 + 3 ^ 40 * 6343305 * 2
def baseEnd_6343305 : Nat := 3257164403068409523715177

theorem tailTrace_6343305 : CollatzResearch.WordTrace tailWord_6343305 prefixEnd_6343305 3257164403068409523715177 := by
  unfold tailWord_6343305
  simp only [CollatzResearch.WordTrace]
  refine ⟨231359340284296810089191369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154239560189531206726127579 231359340284296810089191369)
  ·
    refine ⟨173519505213222607566893527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231359340284296810089191369 173519505213222607566893527)
    ·
      refine ⟨260279257819833911350340291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173519505213222607566893527 260279257819833911350340291)
      ·
        refine ⟨390418886729750867025510437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260279257819833911350340291 390418886729750867025510437)
        ·
          refine ⟨73203541261828287567283207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390418886729750867025510437 73203541261828287567283207)
          ·
            refine ⟨109805311892742431350924811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73203541261828287567283207 109805311892742431350924811)
            ·
              refine ⟨164707967839113647026387217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109805311892742431350924811 164707967839113647026387217)
              ·
                refine ⟨123530975879335235269790413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164707967839113647026387217 123530975879335235269790413)
                ·
                  refine ⟨46324115954750713226171405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123530975879335235269790413 46324115954750713226171405)
                  ·
                    refine ⟨17371543483031517459814277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46324115954750713226171405 17371543483031517459814277)
                    ·
                      refine ⟨3257164403068409523715177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17371543483031517459814277 3257164403068409523715177)
                      ·
                        rfl

theorem cell23_6343305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_6343305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343305 prefixEnd_6343305 := by exact prefixLift 6343305
  have htrace : WordTrace (prefixWord ++ tailWord_6343305) baseStart_6343305 baseEnd_6343305 := by
    simpa [prefixWord, tailWord_6343305, baseEnd_6343305] using wordTrace_append hprefix tailTrace_6343305
  have hstable : (prefixWord ++ tailWord_6343305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343305).length < 2 ^ (prefixWord ++ tailWord_6343305).sum := by decide
  have hdescent : baseEnd_6343305 < baseStart_6343305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343400 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6343400 : Nat := 118140960795 + 6343400 * 2 ^ 59
def prefixEnd_6343400 : Nat := 4983230072969 + 3 ^ 40 * 6343400 * 2
def baseEnd_6343400 : Nat := 1085737727910195550675747

theorem tailTrace_6343400 : CollatzResearch.WordTrace tailWord_6343400 prefixEnd_6343400 1085737727910195550675747 := by
  unfold tailWord_6343400
  simp only [CollatzResearch.WordTrace]
  refine ⟨115681402609476320656949827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154241870145968427542599769 115681402609476320656949827)
  ·
    refine ⟨173522103914214480985424741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115681402609476320656949827 173522103914214480985424741)
    ·
      refine ⟨32535394483915215184767139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173522103914214480985424741 32535394483915215184767139)
      ·
        refine ⟨48803091725872822777150709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32535394483915215184767139 48803091725872822777150709)
        ·
          refine ⟨4575289849300577135357879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48803091725872822777150709 4575289849300577135357879)
          ·
            refine ⟨6862934773950865703036819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575289849300577135357879 6862934773950865703036819)
            ·
              refine ⟨10294402160926298554555229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862934773950865703036819 10294402160926298554555229)
              ·
                refine ⟨3860400810347361957958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10294402160926298554555229 3860400810347361957958211)
                ·
                  refine ⟨5790601215521042936937317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860400810347361957958211 5790601215521042936937317)
                  ·
                    refine ⟨1085737727910195550675747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790601215521042936937317 1085737727910195550675747)
                    ·
                      rfl

theorem cell23_6343400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6343400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343400 prefixEnd_6343400 := by exact prefixLift 6343400
  have htrace : WordTrace (prefixWord ++ tailWord_6343400) baseStart_6343400 baseEnd_6343400 := by
    simpa [prefixWord, tailWord_6343400, baseEnd_6343400] using wordTrace_append hprefix tailTrace_6343400
  have hstable : (prefixWord ++ tailWord_6343400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343400).length < 2 ^ (prefixWord ++ tailWord_6343400).sum := by decide
  have hdescent : baseEnd_6343400 < baseStart_6343400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343439 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 2, 4]
def baseStart_6343439 : Nat := 118140960795 + 6343439 * 2 ^ 59
def prefixEnd_6343439 : Nat := 4983230072969 + 3 ^ 40 * 6343439 * 2
def baseEnd_6343439 : Nat := 1085744403158703999813187

theorem tailTrace_6343439 : CollatzResearch.WordTrace tailWord_6343439 prefixEnd_6343439 1085744403158703999813187 := by
  unfold tailWord_6343439
  simp only [CollatzResearch.WordTrace]
  refine ⟨231364227665811350974569371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154242818443874233983046247 231364227665811350974569371)
  ·
    refine ⟨347046341498717026461854057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231364227665811350974569371 347046341498717026461854057)
    ·
      refine ⟨260284756124037769846390543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347046341498717026461854057 260284756124037769846390543)
      ·
        refine ⟨390427134186056654769585815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260284756124037769846390543 390427134186056654769585815)
        ·
          refine ⟨585640701279084982154378723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390427134186056654769585815 585640701279084982154378723)
          ·
            refine ⟨878461051918627473231568085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585640701279084982154378723 878461051918627473231568085)
            ·
              refine ⟨20588930904342831403864877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 878461051918627473231568085 20588930904342831403864877)
              ·
                refine ⟨7720849089128561776449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20588930904342831403864877 7720849089128561776449329)
                ·
                  refine ⟨5790636816846421332336997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720849089128561776449329 5790636816846421332336997)
                  ·
                    refine ⟨1085744403158703999813187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790636816846421332336997 1085744403158703999813187)
                    ·
                      rfl

theorem cell23_6343439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_6343439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343439 prefixEnd_6343439 := by exact prefixLift 6343439
  have htrace : WordTrace (prefixWord ++ tailWord_6343439) baseStart_6343439 baseEnd_6343439 := by
    simpa [prefixWord, tailWord_6343439, baseEnd_6343439] using wordTrace_append hprefix tailTrace_6343439
  have hstable : (prefixWord ++ tailWord_6343439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343439).length < 2 ^ (prefixWord ++ tailWord_6343439).sum := by decide
  have hdescent : baseEnd_6343439 < baseStart_6343439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343449 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_6343449 : Nat := 118140960795 + 6343449 * 2 ^ 59
def prefixEnd_6343449 : Nat := 4983230072969 + 3 ^ 40 * 6343449 * 2
def baseEnd_6343449 : Nat := 3257238344282656960314515

theorem tailTrace_6343449 : CollatzResearch.WordTrace tailWord_6343449 prefixEnd_6343449 3257238344282656960314515 := by
  unfold tailWord_6343449
  simp only [CollatzResearch.WordTrace]
  refine ⟨231364592395775122682433401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154243061597183415121622267 231364592395775122682433401)
  ·
    refine ⟨173523444296831342011825051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231364592395775122682433401 173523444296831342011825051)
    ·
      refine ⟨260285166445247013017737577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173523444296831342011825051 260285166445247013017737577)
      ·
        refine ⟨195213874833935259763303183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260285166445247013017737577 195213874833935259763303183)
        ·
          refine ⟨292820812250902889644954775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195213874833935259763303183 292820812250902889644954775)
          ·
            refine ⟨439231218376354334467432163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292820812250902889644954775 439231218376354334467432163)
            ·
              refine ⟨658846827564531501701148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439231218376354334467432163 658846827564531501701148245)
              ·
                refine ⟨7720861260521853535560331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 658846827564531501701148245 7720861260521853535560331)
                ·
                  refine ⟨11581291890782780303340497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7720861260521853535560331 11581291890782780303340497)
                  ·
                    refine ⟨8685968918087085227505373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11581291890782780303340497 8685968918087085227505373)
                    ·
                      refine ⟨3257238344282656960314515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8685968918087085227505373 3257238344282656960314515)
                      ·
                        rfl

theorem cell23_6343449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_6343449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343449 prefixEnd_6343449 := by exact prefixLift 6343449
  have htrace : WordTrace (prefixWord ++ tailWord_6343449) baseStart_6343449 baseEnd_6343449 := by
    simpa [prefixWord, tailWord_6343449, baseEnd_6343449] using wordTrace_append hprefix tailTrace_6343449
  have hstable : (prefixWord ++ tailWord_6343449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343449).length < 2 ^ (prefixWord ++ tailWord_6343449).sum := by decide
  have hdescent : baseEnd_6343449 < baseStart_6343449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343452 : List Nat := [2, 2, 3, 1, 1, 3, 2, 9]
def baseStart_6343452 : Nat := 118140960795 + 6343452 * 2 ^ 59
def prefixEnd_6343452 : Nat := 4983230072969 + 3 ^ 40 * 6343452 * 2
def baseEnd_6343452 : Nat := 120638514249060016613963

theorem tailTrace_6343452 : CollatzResearch.WordTrace tailWord_6343452 prefixEnd_6343452 120638514249060016613963 := by
  unfold tailWord_6343452
  simp only [CollatzResearch.WordTrace]
  refine ⟨115682350907382127097396305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154243134543176169463195073 115682350907382127097396305)
  ·
    refine ⟨86761763180536595323047229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115682350907382127097396305 86761763180536595323047229)
    ·
      refine ⟨32535661192701223246142711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86761763180536595323047229 32535661192701223246142711)
      ·
        refine ⟨48803491789051834869214067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32535661192701223246142711 48803491789051834869214067)
        ·
          refine ⟨73205237683577752303821101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48803491789051834869214067 73205237683577752303821101)
          ·
            refine ⟨27451964131341657113932913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73205237683577752303821101 27451964131341657113932913)
            ·
              refine ⟨20588973098506242835449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27451964131341657113932913 20588973098506242835449685)
              ·
                refine ⟨120638514249060016613963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20588973098506242835449685 120638514249060016613963)
                ·
                  rfl

theorem cell23_6343452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 9].length) (baseStart_6343452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343452 prefixEnd_6343452 := by exact prefixLift 6343452
  have htrace : WordTrace (prefixWord ++ tailWord_6343452) baseStart_6343452 baseEnd_6343452 := by
    simpa [prefixWord, tailWord_6343452, baseEnd_6343452] using wordTrace_append hprefix tailTrace_6343452
  have hstable : (prefixWord ++ tailWord_6343452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343452).length < 2 ^ (prefixWord ++ tailWord_6343452).sum := by decide
  have hdescent : baseEnd_6343452 < baseStart_6343452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343469 : List Nat := [1, 5, 3, 2, 12]
def baseStart_6343469 : Nat := 118140960795 + 6343469 * 2 ^ 59
def prefixEnd_6343469 : Nat := 4983230072969 + 3 ^ 40 * 6343469 * 2
def baseEnd_6343469 : Nat := 4468105094507197369087

theorem tailTrace_6343469 : CollatzResearch.WordTrace tailWord_6343469 prefixEnd_6343469 4468105094507197369087 := by
  unfold tailWord_6343469
  simp only [CollatzResearch.WordTrace]
  refine ⟨231365321855702666098161461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154243547903801777398774307 231365321855702666098161461)
  ·
    refine ⟨21690498923972124946702637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231365321855702666098161461 21690498923972124946702637)
    ·
      refine ⟨8133937096489546855013489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21690498923972124946702637 8133937096489546855013489)
      ·
        refine ⟨6100452822367160141260117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8133937096489546855013489 6100452822367160141260117)
        ·
          refine ⟨4468105094507197369087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6100452822367160141260117 4468105094507197369087)
          ·
            rfl

theorem cell23_6343469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 12].length) (baseStart_6343469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343469 prefixEnd_6343469 := by exact prefixLift 6343469
  have htrace : WordTrace (prefixWord ++ tailWord_6343469) baseStart_6343469 baseEnd_6343469 := by
    simpa [prefixWord, tailWord_6343469, baseEnd_6343469] using wordTrace_append hprefix tailTrace_6343469
  have hstable : (prefixWord ++ tailWord_6343469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343469).length < 2 ^ (prefixWord ++ tailWord_6343469).sum := by decide
  have hdescent : baseEnd_6343469 < baseStart_6343469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343486 : List Nat := [4, 2, 1, 2, 3, 2, 1, 8]
def baseStart_6343486 : Nat := 118140960795 + 6343486 * 2 ^ 59
def prefixEnd_6343486 : Nat := 4983230072969 + 3 ^ 40 * 6343486 * 2
def baseEnd_6343486 : Nat := 120639160854328641316735

theorem tailTrace_6343486 : CollatzResearch.WordTrace tailWord_6343486 prefixEnd_6343486 120639160854328641316735 := by
  unfold tailWord_6343486
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920742737080134750191289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154243961264427385334353541 28920742737080134750191289)
  ·
    refine ⟨21690557052810101062643467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28920742737080134750191289 21690557052810101062643467)
    ·
      refine ⟨32535835579215151593965201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21690557052810101062643467 32535835579215151593965201)
      ·
        refine ⟨24401876684411363695473901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32535835579215151593965201 24401876684411363695473901)
        ·
          refine ⟨9150703756654261385802713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24401876684411363695473901 9150703756654261385802713)
          ·
            refine ⟨6863027817490696039352035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9150703756654261385802713 6863027817490696039352035)
            ·
              refine ⟨10294541726236044059028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863027817490696039352035 10294541726236044059028053)
              ·
                refine ⟨120639160854328641316735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10294541726236044059028053 120639160854328641316735)
                ·
                  rfl

theorem cell23_6343486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_6343486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343486 prefixEnd_6343486 := by exact prefixLift 6343486
  have htrace : WordTrace (prefixWord ++ tailWord_6343486) baseStart_6343486 baseEnd_6343486 := by
    simpa [prefixWord, tailWord_6343486, baseEnd_6343486] using wordTrace_append hprefix tailTrace_6343486
  have hstable : (prefixWord ++ tailWord_6343486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343486).length < 2 ^ (prefixWord ++ tailWord_6343486).sum := by decide
  have hdescent : baseEnd_6343486 < baseStart_6343486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343496 : List Nat := [2, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_6343496 : Nat := 118140960795 + 6343496 * 2 ^ 59
def prefixEnd_6343496 : Nat := 4983230072969 + 3 ^ 40 * 6343496 * 2
def baseEnd_6343496 : Nat := 3257262477873418276426799

theorem tailTrace_6343496 : CollatzResearch.WordTrace tailWord_6343496 prefixEnd_6343496 3257262477873418276426799 := by
  unfold tailWord_6343496
  simp only [CollatzResearch.WordTrace]
  refine ⟨115683153313302424854697171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154244204417736566472929561 115683153313302424854697171)
  ·
    refine ⟨173524729969953637282045757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115683153313302424854697171 173524729969953637282045757)
    ·
      refine ⟨65071773738732613980767159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173524729969953637282045757 65071773738732613980767159)
      ·
        refine ⟨97607660608098920971150739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65071773738732613980767159 97607660608098920971150739)
        ·
          refine ⟨146411490912148381456726109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97607660608098920971150739 146411490912148381456726109)
          ·
            refine ⟨54904309092055643046272291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146411490912148381456726109 54904309092055643046272291)
            ·
              refine ⟨82356463638083464569408437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54904309092055643046272291 82356463638083464569408437)
              ·
                refine ⟨7720918466070324803382041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82356463638083464569408437 7720918466070324803382041)
                ·
                  refine ⟨5790688849552743602536531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720918466070324803382041 5790688849552743602536531)
                  ·
                    refine ⟨8686033274329115403804797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790688849552743602536531 8686033274329115403804797)
                    ·
                      refine ⟨3257262477873418276426799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8686033274329115403804797 3257262477873418276426799)
                      ·
                        rfl

theorem cell23_6343496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_6343496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343496 prefixEnd_6343496 := by exact prefixLift 6343496
  have htrace : WordTrace (prefixWord ++ tailWord_6343496) baseStart_6343496 baseEnd_6343496 := by
    simpa [prefixWord, tailWord_6343496, baseEnd_6343496] using wordTrace_append hprefix tailTrace_6343496
  have hstable : (prefixWord ++ tailWord_6343496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343496).length < 2 ^ (prefixWord ++ tailWord_6343496).sum := by decide
  have hdescent : baseEnd_6343496 < baseStart_6343496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343506 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_6343506 : Nat := 118140960795 + 6343506 * 2 ^ 59
def prefixEnd_6343506 : Nat := 4983230072969 + 3 ^ 40 * 6343506 * 2
def baseEnd_6343506 : Nat := 3257267612679963237301753

theorem tailTrace_6343506 : CollatzResearch.WordTrace tailWord_6343506 prefixEnd_6343506 3257267612679963237301753 := by
  unfold tailWord_6343506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57841667839142155354314593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154244447571045747611505581 57841667839142155354314593)
  ·
    refine ⟨43381250879356616515735945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57841667839142155354314593 43381250879356616515735945)
    ·
      refine ⟨32535938159517462386801959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43381250879356616515735945 32535938159517462386801959)
      ·
        refine ⟨48803907239276193580202939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32535938159517462386801959 48803907239276193580202939)
        ·
          refine ⟨73205860858914290370304409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48803907239276193580202939 73205860858914290370304409)
          ·
            refine ⟨54904395644185717777728307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73205860858914290370304409 54904395644185717777728307)
            ·
              refine ⟨82356593466278576666592461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54904395644185717777728307 82356593466278576666592461)
              ·
                refine ⟨30883722549854466249972173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82356593466278576666592461 30883722549854466249972173)
                ·
                  refine ⟨11581395956195424843739565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30883722549854466249972173 11581395956195424843739565)
                  ·
                    refine ⟨4343023483573284316402337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11581395956195424843739565 4343023483573284316402337)
                    ·
                      refine ⟨3257267612679963237301753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343023483573284316402337 3257267612679963237301753)
                      ·
                        rfl

theorem cell23_6343506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_6343506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343506 prefixEnd_6343506 := by exact prefixLift 6343506
  have htrace : WordTrace (prefixWord ++ tailWord_6343506) baseStart_6343506 baseEnd_6343506 := by
    simpa [prefixWord, tailWord_6343506, baseEnd_6343506] using wordTrace_append hprefix tailTrace_6343506
  have hstable : (prefixWord ++ tailWord_6343506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343506).length < 2 ^ (prefixWord ++ tailWord_6343506).sum := by decide
  have hdescent : baseEnd_6343506 < baseStart_6343506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343523 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 1, 3, 2]
def baseStart_6343523 : Nat := 118140960795 + 6343523 * 2 ^ 59
def prefixEnd_6343523 : Nat := 4983230072969 + 3 ^ 40 * 6343523 * 2
def baseEnd_6343523 : Nat := 3257276341851089670789175

theorem tailTrace_6343523 : CollatzResearch.WordTrace tailWord_6343523 prefixEnd_6343523 3257276341851089670789175 := by
  unfold tailWord_6343523
  simp only [CollatzResearch.WordTrace]
  refine ⟨231367291397507033320627223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154244860931671355547084815 231367291397507033320627223)
  ·
    refine ⟨347050937096260549980940835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231367291397507033320627223 347050937096260549980940835)
    ·
      refine ⟨520576405644390824971411253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347050937096260549980940835 520576405644390824971411253)
      ·
        refine ⟨48804038029161639841069805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 520576405644390824971411253 48804038029161639841069805)
        ·
          refine ⟨18301514260935614940401177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48804038029161639841069805 18301514260935614940401177)
          ·
            refine ⟨13726135695701711205300883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18301514260935614940401177 13726135695701711205300883)
            ·
              refine ⟨20589203543552566807951325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13726135695701711205300883 20589203543552566807951325)
              ·
                refine ⟨7720951328832212552981747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20589203543552566807951325 7720951328832212552981747)
                ·
                  refine ⟨11581426993248318829472621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7720951328832212552981747 11581426993248318829472621)
                  ·
                    refine ⟨4343035122468119561052233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11581426993248318829472621 4343035122468119561052233)
                    ·
                      refine ⟨3257276341851089670789175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343035122468119561052233 3257276341851089670789175)
                      ·
                        rfl

theorem cell23_6343523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_6343523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343523 prefixEnd_6343523 := by exact prefixLift 6343523
  have htrace : WordTrace (prefixWord ++ tailWord_6343523) baseStart_6343523 baseEnd_6343523 := by
    simpa [prefixWord, tailWord_6343523, baseEnd_6343523] using wordTrace_append hprefix tailTrace_6343523
  have hstable : (prefixWord ++ tailWord_6343523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343523).length < 2 ^ (prefixWord ++ tailWord_6343523).sum := by decide
  have hdescent : baseEnd_6343523 < baseStart_6343523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343549 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_6343549 : Nat := 118140960795 + 6343549 * 2 ^ 59
def prefixEnd_6343549 : Nat := 4983230072969 + 3 ^ 40 * 6343549 * 2
def baseEnd_6343549 : Nat := 3257289692348106569064055

theorem tailTrace_6343549 : CollatzResearch.WordTrace tailWord_6343549 prefixEnd_6343549 3257289692348106569064055 := by
  unfold tailWord_6343549
  simp only [CollatzResearch.WordTrace]
  refine ⟨231368239695412839761073701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154245493130275226507382467 231368239695412839761073701)
  ·
    refine ⟨43381544942889907455201319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231368239695412839761073701 43381544942889907455201319)
    ·
      refine ⟨65072317414334861182801979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43381544942889907455201319 65072317414334861182801979)
      ·
        refine ⟨97608476121502291774202969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65072317414334861182801979 97608476121502291774202969)
        ·
          refine ⟨73206357091126718830652227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97608476121502291774202969 73206357091126718830652227)
          ·
            refine ⟨109809535636690078245978341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73206357091126718830652227 109809535636690078245978341)
            ·
              refine ⟨20589287931879389671120939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109809535636690078245978341 20589287931879389671120939)
              ·
                refine ⟨30883931897819084506681409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20589287931879389671120939 30883931897819084506681409)
                ·
                  refine ⟨23162948923364313380011057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30883931897819084506681409 23162948923364313380011057)
                  ·
                    refine ⟨17372211692523235035008293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23162948923364313380011057 17372211692523235035008293)
                    ·
                      refine ⟨3257289692348106569064055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17372211692523235035008293 3257289692348106569064055)
                      ·
                        rfl

theorem cell23_6343549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_6343549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343549 prefixEnd_6343549 := by exact prefixLift 6343549
  have htrace : WordTrace (prefixWord ++ tailWord_6343549) baseStart_6343549 baseEnd_6343549 := by
    simpa [prefixWord, tailWord_6343549, baseEnd_6343549] using wordTrace_append hprefix tailTrace_6343549
  have hstable : (prefixWord ++ tailWord_6343549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343549).length < 2 ^ (prefixWord ++ tailWord_6343549).sum := by decide
  have hdescent : baseEnd_6343549 < baseStart_6343549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343559 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 7]
def baseStart_6343559 : Nat := 118140960795 + 6343559 * 2 ^ 59
def prefixEnd_6343559 : Nat := 4983230072969 + 3 ^ 40 * 6343559 * 2
def baseEnd_6343559 : Nat := 361921647461627947771001

theorem tailTrace_6343559 : CollatzResearch.WordTrace tailWord_6343559 prefixEnd_6343559 361921647461627947771001 := by
  unfold tailWord_6343559
  simp only [CollatzResearch.WordTrace]
  refine ⟨231368604425376611468937731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154245736283584407645958487 231368604425376611468937731)
  ·
    refine ⟨347052906638064917203406597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231368604425376611468937731 347052906638064917203406597)
    ·
      refine ⟨65072419994637171975638737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347052906638064917203406597 65072419994637171975638737)
      ·
        refine ⟨48804314995977878981729053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65072419994637171975638737 48804314995977878981729053)
        ·
          refine ⟨18301618123491704618148395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48804314995977878981729053 18301618123491704618148395)
          ·
            refine ⟨27452427185237556927222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18301618123491704618148395 27452427185237556927222593)
            ·
              refine ⟨20589320388928167695416945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27452427185237556927222593 20589320388928167695416945)
              ·
                refine ⟨15441990291696125771562709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20589320388928167695416945 15441990291696125771562709)
                ·
                  refine ⟨361921647461627947771001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15441990291696125771562709 361921647461627947771001)
                  ·
                    rfl

theorem cell23_6343559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 7].length) (baseStart_6343559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343559 prefixEnd_6343559 := by exact prefixLift 6343559
  have htrace : WordTrace (prefixWord ++ tailWord_6343559) baseStart_6343559 baseEnd_6343559 := by
    simpa [prefixWord, tailWord_6343559, baseEnd_6343559] using wordTrace_append hprefix tailTrace_6343559
  have hstable : (prefixWord ++ tailWord_6343559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343559).length < 2 ^ (prefixWord ++ tailWord_6343559).sum := by decide
  have hdescent : baseEnd_6343559 < baseStart_6343559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343604 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6343604 : Nat := 118140960795 + 6343604 * 2 ^ 59
def prefixEnd_6343604 : Nat := 4983230072969 + 3 ^ 40 * 6343604 * 2
def baseEnd_6343604 : Nat := 3257317933784103853876303

theorem tailTrace_6343604 : CollatzResearch.WordTrace tailWord_6343604 prefixEnd_6343604 3257317933784103853876303 := by
  unfold tailWord_6343604
  simp only [CollatzResearch.WordTrace]
  refine ⟨115685122855106792077162933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154246830473475722769550577 115685122855106792077162933)
  ·
    refine ⟨10845480267666261757234025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115685122855106792077162933 10845480267666261757234025)
    ·
      refine ⟨8134110200749696317925519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10845480267666261757234025 8134110200749696317925519)
      ·
        refine ⟨12201165301124544476888279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8134110200749696317925519 12201165301124544476888279)
        ·
          refine ⟨18301747951686816715332419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12201165301124544476888279 18301747951686816715332419)
          ·
            refine ⟨27452621927530225072998629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18301747951686816715332419 27452621927530225072998629)
            ·
              refine ⟨5147366611411917201187243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27452621927530225072998629 5147366611411917201187243)
              ·
                refine ⟨7721049917117875801780865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147366611411917201187243 7721049917117875801780865)
                ·
                  refine ⟨5790787437838406851335649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721049917117875801780865 5790787437838406851335649)
                  ·
                    refine ⟨4343090578378805138501737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5790787437838406851335649 4343090578378805138501737)
                    ·
                      refine ⟨3257317933784103853876303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343090578378805138501737 3257317933784103853876303)
                      ·
                        rfl

theorem cell23_6343604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6343604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343604 prefixEnd_6343604 := by exact prefixLift 6343604
  have htrace : WordTrace (prefixWord ++ tailWord_6343604) baseStart_6343604 baseEnd_6343604 := by
    simpa [prefixWord, tailWord_6343604, baseEnd_6343604] using wordTrace_append hprefix tailTrace_6343604
  have hstable : (prefixWord ++ tailWord_6343604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343604).length < 2 ^ (prefixWord ++ tailWord_6343604).sum := by decide
  have hdescent : baseEnd_6343604 < baseStart_6343604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_6343626 : Nat := 118140960795 + 6343626 * 2 ^ 59
def prefixEnd_6343626 : Nat := 4983230072969 + 3 ^ 40 * 6343626 * 2
def baseEnd_6343626 : Nat := 3257329230358502767801201

theorem tailTrace_6343626 : CollatzResearch.WordTrace tailWord_6343626 prefixEnd_6343626 3257329230358502767801201 := by
  unfold tailWord_6343626
  simp only [CollatzResearch.WordTrace]
  refine ⟨57842762029033470477906683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154247365410755921274417821 57842762029033470477906683)
  ·
    refine ⟨86764143043550205716860025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57842762029033470477906683 86764143043550205716860025)
    ·
      refine ⟨65073107282662654287645019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86764143043550205716860025 65073107282662654287645019)
      ·
        refine ⟨97609660923993981431467529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65073107282662654287645019 97609660923993981431467529)
        ·
          refine ⟨73207245692995486073600647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97609660923993981431467529 73207245692995486073600647)
          ·
            refine ⟨109810868539493229110400971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73207245692995486073600647 109810868539493229110400971)
            ·
              refine ⟨164716302809239843665601457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109810868539493229110400971 164716302809239843665601457)
              ·
                refine ⟨123537227106929882749201093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164716302809239843665601457 123537227106929882749201093)
                ·
                  refine ⟨23163230082549353015475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123537227106929882749201093 23163230082549353015475205)
                  ·
                    refine ⟨4343105640478003690401601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23163230082549353015475205 4343105640478003690401601)
                    ·
                      refine ⟨3257329230358502767801201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343105640478003690401601 3257329230358502767801201)
                      ·
                        rfl

theorem cell23_6343626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_6343626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343626 prefixEnd_6343626 := by exact prefixLift 6343626
  have htrace : WordTrace (prefixWord ++ tailWord_6343626) baseStart_6343626 baseEnd_6343626 := by
    simpa [prefixWord, tailWord_6343626, baseEnd_6343626] using wordTrace_append hprefix tailTrace_6343626
  have hstable : (prefixWord ++ tailWord_6343626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343626).length < 2 ^ (prefixWord ++ tailWord_6343626).sum := by decide
  have hdescent : baseEnd_6343626 < baseStart_6343626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343659 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3]
def baseStart_6343659 : Nat := 118140960795 + 6343659 * 2 ^ 59
def prefixEnd_6343659 : Nat := 4983230072969 + 3 ^ 40 * 6343659 * 2
def baseEnd_6343659 : Nat := 3257346175220101138688549

theorem tailTrace_6343659 : CollatzResearch.WordTrace tailWord_6343659 prefixEnd_6343659 3257346175220101138688549 := by
  unfold tailWord_6343659
  simp only [CollatzResearch.WordTrace]
  refine ⟨231372251725014328547578031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154248167816676219031718687 231372251725014328547578031)
  ·
    refine ⟨347058377587521492821367047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231372251725014328547578031 347058377587521492821367047)
    ·
      refine ⟨520587566381282239232050571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347058377587521492821367047 520587566381282239232050571)
      ·
        refine ⟨780881349571923358848075857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520587566381282239232050571 780881349571923358848075857)
        ·
          refine ⟨585661012178942519136056893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780881349571923358848075857 585661012178942519136056893)
          ·
            refine ⟨219622879567103444676021335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585661012178942519136056893 219622879567103444676021335)
            ·
              refine ⟨329434319350655167014032003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219622879567103444676021335 329434319350655167014032003)
              ·
                refine ⟨494151479025982750521048005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329434319350655167014032003 494151479025982750521048005)
                ·
                  refine ⟨92653402317371765722696501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494151479025982750521048005 92653402317371765722696501)
                  ·
                    refine ⟨8686256467253603036502797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92653402317371765722696501 8686256467253603036502797)
                    ·
                      refine ⟨3257346175220101138688549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8686256467253603036502797 3257346175220101138688549)
                      ·
                        rfl

theorem cell23_6343659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].length) (baseStart_6343659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343659 prefixEnd_6343659 := by exact prefixLift 6343659
  have htrace : WordTrace (prefixWord ++ tailWord_6343659) baseStart_6343659 baseEnd_6343659 := by
    simpa [prefixWord, tailWord_6343659, baseEnd_6343659] using wordTrace_append hprefix tailTrace_6343659
  have hstable : (prefixWord ++ tailWord_6343659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343659).length < 2 ^ (prefixWord ++ tailWord_6343659).sum := by decide
  have hdescent : baseEnd_6343659 < baseStart_6343659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343759 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_6343759 : Nat := 118140960795 + 6343759 * 2 ^ 59
def prefixEnd_6343759 : Nat := 4983230072969 + 3 ^ 40 * 6343759 * 2
def baseEnd_6343759 : Nat := 3257397523285550747438089

theorem tailTrace_6343759 : CollatzResearch.WordTrace tailWord_6343759 prefixEnd_6343759 3257397523285550747438089 := by
  unfold tailWord_6343759
  simp only [CollatzResearch.WordTrace]
  refine ⟨231375899024652045626218331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154250599349768030417478887 231375899024652045626218331)
  ·
    refine ⟨347063848536978068439327497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231375899024652045626218331 347063848536978068439327497)
    ·
      refine ⟨260297886402733551329495623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347063848536978068439327497 260297886402733551329495623)
      ·
        refine ⟨390446829604100326994243435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260297886402733551329495623 390446829604100326994243435)
        ·
          refine ⟨585670244406150490491365153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390446829604100326994243435 585670244406150490491365153)
          ·
            refine ⟨439252683304612867868523865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585670244406150490491365153 439252683304612867868523865)
            ·
              refine ⟨329439512478459650901392899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439252683304612867868523865 329439512478459650901392899)
              ·
                refine ⟨494159268717689476352089349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329439512478459650901392899 494159268717689476352089349)
                ·
                  refine ⟨92654862884566776816016753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494159268717689476352089349 92654862884566776816016753)
                  ·
                    refine ⟨69491147163425082612012565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92654862884566776816016753 69491147163425082612012565)
                    ·
                      refine ⟨3257397523285550747438089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69491147163425082612012565 3257397523285550747438089)
                      ·
                        rfl

theorem cell23_6343759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_6343759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343759 prefixEnd_6343759 := by exact prefixLift 6343759
  have htrace : WordTrace (prefixWord ++ tailWord_6343759) baseStart_6343759 baseEnd_6343759 := by
    simpa [prefixWord, tailWord_6343759, baseEnd_6343759] using wordTrace_append hprefix tailTrace_6343759
  have hstable : (prefixWord ++ tailWord_6343759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343759).length < 2 ^ (prefixWord ++ tailWord_6343759).sum := by decide
  have hdescent : baseEnd_6343759 < baseStart_6343759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343784 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6343784 : Nat := 118140960795 + 6343784 * 2 ^ 59
def prefixEnd_6343784 : Nat := 4983230072969 + 3 ^ 40 * 6343784 * 2
def baseEnd_6343784 : Nat := 3257410360301913149625475

theorem tailTrace_6343784 : CollatzResearch.WordTrace tailWord_6343784 prefixEnd_6343784 3257410360301913149625475 := by
  unfold tailWord_6343784
  simp only [CollatzResearch.WordTrace]
  refine ⟨115688405424780737447939203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154251207233040983263918937 115688405424780737447939203)
  ·
    refine ⟨173532608137171106171908805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115688405424780737447939203 173532608137171106171908805)
    ·
      refine ⟨32537364025719582407232901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173532608137171106171908805 32537364025719582407232901)
      ·
        refine ⟨6100755754822421701356169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32537364025719582407232901 6100755754822421701356169)
        ·
          refine ⟨4575566816116816276017127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6100755754822421701356169 4575566816116816276017127)
          ·
            refine ⟨6863350224175224414025691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575566816116816276017127 6863350224175224414025691)
            ·
              refine ⟨10295025336262836621038537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863350224175224414025691 10295025336262836621038537)
              ·
                refine ⟨7721269002197127465778903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10295025336262836621038537 7721269002197127465778903)
                ·
                  refine ⟨11581903503295691198668355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721269002197127465778903 11581903503295691198668355)
                  ·
                    refine ⟨17372855254943536798002533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11581903503295691198668355 17372855254943536798002533)
                    ·
                      refine ⟨3257410360301913149625475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17372855254943536798002533 3257410360301913149625475)
                      ·
                        rfl

theorem cell23_6343784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6343784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343784 prefixEnd_6343784 := by exact prefixLift 6343784
  have htrace : WordTrace (prefixWord ++ tailWord_6343784) baseStart_6343784 baseEnd_6343784 := by
    simpa [prefixWord, tailWord_6343784, baseEnd_6343784] using wordTrace_append hprefix tailTrace_6343784
  have hstable : (prefixWord ++ tailWord_6343784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343784).length < 2 ^ (prefixWord ++ tailWord_6343784).sum := by decide
  have hdescent : baseEnd_6343784 < baseStart_6343784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343840 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2]
def baseStart_6343840 : Nat := 118140960795 + 6343840 * 2 ^ 59
def prefixEnd_6343840 : Nat := 4983230072969 + 3 ^ 40 * 6343840 * 2
def baseEnd_6343840 : Nat := 3257439115218564930525217

theorem tailTrace_6343840 : CollatzResearch.WordTrace tailWord_6343840 prefixEnd_6343840 3257439115218564930525217 := by
  unfold tailWord_6343840
  simp only [CollatzResearch.WordTrace]
  refine ⟨115689426668679298229958487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154252568891572397639944649 115689426668679298229958487)
  ·
    refine ⟨173534140003018947344937731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115689426668679298229958487 173534140003018947344937731)
    ·
      refine ⟨260301210004528421017406597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173534140003018947344937731 260301210004528421017406597)
      ·
        refine ⟨48806476875849078940763737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260301210004528421017406597 48806476875849078940763737)
        ·
          refine ⟨36604857656886809205572803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48806476875849078940763737 36604857656886809205572803)
          ·
            refine ⟨54907286485330213808359205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36604857656886809205572803 54907286485330213808359205)
            ·
              refine ⟨10295116215999415089067351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54907286485330213808359205 10295116215999415089067351)
              ·
                refine ⟨15442674323999122633601027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10295116215999415089067351 15442674323999122633601027)
                ·
                  refine ⟨23164011485998683950401541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15442674323999122633601027 23164011485998683950401541)
                  ·
                    refine ⟨4343252153624753240700289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23164011485998683950401541 4343252153624753240700289)
                    ·
                      refine ⟨3257439115218564930525217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343252153624753240700289 3257439115218564930525217)
                      ·
                        rfl

theorem cell23_6343840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_6343840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343840 prefixEnd_6343840 := by exact prefixLift 6343840
  have htrace : WordTrace (prefixWord ++ tailWord_6343840) baseStart_6343840 baseEnd_6343840 := by
    simpa [prefixWord, tailWord_6343840, baseEnd_6343840] using wordTrace_append hprefix tailTrace_6343840
  have hstable : (prefixWord ++ tailWord_6343840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343840).length < 2 ^ (prefixWord ++ tailWord_6343840).sum := by decide
  have hdescent : baseEnd_6343840 < baseStart_6343840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343883 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 5, 2]
def baseStart_6343883 : Nat := 118140960795 + 6343883 * 2 ^ 59
def prefixEnd_6343883 : Nat := 4983230072969 + 3 ^ 40 * 6343883 * 2
def baseEnd_6343883 : Nat := 3257461194886708262287519

theorem tailTrace_6343883 : CollatzResearch.WordTrace tailWord_6343883 prefixEnd_6343883 3257461194886708262287519 := by
  unfold tailWord_6343883
  simp only [CollatzResearch.WordTrace]
  refine ⟨231380421676202814803732303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154253614450801876535821535 231380421676202814803732303)
  ·
    refine ⟨347070632514304222205598455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231380421676202814803732303 347070632514304222205598455)
    ·
      refine ⟨520605948771456333308397683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347070632514304222205598455 520605948771456333308397683)
      ·
        refine ⟨780908923157184499962596525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520605948771456333308397683 780908923157184499962596525)
        ·
          refine ⟨292840846183944187485973697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 780908923157184499962596525 292840846183944187485973697)
          ·
            refine ⟨219630634637958140614480273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292840846183944187485973697 219630634637958140614480273)
            ·
              refine ⟨164722975978468605460860205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219630634637958140614480273 164722975978468605460860205)
              ·
                refine ⟨61771115991925727047822577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164722975978468605460860205 61771115991925727047822577)
                ·
                  refine ⟨46328336993944295285866933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61771115991925727047822577 46328336993944295285866933)
                  ·
                    refine ⟨4343281593182277683050025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46328336993944295285866933 4343281593182277683050025)
                    ·
                      refine ⟨3257461194886708262287519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343281593182277683050025 3257461194886708262287519)
                      ·
                        rfl

theorem cell23_6343883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5, 2].length) (baseStart_6343883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343883 prefixEnd_6343883 := by exact prefixLift 6343883
  have htrace : WordTrace (prefixWord ++ tailWord_6343883) baseStart_6343883 baseEnd_6343883 := by
    simpa [prefixWord, tailWord_6343883, baseEnd_6343883] using wordTrace_append hprefix tailTrace_6343883
  have hstable : (prefixWord ++ tailWord_6343883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343883).length < 2 ^ (prefixWord ++ tailWord_6343883).sum := by decide
  have hdescent : baseEnd_6343883 < baseStart_6343883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343893 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_6343893 : Nat := 118140960795 + 6343893 * 2 ^ 59
def prefixEnd_6343893 : Nat := 4983230072969 + 3 ^ 40 * 6343893 * 2
def baseEnd_6343893 : Nat := 1085822109897751074387491

theorem tailTrace_6343893 : CollatzResearch.WordTrace tailWord_6343893 prefixEnd_6343893 1085822109897751074387491 := by
  unfold tailWord_6343893
  simp only [CollatzResearch.WordTrace]
  refine ⟨231380786406166586511596333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154253857604111057674397555 231380786406166586511596333)
  ·
    refine ⟨86767794902312469941848625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231380786406166586511596333 86767794902312469941848625)
    ·
      refine ⟨65075846176734352456386469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86767794902312469941848625 65075846176734352456386469)
      ·
        refine ⟨12201721158137691085572463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65075846176734352456386469 12201721158137691085572463)
        ·
          refine ⟨18302581737206536628358695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12201721158137691085572463 18302581737206536628358695)
          ·
            refine ⟨27453872605809804942538043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18302581737206536628358695 27453872605809804942538043)
            ·
              refine ⟨41180808908714707413807065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27453872605809804942538043 41180808908714707413807065)
              ·
                refine ⟨30885606681536030560355299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41180808908714707413807065 30885606681536030560355299)
                ·
                  refine ⟨46328410022304045840532949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30885606681536030560355299 46328410022304045840532949)
                  ·
                    refine ⟨1085822109897751074387491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46328410022304045840532949 1085822109897751074387491)
                    ·
                      rfl

theorem cell23_6343893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_6343893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343893 prefixEnd_6343893 := by exact prefixLift 6343893
  have htrace : WordTrace (prefixWord ++ tailWord_6343893) baseStart_6343893 baseEnd_6343893 := by
    simpa [prefixWord, tailWord_6343893, baseEnd_6343893] using wordTrace_append hprefix tailTrace_6343893
  have hstable : (prefixWord ++ tailWord_6343893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343893).length < 2 ^ (prefixWord ++ tailWord_6343893).sum := by decide
  have hdescent : baseEnd_6343893 < baseStart_6343893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343953 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 6]
def baseStart_6343953 : Nat := 118140960795 + 6343953 * 2 ^ 59
def prefixEnd_6343953 : Nat := 4983230072969 + 3 ^ 40 * 6343953 * 2
def baseEnd_6343953 : Nat := 361944126503613665379133

theorem tailTrace_6343953 : CollatzResearch.WordTrace tailWord_6343953 prefixEnd_6343953 361944126503613665379133 := by
  unfold tailWord_6343953
  simp only [CollatzResearch.WordTrace]
  refine ⟨231382974785949216758780513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154255316523966144505853675 231382974785949216758780513)
  ·
    refine ⟨173537231089461912569085385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231382974785949216758780513 173537231089461912569085385)
    ·
      refine ⟨130152923317096434426814039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173537231089461912569085385 130152923317096434426814039)
      ·
        refine ⟨195229384975644651640221059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130152923317096434426814039 195229384975644651640221059)
        ·
          refine ⟨292844077463466977460331589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195229384975644651640221059 292844077463466977460331589)
          ·
            refine ⟨54908264524400058273812173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292844077463466977460331589 54908264524400058273812173)
            ·
              refine ⟨20590599196650021852679565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54908264524400058273812173 20590599196650021852679565)
              ·
                refine ⟨7721474698743758194754837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20590599196650021852679565 7721474698743758194754837)
                ·
                  refine ⟨361944126503613665379133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7721474698743758194754837 361944126503613665379133)
                  ·
                    rfl

theorem cell23_6343953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 6].length) (baseStart_6343953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343953 prefixEnd_6343953 := by exact prefixLift 6343953
  have htrace : WordTrace (prefixWord ++ tailWord_6343953) baseStart_6343953 baseEnd_6343953 := by
    simpa [prefixWord, tailWord_6343953, baseEnd_6343953] using wordTrace_append hprefix tailTrace_6343953
  have hstable : (prefixWord ++ tailWord_6343953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343953).length < 2 ^ (prefixWord ++ tailWord_6343953).sum := by decide
  have hdescent : baseEnd_6343953 < baseStart_6343953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6343967 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_6343967 : Nat := 118140960795 + 6343967 * 2 ^ 59
def prefixEnd_6343967 : Nat := 4983230072969 + 3 ^ 40 * 6343967 * 2
def baseEnd_6343967 : Nat := 3257504327261685933637133

theorem tailTrace_6343967 : CollatzResearch.WordTrace tailWord_6343967 prefixEnd_6343967 3257504327261685933637133 := by
  unfold tailWord_6343967
  simp only [CollatzResearch.WordTrace]
  refine ⟨231383485407898497149790155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154255656938598998099860103 231383485407898497149790155)
  ·
    refine ⟨347075228111847745724685233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231383485407898497149790155 347075228111847745724685233)
    ·
      refine ⟨260306421083885809293513925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347075228111847745724685233 260306421083885809293513925)
      ·
        refine ⟨48807453953228589242533861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260306421083885809293513925 48807453953228589242533861)
        ·
          refine ⟨9151397616230360482975099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48807453953228589242533861 9151397616230360482975099)
          ·
            refine ⟨13727096424345540724462649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151397616230360482975099 13727096424345540724462649)
            ·
              refine ⟨10295322318259155543346987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727096424345540724462649 10295322318259155543346987)
              ·
                refine ⟨15442983477388733315020481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10295322318259155543346987 15442983477388733315020481)
                ·
                  refine ⟨11582237608041549986265361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15442983477388733315020481 11582237608041549986265361)
                  ·
                    refine ⟨8686678206031162489699021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11582237608041549986265361 8686678206031162489699021)
                    ·
                      refine ⟨3257504327261685933637133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8686678206031162489699021 3257504327261685933637133)
                      ·
                        rfl

theorem cell23_6343967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_6343967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6343967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6343967 prefixEnd_6343967 := by exact prefixLift 6343967
  have htrace : WordTrace (prefixWord ++ tailWord_6343967) baseStart_6343967 baseEnd_6343967 := by
    simpa [prefixWord, tailWord_6343967, baseEnd_6343967] using wordTrace_append hprefix tailTrace_6343967
  have hstable : (prefixWord ++ tailWord_6343967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6343967).length < 2 ^ (prefixWord ++ tailWord_6343967).sum := by decide
  have hdescent : baseEnd_6343967 < baseStart_6343967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6343967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344020 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6344020 : Nat := 118140960795 + 6344020 * 2 ^ 59
def prefixEnd_6344020 : Nat := 4983230072969 + 3 ^ 40 * 6344020 * 2
def baseEnd_6344020 : Nat := 3257531541736374226274389

theorem tailTrace_6344020 : CollatzResearch.WordTrace tailWord_6344020 prefixEnd_6344020 3257531541736374226274389 := by
  unfold tailWord_6344020
  simp only [CollatzResearch.WordTrace]
  refine ⟨115692709238353243600734757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154256945651137658134313009 115692709238353243600734757)
  ·
    refine ⟨21692382982191233175137767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115692709238353243600734757 21692382982191233175137767)
    ·
      refine ⟨32538574473286849762706651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21692382982191233175137767 32538574473286849762706651)
      ·
        refine ⟨48807861709930274644059977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32538574473286849762706651 48807861709930274644059977)
        ·
          refine ⟨36605896282447705983044983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48807861709930274644059977 36605896282447705983044983)
          ·
            refine ⟨54908844423671558974567475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36605896282447705983044983 54908844423671558974567475)
            ·
              refine ⟨82363266635507338461851213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54908844423671558974567475 82363266635507338461851213)
              ·
                refine ⟨30886224988315251923194205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82363266635507338461851213 30886224988315251923194205)
                ·
                  refine ⟨11582334370618219471197827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30886224988315251923194205 11582334370618219471197827)
                  ·
                    refine ⟨17373501555927329206796741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11582334370618219471197827 17373501555927329206796741)
                    ·
                      refine ⟨3257531541736374226274389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17373501555927329206796741 3257531541736374226274389)
                      ·
                        rfl

theorem cell23_6344020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6344020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344020 prefixEnd_6344020 := by exact prefixLift 6344020
  have htrace : WordTrace (prefixWord ++ tailWord_6344020) baseStart_6344020 baseEnd_6344020 := by
    simpa [prefixWord, tailWord_6344020, baseEnd_6344020] using wordTrace_append hprefix tailTrace_6344020
  have hstable : (prefixWord ++ tailWord_6344020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344020).length < 2 ^ (prefixWord ++ tailWord_6344020).sum := by decide
  have hdescent : baseEnd_6344020 < baseStart_6344020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344037 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6344037 : Nat := 118140960795 + 6344037 * 2 ^ 59
def prefixEnd_6344037 : Nat := 4983230072969 + 3 ^ 40 * 6344037 * 2
def baseEnd_6344037 : Nat := 3257540270907500659761811

theorem tailTrace_6344037 : CollatzResearch.WordTrace tailWord_6344037 prefixEnd_6344037 3257540270907500659761811 := by
  unfold tailWord_6344037
  simp only [CollatzResearch.WordTrace]
  refine ⟨231386038517644899104838365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154257359011763266069892243 231386038517644899104838365)
  ·
    refine ⟨86769764444116837164314387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231386038517644899104838365 86769764444116837164314387)
    ·
      refine ⟨130154646666175255746471581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86769764444116837164314387 130154646666175255746471581)
      ·
        refine ⟨48807992499815720904926843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130154646666175255746471581 48807992499815720904926843)
        ·
          refine ⟨73211988749723581357390265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48807992499815720904926843 73211988749723581357390265)
          ·
            refine ⟨54908991562292686018042699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73211988749723581357390265 54908991562292686018042699)
            ·
              refine ⟨82363487343439029027064049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54908991562292686018042699 82363487343439029027064049)
              ·
                refine ⟨61772615507579271770298037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82363487343439029027064049 61772615507579271770298037)
                ·
                  refine ⟨5791182703835556728465441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61772615507579271770298037 5791182703835556728465441)
                  ·
                    refine ⟨4343387027876667546349081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791182703835556728465441 4343387027876667546349081)
                    ·
                      refine ⟨3257540270907500659761811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343387027876667546349081 3257540270907500659761811)
                      ·
                        rfl

theorem cell23_6344037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6344037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344037 prefixEnd_6344037 := by exact prefixLift 6344037
  have htrace : WordTrace (prefixWord ++ tailWord_6344037) baseStart_6344037 baseEnd_6344037 := by
    simpa [prefixWord, tailWord_6344037, baseEnd_6344037] using wordTrace_append hprefix tailTrace_6344037
  have hstable : (prefixWord ++ tailWord_6344037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344037).length < 2 ^ (prefixWord ++ tailWord_6344037).sum := by decide
  have hdescent : baseEnd_6344037 < baseStart_6344037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344067 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 4]
def baseStart_6344067 : Nat := 118140960795 + 6344067 * 2 ^ 59
def prefixEnd_6344067 : Nat := 4983230072969 + 3 ^ 40 * 6344067 * 2
def baseEnd_6344067 : Nat := 3257555675327135542386673

theorem tailTrace_6344067 : CollatzResearch.WordTrace tailWord_6344067 prefixEnd_6344067 3257555675327135542386673 := by
  unfold tailWord_6344067
  simp only [CollatzResearch.WordTrace]
  refine ⟨231387132707536214228430455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154258088471690809485620303 231387132707536214228430455)
  ·
    refine ⟨347080699061304321342645683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231387132707536214228430455 347080699061304321342645683)
    ·
      refine ⟨520621048591956482013968525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347080699061304321342645683 520621048591956482013968525)
      ·
        refine ⟨195232893221983680755238197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520621048591956482013968525 195232893221983680755238197)
        ·
          refine ⟨18303083739560970070803581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195232893221983680755238197 18303083739560970070803581)
          ·
            refine ⟨6863656402335363776551343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18303083739560970070803581 6863656402335363776551343)
            ·
              refine ⟨10295484603503045664827015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863656402335363776551343 10295484603503045664827015)
              ·
                refine ⟨15443226905254568497240523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10295484603503045664827015 15443226905254568497240523)
                ·
                  refine ⟨23164840357881852745860785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15443226905254568497240523 23164840357881852745860785)
                  ·
                    refine ⟨17373630268411389559395589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23164840357881852745860785 17373630268411389559395589)
                    ·
                      refine ⟨3257555675327135542386673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17373630268411389559395589 3257555675327135542386673)
                      ·
                        rfl

theorem cell23_6344067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_6344067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344067 prefixEnd_6344067 := by exact prefixLift 6344067
  have htrace : WordTrace (prefixWord ++ tailWord_6344067) baseStart_6344067 baseEnd_6344067 := by
    simpa [prefixWord, tailWord_6344067, baseEnd_6344067] using wordTrace_append hprefix tailTrace_6344067
  have hstable : (prefixWord ++ tailWord_6344067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344067).length < 2 ^ (prefixWord ++ tailWord_6344067).sum := by decide
  have hdescent : baseEnd_6344067 < baseStart_6344067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344094 : List Nat := [4, 3, 1, 2, 3, 1, 9]
def baseStart_6344094 : Nat := 118140960795 + 6344094 * 2 ^ 59
def prefixEnd_6344094 : Nat := 4983230072969 + 3 ^ 40 * 6344094 * 2
def baseEnd_6344094 : Nat := 40216907892651937490729

theorem tailTrace_6344094 : CollatzResearch.WordTrace tailWord_6344094 prefixEnd_6344094 40216907892651937490729 := by
  unfold tailWord_6344094
  simp only [CollatzResearch.WordTrace]
  refine ⟨28923514684804799729957917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154258744985625598559775557 28923514684804799729957917)
  ·
    refine ⟨10846318006801799898734219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28923514684804799729957917 10846318006801799898734219)
    ·
      refine ⟨16269477010202699848101329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10846318006801799898734219 16269477010202699848101329)
      ·
        refine ⟨12202107757652024886075997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16269477010202699848101329 12202107757652024886075997)
        ·
          refine ⟨4575790409119509332278499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12202107757652024886075997 4575790409119509332278499)
          ·
            refine ⟨6863685613679263998417749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575790409119509332278499 6863685613679263998417749)
            ·
              refine ⟨40216907892651937490729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6863685613679263998417749 40216907892651937490729)
              ·
                rfl

theorem cell23_6344094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 9].length) (baseStart_6344094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344094 prefixEnd_6344094 := by exact prefixLift 6344094
  have htrace : WordTrace (prefixWord ++ tailWord_6344094) baseStart_6344094 baseEnd_6344094 := by
    simpa [prefixWord, tailWord_6344094, baseEnd_6344094] using wordTrace_append hprefix tailTrace_6344094
  have hstable : (prefixWord ++ tailWord_6344094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344094).length < 2 ^ (prefixWord ++ tailWord_6344094).sum := by decide
  have hdescent : baseEnd_6344094 < baseStart_6344094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344148 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6344148 : Nat := 118140960795 + 6344148 * 2 ^ 59
def prefixEnd_6344148 : Nat := 4983230072969 + 3 ^ 40 * 6344148 * 2
def baseEnd_6344148 : Nat := 3257597267260149725473801

theorem tailTrace_6344148 : CollatzResearch.WordTrace tailWord_6344148 prefixEnd_6344148 3257597267260149725473801 := by
  unfold tailWord_6344148
  simp only [CollatzResearch.WordTrace]
  refine ⟨115695043510121382531064549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154260058013495176708086065 115695043510121382531064549)
  ·
    refine ⟨21692820658147759224574603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115695043510121382531064549 21692820658147759224574603)
    ·
      refine ⟨32539230987221638836861905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21692820658147759224574603 32539230987221638836861905)
      ·
        refine ⟨24404423240416229127646429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32539230987221638836861905 24404423240416229127646429)
        ·
          refine ⟨9151658715156085922867411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24404423240416229127646429 9151658715156085922867411)
          ·
            refine ⟨13727488072734128884301117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151658715156085922867411 13727488072734128884301117)
            ·
              refine ⟨5147808027275298331612919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13727488072734128884301117 5147808027275298331612919)
              ·
                refine ⟨7721712040912947497419379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147808027275298331612919 7721712040912947497419379)
                ·
                  refine ⟨11582568061369421246129069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721712040912947497419379 11582568061369421246129069)
                  ·
                    refine ⟨4343463023013532967298401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11582568061369421246129069 4343463023013532967298401)
                    ·
                      refine ⟨3257597267260149725473801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343463023013532967298401 3257597267260149725473801)
                      ·
                        rfl

theorem cell23_6344148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6344148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344148 prefixEnd_6344148 := by exact prefixLift 6344148
  have htrace : WordTrace (prefixWord ++ tailWord_6344148) baseStart_6344148 baseEnd_6344148 := by
    simpa [prefixWord, tailWord_6344148, baseEnd_6344148] using wordTrace_append hprefix tailTrace_6344148
  have hstable : (prefixWord ++ tailWord_6344148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344148).length < 2 ^ (prefixWord ++ tailWord_6344148).sum := by decide
  have hdescent : baseEnd_6344148 < baseStart_6344148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344161 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_6344161 : Nat := 118140960795 + 6344161 * 2 ^ 59
def prefixEnd_6344161 : Nat := 4983230072969 + 3 ^ 40 * 6344161 * 2
def baseEnd_6344161 : Nat := 3257603942508658174611241

theorem tailTrace_6344161 : CollatzResearch.WordTrace tailWord_6344161 prefixEnd_6344161 3257603942508658174611241 := by
  unfold tailWord_6344161
  simp only [CollatzResearch.WordTrace]
  refine ⟨231390561169195668282352337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154260374112797112188234891 231390561169195668282352337)
  ·
    refine ⟨173542920876896751211764253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231390561169195668282352337 173542920876896751211764253)
    ·
      refine ⟨65078595328836281704411595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173542920876896751211764253 65078595328836281704411595)
      ·
        refine ⟨97617892993254422556617393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65078595328836281704411595 97617892993254422556617393)
        ·
          refine ⟨73213419744940816917463045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97617892993254422556617393 73213419744940816917463045)
          ·
            refine ⟨13727516202176403172024321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73213419744940816917463045 13727516202176403172024321)
            ·
              refine ⟨10295637151632302379018241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727516202176403172024321 10295637151632302379018241)
              ·
                refine ⟨7721727863724226784263681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10295637151632302379018241 7721727863724226784263681)
                ·
                  refine ⟨5791295897793170088197761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721727863724226784263681 5791295897793170088197761)
                  ·
                    refine ⟨4343471923344877566148321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791295897793170088197761 4343471923344877566148321)
                    ·
                      refine ⟨3257603942508658174611241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343471923344877566148321 3257603942508658174611241)
                      ·
                        rfl

theorem cell23_6344161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_6344161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344161 prefixEnd_6344161 := by exact prefixLift 6344161
  have htrace : WordTrace (prefixWord ++ tailWord_6344161) baseStart_6344161 baseEnd_6344161 := by
    simpa [prefixWord, tailWord_6344161, baseEnd_6344161] using wordTrace_append hprefix tailTrace_6344161
  have hstable : (prefixWord ++ tailWord_6344161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344161).length < 2 ^ (prefixWord ++ tailWord_6344161).sum := by decide
  have hdescent : baseEnd_6344161 < baseStart_6344161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344177 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_6344177 : Nat := 118140960795 + 6344177 * 2 ^ 59
def prefixEnd_6344177 : Nat := 4983230072969 + 3 ^ 40 * 6344177 * 2
def baseEnd_6344177 : Nat := 3257612158199130112011167

theorem tailTrace_6344177 : CollatzResearch.WordTrace tailWord_6344177 prefixEnd_6344177 3257612158199130112011167 := by
  unfold tailWord_6344177
  simp only [CollatzResearch.WordTrace]
  refine ⟨231391144737137703014934785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154260763158091802009956523 231391144737137703014934785)
  ·
    refine ⟨173543358552853277261201089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231391144737137703014934785 173543358552853277261201089)
    ·
      refine ⟨130157518914639957945900817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173543358552853277261201089 130157518914639957945900817)
      ·
        refine ⟨97618139185979968459425613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130157518914639957945900817 97618139185979968459425613)
        ·
          refine ⟨36606802194742488172284605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97618139185979968459425613 36606802194742488172284605)
          ·
            refine ⟨13727550823028433064606727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36606802194742488172284605 13727550823028433064606727)
            ·
              refine ⟨20591326234542649596910091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727550823028433064606727 20591326234542649596910091)
              ·
                refine ⟨30886989351813974395365137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20591326234542649596910091 30886989351813974395365137)
                ·
                  refine ⟨23165242013860480796523853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30886989351813974395365137 23165242013860480796523853)
                  ·
                    refine ⟨8686965755197680298696445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23165242013860480796523853 8686965755197680298696445)
                    ·
                      refine ⟨3257612158199130112011167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8686965755197680298696445 3257612158199130112011167)
                      ·
                        rfl

theorem cell23_6344177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_6344177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344177 prefixEnd_6344177 := by exact prefixLift 6344177
  have htrace : WordTrace (prefixWord ++ tailWord_6344177) baseStart_6344177 baseEnd_6344177 := by
    simpa [prefixWord, tailWord_6344177, baseEnd_6344177] using wordTrace_append hprefix tailTrace_6344177
  have hstable : (prefixWord ++ tailWord_6344177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344177).length < 2 ^ (prefixWord ++ tailWord_6344177).sum := by decide
  have hdescent : baseEnd_6344177 < baseStart_6344177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344212 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6344212 : Nat := 118140960795 + 6344212 * 2 ^ 59
def prefixEnd_6344212 : Nat := 4983230072969 + 3 ^ 40 * 6344212 * 2
def baseEnd_6344212 : Nat := 3257630130022037475073507

theorem tailTrace_6344212 : CollatzResearch.WordTrace tailWord_6344212 prefixEnd_6344212 3257630130022037475073507 := by
  unfold tailWord_6344212
  simp only [CollatzResearch.WordTrace]
  refine ⟨115696210646005451996229445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154261614194673935994972593 115696210646005451996229445)
  ·
    refine ⟨21693039496126022249293021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115696210646005451996229445 21693039496126022249293021)
    ·
      refine ⟨8134889811047258343484883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21693039496126022249293021 8134889811047258343484883)
      ·
        refine ⟨12202334716570887515227325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8134889811047258343484883 12202334716570887515227325)
        ·
          refine ⟨4575875518714082818210247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12202334716570887515227325 4575875518714082818210247)
          ·
            refine ⟨6863813278071124227315371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575875518714082818210247 6863813278071124227315371)
            ·
              refine ⟨10295719917106686340973057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863813278071124227315371 10295719917106686340973057)
              ·
                refine ⟨7721789937830014755729793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10295719917106686340973057 7721789937830014755729793)
                ·
                  refine ⟨5791342453372511066797345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721789937830014755729793 5791342453372511066797345)
                  ·
                    refine ⟨4343506840029383300098009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791342453372511066797345 4343506840029383300098009)
                    ·
                      refine ⟨3257630130022037475073507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343506840029383300098009 3257630130022037475073507)
                      ·
                        rfl

theorem cell23_6344212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6344212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344212 prefixEnd_6344212 := by exact prefixLift 6344212
  have htrace : WordTrace (prefixWord ++ tailWord_6344212) baseStart_6344212 baseEnd_6344212 := by
    simpa [prefixWord, tailWord_6344212, baseEnd_6344212] using wordTrace_append hprefix tailTrace_6344212
  have hstable : (prefixWord ++ tailWord_6344212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344212).length < 2 ^ (prefixWord ++ tailWord_6344212).sum := by decide
  have hdescent : baseEnd_6344212 < baseStart_6344212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344234 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6344234 : Nat := 118140960795 + 6344234 * 2 ^ 59
def prefixEnd_6344234 : Nat := 4983230072969 + 3 ^ 40 * 6344234 * 2
def baseEnd_6344234 : Nat := 3257641426596436388998405

theorem tailTrace_6344234 : CollatzResearch.WordTrace tailWord_6344234 prefixEnd_6344234 3257641426596436388998405 := by
  unfold tailWord_6344234
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848305924482800437439939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154262149131954134499839837 57848305924482800437439939)
  ·
    refine ⟨86772458886724200656159909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848305924482800437439939 86772458886724200656159909)
    ·
      refine ⟨16269836041260787623029983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86772458886724200656159909 16269836041260787623029983)
      ·
        refine ⟨24404754061891181434544975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16269836041260787623029983 24404754061891181434544975)
        ·
          refine ⟨36607131092836772151817463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24404754061891181434544975 36607131092836772151817463)
          ·
            refine ⟨54910696639255158227726195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36607131092836772151817463 54910696639255158227726195)
            ·
              refine ⟨82366044958882737341589293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54910696639255158227726195 82366044958882737341589293)
              ·
                refine ⟨30887266859581026503095985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82366044958882737341589293 30887266859581026503095985)
                ·
                  refine ⟨23165450144685769877321989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30887266859581026503095985 23165450144685769877321989)
                  ·
                    refine ⟨4343521902128581851997873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23165450144685769877321989 4343521902128581851997873)
                    ·
                      refine ⟨3257641426596436388998405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343521902128581851997873 3257641426596436388998405)
                      ·
                        rfl

theorem cell23_6344234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6344234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344234 prefixEnd_6344234 := by exact prefixLift 6344234
  have htrace : WordTrace (prefixWord ++ tailWord_6344234) baseStart_6344234 baseEnd_6344234 := by
    simpa [prefixWord, tailWord_6344234, baseEnd_6344234] using wordTrace_append hprefix tailTrace_6344234
  have hstable : (prefixWord ++ tailWord_6344234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344234).length < 2 ^ (prefixWord ++ tailWord_6344234).sum := by decide
  have hdescent : baseEnd_6344234 < baseStart_6344234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344280 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6344280 : Nat := 118140960795 + 6344280 * 2 ^ 59
def prefixEnd_6344280 : Nat := 4983230072969 + 3 ^ 40 * 6344280 * 2
def baseEnd_6344280 : Nat := 3257665046706543209023193

theorem tailTrace_6344280 : CollatzResearch.WordTrace tailWord_6344280 prefixEnd_6344280 3257665046706543209023193 := by
  unfold tailWord_6344280
  simp only [CollatzResearch.WordTrace]
  refine ⟨115697450727882275802967147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154263267637176367737289529 115697450727882275802967147)
  ·
    refine ⟨173546176091823413704450721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115697450727882275802967147 173546176091823413704450721)
    ·
      refine ⟨130159632068867560278338041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173546176091823413704450721 130159632068867560278338041)
      ·
        refine ⟨97619724051650670208753531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130159632068867560278338041 97619724051650670208753531)
        ·
          refine ⟨146429586077476005313130297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97619724051650670208753531 146429586077476005313130297)
          ·
            refine ⟨109822189558107003984847723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146429586077476005313130297 109822189558107003984847723)
            ·
              refine ⟨164733284337160505977271585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109822189558107003984847723 164733284337160505977271585)
              ·
                refine ⟨123549963252870379482953689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164733284337160505977271585 123549963252870379482953689)
                ·
                  refine ⟨92662472439652784612215267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123549963252870379482953689 92662472439652784612215267)
                  ·
                    refine ⟨138993708659479176918322901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92662472439652784612215267 138993708659479176918322901)
                    ·
                      refine ⟨3257665046706543209023193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138993708659479176918322901 3257665046706543209023193)
                      ·
                        rfl

theorem cell23_6344280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6344280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344280 prefixEnd_6344280 := by exact prefixLift 6344280
  have htrace : WordTrace (prefixWord ++ tailWord_6344280) baseStart_6344280 baseEnd_6344280 := by
    simpa [prefixWord, tailWord_6344280, baseEnd_6344280] using wordTrace_append hprefix tailTrace_6344280
  have hstable : (prefixWord ++ tailWord_6344280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344280).length < 2 ^ (prefixWord ++ tailWord_6344280).sum := by decide
  have hdescent : baseEnd_6344280 < baseStart_6344280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344304 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_6344304 : Nat := 118140960795 + 6344304 * 2 ^ 59
def prefixEnd_6344304 : Nat := 4983230072969 + 3 ^ 40 * 6344304 * 2
def baseEnd_6344304 : Nat := 1085892456747417038374361

theorem tailTrace_6344304 : CollatzResearch.WordTrace tailWord_6344304 prefixEnd_6344304 1085892456747417038374361 := by
  unfold tailWord_6344304
  simp only [CollatzResearch.WordTrace]
  refine ⟨115697888403838801852403983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154263851205118402469871977 115697888403838801852403983)
  ·
    refine ⟨173546832605758202778605975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115697888403838801852403983 173546832605758202778605975)
    ·
      refine ⟨260320248908637304167908963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173546832605758202778605975 260320248908637304167908963)
      ·
        refine ⟨390480373362955956251863445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260320248908637304167908963 390480373362955956251863445)
        ·
          refine ⟨18303767501388560449306099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 390480373362955956251863445 18303767501388560449306099)
          ·
            refine ⟨27455651252082840673959149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18303767501388560449306099 27455651252082840673959149)
            ·
              refine ⟨10295869219531065252734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27455651252082840673959149 10295869219531065252734681)
              ·
                refine ⟨7721901914648298939551011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10295869219531065252734681 7721901914648298939551011)
                ·
                  refine ⟨11582852871972448409326517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721901914648298939551011 11582852871972448409326517)
                  ·
                    refine ⟨1085892456747417038374361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11582852871972448409326517 1085892456747417038374361)
                    ·
                      rfl

theorem cell23_6344304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_6344304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344304 prefixEnd_6344304 := by exact prefixLift 6344304
  have htrace : WordTrace (prefixWord ++ tailWord_6344304) baseStart_6344304 baseEnd_6344304 := by
    simpa [prefixWord, tailWord_6344304, baseEnd_6344304] using wordTrace_append hprefix tailTrace_6344304
  have hstable : (prefixWord ++ tailWord_6344304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344304).length < 2 ^ (prefixWord ++ tailWord_6344304).sum := by decide
  have hdescent : baseEnd_6344304 < baseStart_6344304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344317 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_6344317 : Nat := 118140960795 + 6344317 * 2 ^ 59
def prefixEnd_6344317 : Nat := 4983230072969 + 3 ^ 40 * 6344317 * 2
def baseEnd_6344317 : Nat := 1085894681830253188086841

theorem tailTrace_6344317 : CollatzResearch.WordTrace tailWord_6344317 prefixEnd_6344317 1085894681830253188086841 := by
  unfold tailWord_6344317
  simp only [CollatzResearch.WordTrace]
  refine ⟨231396250956630506925031205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154264167304420337950020803 231396250956630506925031205)
  ·
    refine ⟨43386797054368220048443351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231396250956630506925031205 43386797054368220048443351)
    ·
      refine ⟨65080195581552330072665027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43386797054368220048443351 65080195581552330072665027)
      ·
        refine ⟨97620293372328495108997541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65080195581552330072665027 97620293372328495108997541)
        ·
          refine ⟨18303805007311592832937039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97620293372328495108997541 18303805007311592832937039)
          ·
            refine ⟨27455707510967389249405559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18303805007311592832937039 27455707510967389249405559)
            ·
              refine ⟨41183561266451083874108339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27455707510967389249405559 41183561266451083874108339)
              ·
                refine ⟨61775341899676625811162509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41183561266451083874108339 61775341899676625811162509)
                ·
                  refine ⟨23165753212378734679185941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61775341899676625811162509 23165753212378734679185941)
                  ·
                    refine ⟨1085894681830253188086841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23165753212378734679185941 1085894681830253188086841)
                    ·
                      rfl

theorem cell23_6344317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_6344317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344317 prefixEnd_6344317 := by exact prefixLift 6344317
  have htrace : WordTrace (prefixWord ++ tailWord_6344317) baseStart_6344317 baseEnd_6344317 := by
    simpa [prefixWord, tailWord_6344317, baseEnd_6344317] using wordTrace_append hprefix tailTrace_6344317
  have hstable : (prefixWord ++ tailWord_6344317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344317).length < 2 ^ (prefixWord ++ tailWord_6344317).sum := by decide
  have hdescent : baseEnd_6344317 < baseStart_6344317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344321 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6344321 : Nat := 118140960795 + 6344321 * 2 ^ 59
def prefixEnd_6344321 : Nat := 4983230072969 + 3 ^ 40 * 6344321 * 2
def baseEnd_6344321 : Nat := 1085895366471125849536835

theorem tailTrace_6344321 : CollatzResearch.WordTrace tailWord_6344321 prefixEnd_6344321 1085895366471125849536835 := by
  unfold tailWord_6344321
  simp only [CollatzResearch.WordTrace]
  refine ⟨231396396848616015608176817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154264264565744010405451211 231396396848616015608176817)
  ·
    refine ⟨173547297636462011706132613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231396396848616015608176817 173547297636462011706132613)
    ·
      refine ⟨32540118306836627194899865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173547297636462011706132613 32540118306836627194899865)
      ·
        refine ⟨24405088730127470396174899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32540118306836627194899865 24405088730127470396174899)
        ·
          refine ⟨36607633095191205594262349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24405088730127470396174899 36607633095191205594262349)
          ·
            refine ⟨13727862410696702097848381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36607633095191205594262349 13727862410696702097848381)
            ·
              refine ⟨5147948404011263286693143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13727862410696702097848381 5147948404011263286693143)
              ·
                refine ⟨7721922606016894930039715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147948404011263286693143 7721922606016894930039715)
                ·
                  refine ⟨11582883909025342395059573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721922606016894930039715 11582883909025342395059573)
                  ·
                    refine ⟨1085895366471125849536835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11582883909025342395059573 1085895366471125849536835)
                    ·
                      rfl

theorem cell23_6344321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6344321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344321 prefixEnd_6344321 := by exact prefixLift 6344321
  have htrace : WordTrace (prefixWord ++ tailWord_6344321) baseStart_6344321 baseEnd_6344321 := by
    simpa [prefixWord, tailWord_6344321, baseEnd_6344321] using wordTrace_append hprefix tailTrace_6344321
  have hstable : (prefixWord ++ tailWord_6344321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344321).length < 2 ^ (prefixWord ++ tailWord_6344321).sum := by decide
  have hdescent : baseEnd_6344321 < baseStart_6344321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344344 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6344344 : Nat := 118140960795 + 6344344 * 2 ^ 59
def prefixEnd_6344344 : Nat := 4983230072969 + 3 ^ 40 * 6344344 * 2
def baseEnd_6344344 : Nat := 3257697909468430958622899

theorem tailTrace_6344344 : CollatzResearch.WordTrace tailWord_6344344 prefixEnd_6344344 3257697909468430958622899 := by
  unfold tailWord_6344344
  simp only [CollatzResearch.WordTrace]
  refine ⟨115698617863766345268132043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154264823818355127024176057 115698617863766345268132043)
  ·
    refine ⟨173547926795649517902198065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115698617863766345268132043 173547926795649517902198065)
    ·
      refine ⟨130160945096737138426648549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173547926795649517902198065 130160945096737138426648549)
      ·
        refine ⟨24405177205638213454996603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130160945096737138426648549 24405177205638213454996603)
        ·
          refine ⟨36607765808457320182494905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24405177205638213454996603 36607765808457320182494905)
          ·
            refine ⟨27455824356342990136871179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36607765808457320182494905 27455824356342990136871179)
            ·
              refine ⟨41183736534514485205306769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27455824356342990136871179 41183736534514485205306769)
              ·
                refine ⟨30887802400885863903980077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41183736534514485205306769 30887802400885863903980077)
                ·
                  refine ⟨11582925900332198963992529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30887802400885863903980077 11582925900332198963992529)
                  ·
                    refine ⟨8687194425249149222994397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11582925900332198963992529 8687194425249149222994397)
                    ·
                      refine ⟨3257697909468430958622899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687194425249149222994397 3257697909468430958622899)
                      ·
                        rfl

theorem cell23_6344344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6344344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344344 prefixEnd_6344344 := by exact prefixLift 6344344
  have htrace : WordTrace (prefixWord ++ tailWord_6344344) baseStart_6344344 baseEnd_6344344 := by
    simpa [prefixWord, tailWord_6344344, baseEnd_6344344] using wordTrace_append hprefix tailTrace_6344344
  have hstable : (prefixWord ++ tailWord_6344344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344344).length < 2 ^ (prefixWord ++ tailWord_6344344).sum := by decide
  have hdescent : baseEnd_6344344 < baseStart_6344344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344351 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 6]
def baseStart_6344351 : Nat := 118140960795 + 6344351 * 2 ^ 59
def prefixEnd_6344351 : Nat := 4983230072969 + 3 ^ 40 * 6344351 * 2
def baseEnd_6344351 : Nat := 1085900501277670810411789

theorem tailTrace_6344351 : CollatzResearch.WordTrace tailWord_6344351 prefixEnd_6344351 1085900501277670810411789 := by
  unfold tailWord_6344351
  simp only [CollatzResearch.WordTrace]
  refine ⟨231397491038507330731768907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154264994025671553821179271 231397491038507330731768907)
  ·
    refine ⟨347096236557760996097653361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231397491038507330731768907 347096236557760996097653361)
    ·
      refine ⟨260322177418320747073240021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347096236557760996097653361 260322177418320747073240021)
      ·
        refine ⟨6101301033241892509529063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 260322177418320747073240021 6101301033241892509529063)
        ·
          refine ⟨9151951549862838764293595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101301033241892509529063 9151951549862838764293595)
          ·
            refine ⟨13727927324794258146440393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151951549862838764293595 13727927324794258146440393)
            ·
              refine ⟨10295945493595693609830295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727927324794258146440393 10295945493595693609830295)
              ·
                refine ⟨15443918240393540414745443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10295945493595693609830295 15443918240393540414745443)
                ·
                  refine ⟨23165877360590310622118165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15443918240393540414745443 23165877360590310622118165)
                  ·
                    refine ⟨1085900501277670810411789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23165877360590310622118165 1085900501277670810411789)
                    ·
                      rfl

theorem cell23_6344351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_6344351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344351 prefixEnd_6344351 := by exact prefixLift 6344351
  have htrace : WordTrace (prefixWord ++ tailWord_6344351) baseStart_6344351 baseEnd_6344351 := by
    simpa [prefixWord, tailWord_6344351, baseEnd_6344351] using wordTrace_append hprefix tailTrace_6344351
  have hstable : (prefixWord ++ tailWord_6344351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344351).length < 2 ^ (prefixWord ++ tailWord_6344351).sum := by decide
  have hdescent : baseEnd_6344351 < baseStart_6344351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344375 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 1, 2, 2]
def baseStart_6344375 : Nat := 118140960795 + 6344375 * 2 ^ 59
def prefixEnd_6344375 : Nat := 4983230072969 + 3 ^ 40 * 6344375 * 2
def baseEnd_6344375 : Nat := 3257713827368720337335257

theorem tailTrace_6344375 : CollatzResearch.WordTrace tailWord_6344375 prefixEnd_6344375 3257713827368720337335257 := by
  unfold tailWord_6344375
  simp only [CollatzResearch.WordTrace]
  refine ⟨231398366390420382830642579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154265577593613588553761719 231398366390420382830642579)
  ·
    refine ⟨347097549585630574245963869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231398366390420382830642579 347097549585630574245963869)
    ·
      refine ⟨130161581094611465342236451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347097549585630574245963869 130161581094611465342236451)
      ·
        refine ⟨195242371641917198013354677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130161581094611465342236451 195242371641917198013354677)
        ·
          refine ⟨18303972341429737313752001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195242371641917198013354677 18303972341429737313752001)
          ·
            refine ⟨13727979256072302985314001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18303972341429737313752001 13727979256072302985314001)
            ·
              refine ⟨10295984442054227238985501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727979256072302985314001 10295984442054227238985501)
              ·
                refine ⟨3860994165770335214619563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10295984442054227238985501 3860994165770335214619563)
                ·
                  refine ⟨5791491248655502821929345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860994165770335214619563 5791491248655502821929345)
                  ·
                    refine ⟨4343618436491627116447009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791491248655502821929345 4343618436491627116447009)
                    ·
                      refine ⟨3257713827368720337335257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343618436491627116447009 3257713827368720337335257)
                      ·
                        rfl

theorem cell23_6344375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_6344375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344375 prefixEnd_6344375 := by exact prefixLift 6344375
  have htrace : WordTrace (prefixWord ++ tailWord_6344375) baseStart_6344375 baseEnd_6344375 := by
    simpa [prefixWord, tailWord_6344375, baseEnd_6344375] using wordTrace_append hprefix tailTrace_6344375
  have hstable : (prefixWord ++ tailWord_6344375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344375).length < 2 ^ (prefixWord ++ tailWord_6344375).sum := by decide
  have hdescent : baseEnd_6344375 < baseStart_6344375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344378 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_6344378 : Nat := 118140960795 + 6344378 * 2 ^ 59
def prefixEnd_6344378 : Nat := 4983230072969 + 3 ^ 40 * 6344378 * 2
def baseEnd_6344378 : Nat := 3257715367810683825597743

theorem tailTrace_6344378 : CollatzResearch.WordTrace tailWord_6344378 prefixEnd_6344378 3257715367810683825597743 := by
  unfold tailWord_6344378
  simp only [CollatzResearch.WordTrace]
  refine ⟨57849618952352378585750447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154265650539606342895334525 57849618952352378585750447)
  ·
    refine ⟨86774428428528567878625671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57849618952352378585750447 86774428428528567878625671)
    ·
      refine ⟨130161642642792851817938507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86774428428528567878625671 130161642642792851817938507)
      ·
        refine ⟨195242463964189277726907761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130161642642792851817938507 195242463964189277726907761)
        ·
          refine ⟨146431847973141958295180821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195242463964189277726907761 146431847973141958295180821)
          ·
            refine ⟨6863992873741029295086601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146431847973141958295180821 6863992873741029295086601)
            ·
              refine ⟨5147994655305771971314951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6863992873741029295086601 5147994655305771971314951)
              ·
                refine ⟨7721991982958657956972427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147994655305771971314951 7721991982958657956972427)
                ·
                  refine ⟨11582987974437986935458641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721991982958657956972427 11582987974437986935458641)
                  ·
                    refine ⟨8687240980828490201593981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11582987974437986935458641 8687240980828490201593981)
                    ·
                      refine ⟨3257715367810683825597743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687240980828490201593981 3257715367810683825597743)
                      ·
                        rfl

theorem cell23_6344378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_6344378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344378 prefixEnd_6344378 := by exact prefixLift 6344378
  have htrace : WordTrace (prefixWord ++ tailWord_6344378) baseStart_6344378 baseEnd_6344378 := by
    simpa [prefixWord, tailWord_6344378, baseEnd_6344378] using wordTrace_append hprefix tailTrace_6344378
  have hstable : (prefixWord ++ tailWord_6344378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344378).length < 2 ^ (prefixWord ++ tailWord_6344378).sum := by decide
  have hdescent : baseEnd_6344378 < baseStart_6344378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344407 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 6]
def baseStart_6344407 : Nat := 118140960795 + 6344407 * 2 ^ 59
def prefixEnd_6344407 : Nat := 4983230072969 + 3 ^ 40 * 6344407 * 2
def baseEnd_6344407 : Nat := 1085910086249888070711703

theorem tailTrace_6344407 : CollatzResearch.WordTrace tailWord_6344407 prefixEnd_6344407 1085910086249888070711703 := by
  unfold tailWord_6344407
  simp only [CollatzResearch.WordTrace]
  refine ⟨231399533526304452295807475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154266355684202968197204983 231399533526304452295807475)
  ·
    refine ⟨347099300289456678443711213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231399533526304452295807475 347099300289456678443711213)
    ·
      refine ⟨130162237608546254416391705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347099300289456678443711213 130162237608546254416391705)
      ·
        refine ⟨97621678206409690812293779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130162237608546254416391705 97621678206409690812293779)
        ·
          refine ⟨146432517309614536218440669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97621678206409690812293779 146432517309614536218440669)
          ·
            refine ⟨54912193991105451081915251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146432517309614536218440669 54912193991105451081915251)
            ·
              refine ⟨82368290986658176622872877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54912193991105451081915251 82368290986658176622872877)
              ·
                refine ⟨30888109119996816233577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82368290986658176622872877 30888109119996816233577329)
                ·
                  refine ⟨23166081839997612175182997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30888109119996816233577329 23166081839997612175182997)
                  ·
                    refine ⟨1085910086249888070711703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23166081839997612175182997 1085910086249888070711703)
                    ·
                      rfl

theorem cell23_6344407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_6344407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344407 prefixEnd_6344407 := by exact prefixLift 6344407
  have htrace : WordTrace (prefixWord ++ tailWord_6344407) baseStart_6344407 baseEnd_6344407 := by
    simpa [prefixWord, tailWord_6344407, baseEnd_6344407] using wordTrace_append hprefix tailTrace_6344407
  have hstable : (prefixWord ++ tailWord_6344407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344407).length < 2 ^ (prefixWord ++ tailWord_6344407).sum := by decide
  have hdescent : baseEnd_6344407 < baseStart_6344407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344408 : List Nat := [2, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_6344408 : Nat := 118140960795 + 6344408 * 2 ^ 59
def prefixEnd_6344408 : Nat := 4983230072969 + 3 ^ 40 * 6344408 * 2
def baseEnd_6344408 : Nat := 3257730772230318708222605

theorem tailTrace_6344408 : CollatzResearch.WordTrace tailWord_6344408 prefixEnd_6344408 3257730772230318708222605 := by
  unfold tailWord_6344408
  simp only [CollatzResearch.WordTrace]
  refine ⟨115699784999650414733296939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154266379999533886311062585 115699784999650414733296939)
  ·
    refine ⟨173549677499475622099945409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115699784999650414733296939 173549677499475622099945409)
    ·
      refine ⟨130162258124606716574959057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173549677499475622099945409 130162258124606716574959057)
      ·
        refine ⟨97621693593455037431219293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130162258124606716574959057 97621693593455037431219293)
        ·
          refine ⟨36608135097545639036707235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97621693593455037431219293 36608135097545639036707235)
          ·
            refine ⟨54912202646318458555060853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608135097545639036707235 54912202646318458555060853)
            ·
              refine ⟨5148018998092355489536955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54912202646318458555060853 5148018998092355489536955)
              ·
                refine ⟨7722028497138533234305433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5148018998092355489536955 7722028497138533234305433)
                ·
                  refine ⟨5791521372853899925729075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7722028497138533234305433 5791521372853899925729075)
                  ·
                    refine ⟨8687282059280849888593613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5791521372853899925729075 8687282059280849888593613)
                    ·
                      refine ⟨3257730772230318708222605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687282059280849888593613 3257730772230318708222605)
                      ·
                        rfl

theorem cell23_6344408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_6344408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344408 prefixEnd_6344408 := by exact prefixLift 6344408
  have htrace : WordTrace (prefixWord ++ tailWord_6344408) baseStart_6344408 baseEnd_6344408 := by
    simpa [prefixWord, tailWord_6344408, baseEnd_6344408] using wordTrace_append hprefix tailTrace_6344408
  have hstable : (prefixWord ++ tailWord_6344408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344408).length < 2 ^ (prefixWord ++ tailWord_6344408).sum := by decide
  have hdescent : baseEnd_6344408 < baseStart_6344408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344427 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_6344427 : Nat := 118140960795 + 6344427 * 2 ^ 59
def prefixEnd_6344427 : Nat := 4983230072969 + 3 ^ 40 * 6344427 * 2
def baseEnd_6344427 : Nat := 3257740528362754133885017

theorem tailTrace_6344427 : CollatzResearch.WordTrace tailWord_6344427 prefixEnd_6344427 3257740528362754133885017 := by
  unfold tailWord_6344427
  simp only [CollatzResearch.WordTrace]
  refine ⟨231400262986231995711535535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154266841990821330474357023 231400262986231995711535535)
  ·
    refine ⟨347100394479347993567303303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231400262986231995711535535 347100394479347993567303303)
    ·
      refine ⟨520650591719021990350954955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347100394479347993567303303 520650591719021990350954955)
      ·
        refine ⟨780975887578532985526432433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520650591719021990350954955 780975887578532985526432433)
        ·
          refine ⟨585731915683899739144824325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780975887578532985526432433 585731915683899739144824325)
          ·
            refine ⟨109824734190731201089654561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585731915683899739144824325 109824734190731201089654561)
            ·
              refine ⟨82368550643048400817240921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109824734190731201089654561 82368550643048400817240921)
              ·
                refine ⟨61776412982286300612930691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82368550643048400817240921 61776412982286300612930691)
                ·
                  refine ⟨92664619473429450919396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61776412982286300612930691 92664619473429450919396037)
                  ·
                    refine ⟨17374616151268022047386757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92664619473429450919396037 17374616151268022047386757)
                    ·
                      refine ⟨3257740528362754133885017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17374616151268022047386757 3257740528362754133885017)
                      ·
                        rfl

theorem cell23_6344427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_6344427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344427 prefixEnd_6344427 := by exact prefixLift 6344427
  have htrace : WordTrace (prefixWord ++ tailWord_6344427) baseStart_6344427 baseEnd_6344427 := by
    simpa [prefixWord, tailWord_6344427, baseEnd_6344427] using wordTrace_append hprefix tailTrace_6344427
  have hstable : (prefixWord ++ tailWord_6344427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344427).length < 2 ^ (prefixWord ++ tailWord_6344427).sum := by decide
  have hdescent : baseEnd_6344427 < baseStart_6344427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344431 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 6, 2, 2]
def baseStart_6344431 : Nat := 118140960795 + 6344431 * 2 ^ 59
def prefixEnd_6344431 : Nat := 4983230072969 + 3 ^ 40 * 6344431 * 2
def baseEnd_6344431 : Nat := 3257742582285372118234999

theorem tailTrace_6344431 : CollatzResearch.WordTrace tailWord_6344431 prefixEnd_6344431 3257742582285372118234999 := by
  unfold tailWord_6344431
  simp only [CollatzResearch.WordTrace]
  refine ⟨231400408878217504394681147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154266939252145002929787431 231400408878217504394681147)
  ·
    refine ⟨347100613317326256592021721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231400408878217504394681147 347100613317326256592021721)
    ·
      refine ⟨260325459987994692444016291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347100613317326256592021721 260325459987994692444016291)
      ·
        refine ⟨390488189981992038666024437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260325459987994692444016291 390488189981992038666024437)
        ·
          refine ⟨36608267810811753624939791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390488189981992038666024437 36608267810811753624939791)
          ·
            refine ⟨54912401716217630437409687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608267810811753624939791 54912401716217630437409687)
            ·
              refine ⟨82368602574326445656114531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54912401716217630437409687 82368602574326445656114531)
              ·
                refine ⟨123552903861489668484171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82368602574326445656114531 123552903861489668484171797)
                ·
                  refine ⟨5791542368507328210195553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123552903861489668484171797 5791542368507328210195553)
                  ·
                    refine ⟨4343656776380496157646665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791542368507328210195553 4343656776380496157646665)
                    ·
                      refine ⟨3257742582285372118234999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343656776380496157646665 3257742582285372118234999)
                      ·
                        rfl

theorem cell23_6344431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2, 2].length) (baseStart_6344431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344431 prefixEnd_6344431 := by exact prefixLift 6344431
  have htrace : WordTrace (prefixWord ++ tailWord_6344431) baseStart_6344431 baseEnd_6344431 := by
    simpa [prefixWord, tailWord_6344431, baseEnd_6344431] using wordTrace_append hprefix tailTrace_6344431
  have hstable : (prefixWord ++ tailWord_6344431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344431).length < 2 ^ (prefixWord ++ tailWord_6344431).sum := by decide
  have hdescent : baseEnd_6344431 < baseStart_6344431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344434 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6344434 : Nat := 118140960795 + 6344434 * 2 ^ 59
def prefixEnd_6344434 : Nat := 4983230072969 + 3 ^ 40 * 6344434 * 2
def baseEnd_6344434 : Nat := 3257744122727335606497485

theorem tailTrace_6344434 : CollatzResearch.WordTrace tailWord_6344434 prefixEnd_6344434 3257744122727335606497485 := by
  unfold tailWord_6344434
  simp only [CollatzResearch.WordTrace]
  refine ⟨57850129574301658976760089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154267012198137757271360237 57850129574301658976760089)
  ·
    refine ⟨43387597180726244232570067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57850129574301658976760089 43387597180726244232570067)
    ·
      refine ⟨65081395771089366348855101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43387597180726244232570067 65081395771089366348855101)
      ·
        refine ⟨24405523414158512380820663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65081395771089366348855101 24405523414158512380820663)
        ·
          refine ⟨36608285121237768571230995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24405523414158512380820663 36608285121237768571230995)
          ·
            refine ⟨54912427681856652856846493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608285121237768571230995 54912427681856652856846493)
            ·
              refine ⟨20592160380696244821317435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54912427681856652856846493 20592160380696244821317435)
              ·
                refine ⟨30888240571044367231976153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20592160380696244821317435 30888240571044367231976153)
                ·
                  refine ⟨23166180428283275423982115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30888240571044367231976153 23166180428283275423982115)
                  ·
                    refine ⟨34749270642424913135973173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23166180428283275423982115 34749270642424913135973173)
                    ·
                      refine ⟨3257744122727335606497485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34749270642424913135973173 3257744122727335606497485)
                      ·
                        rfl

theorem cell23_6344434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6344434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344434 prefixEnd_6344434 := by exact prefixLift 6344434
  have htrace : WordTrace (prefixWord ++ tailWord_6344434) baseStart_6344434 baseEnd_6344434 := by
    simpa [prefixWord, tailWord_6344434, baseEnd_6344434] using wordTrace_append hprefix tailTrace_6344434
  have hstable : (prefixWord ++ tailWord_6344434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344434).length < 2 ^ (prefixWord ++ tailWord_6344434).sum := by decide
  have hdescent : baseEnd_6344434 < baseStart_6344434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344467 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 7]
def baseStart_6344467 : Nat := 118140960795 + 6344467 * 2 ^ 59
def prefixEnd_6344467 : Nat := 4983230072969 + 3 ^ 40 * 6344467 * 2
def baseEnd_6344467 : Nat := 1085920355862977992461611

theorem tailTrace_6344467 : CollatzResearch.WordTrace tailWord_6344467 prefixEnd_6344467 1085920355862977992461611 := by
  unfold tailWord_6344467
  simp only [CollatzResearch.WordTrace]
  refine ⟨231401721906087082542991655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154267814604058055028661103 231401721906087082542991655)
  ·
    refine ⟨347102582859130623814487483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231401721906087082542991655 347102582859130623814487483)
    ·
      refine ⟨520653874288695935721731225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347102582859130623814487483 520653874288695935721731225)
      ·
        refine ⟨390490405716521951791298419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520653874288695935721731225 390490405716521951791298419)
        ·
          refine ⟨585735608574782927686947629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390490405716521951791298419 585735608574782927686947629)
          ·
            refine ⟨219650853215543597882605361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585735608574782927686947629 219650853215543597882605361)
            ·
              refine ⟨164738139911657698411954021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219650853215543597882605361 164738139911657698411954021)
              ·
                refine ⟨30888401233435818452241379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164738139911657698411954021 30888401233435818452241379)
                ·
                  refine ⟨46332601850153727678362069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30888401233435818452241379 46332601850153727678362069)
                  ·
                    refine ⟨1085920355862977992461611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46332601850153727678362069 1085920355862977992461611)
                    ·
                      rfl

theorem cell23_6344467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_6344467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344467 prefixEnd_6344467 := by exact prefixLift 6344467
  have htrace : WordTrace (prefixWord ++ tailWord_6344467) baseStart_6344467 baseEnd_6344467 := by
    simpa [prefixWord, tailWord_6344467, baseEnd_6344467] using wordTrace_append hprefix tailTrace_6344467
  have hstable : (prefixWord ++ tailWord_6344467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344467).length < 2 ^ (prefixWord ++ tailWord_6344467).sum := by decide
  have hdescent : baseEnd_6344467 < baseStart_6344467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344521 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 4, 2]
def baseStart_6344521 : Nat := 118140960795 + 6344521 * 2 ^ 59
def prefixEnd_6344521 : Nat := 4983230072969 + 3 ^ 40 * 6344521 * 2
def baseEnd_6344521 : Nat := 3257788795544276766109585

theorem tailTrace_6344521 : CollatzResearch.WordTrace tailWord_6344521 prefixEnd_6344521 3257788795544276766109585 := by
  unfold tailWord_6344521
  simp only [CollatzResearch.WordTrace]
  refine ⟨231403691447891449765457417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154269127631927633176971611 231403691447891449765457417)
  ·
    refine ⟨173552768585918587324093063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231403691447891449765457417 173552768585918587324093063)
    ·
      refine ⟨260329152878877880986139595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173552768585918587324093063 260329152878877880986139595)
      ·
        refine ⟨390493729318316821479209393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260329152878877880986139595 390493729318316821479209393)
        ·
          refine ⟨292870296988737616109407045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390493729318316821479209393 292870296988737616109407045)
          ·
            refine ⟨54913180685388303020513821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292870296988737616109407045 54913180685388303020513821)
            ·
              refine ⟨20592442757020613632692683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54913180685388303020513821 20592442757020613632692683)
              ·
                refine ⟨30888664135530920449039025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20592442757020613632692683 30888664135530920449039025)
                ·
                  refine ⟨23166498101648190336779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30888664135530920449039025 23166498101648190336779269)
                  ·
                    refine ⟨4343718394059035688146113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23166498101648190336779269 4343718394059035688146113)
                    ·
                      refine ⟨3257788795544276766109585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343718394059035688146113 3257788795544276766109585)
                      ·
                        rfl

theorem cell23_6344521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4, 2].length) (baseStart_6344521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344521 prefixEnd_6344521 := by exact prefixLift 6344521
  have htrace : WordTrace (prefixWord ++ tailWord_6344521) baseStart_6344521 baseEnd_6344521 := by
    simpa [prefixWord, tailWord_6344521, baseEnd_6344521] using wordTrace_append hprefix tailTrace_6344521
  have hstable : (prefixWord ++ tailWord_6344521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344521).length < 2 ^ (prefixWord ++ tailWord_6344521).sum := by decide
  have hdescent : baseEnd_6344521 < baseStart_6344521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344581 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_6344581 : Nat := 118140960795 + 6344581 * 2 ^ 59
def prefixEnd_6344581 : Nat := 4983230072969 + 3 ^ 40 * 6344581 * 2
def baseEnd_6344581 : Nat := 3257819604383546531359309

theorem tailTrace_6344581 : CollatzResearch.WordTrace tailWord_6344581 prefixEnd_6344581 3257819604383546531359309 := by
  unfold tailWord_6344581
  simp only [CollatzResearch.WordTrace]
  refine ⟨231405879827674080012641597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154270586551782720008427731 231405879827674080012641597)
  ·
    refine ⟨86777204935377780004740599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231405879827674080012641597 86777204935377780004740599)
    ·
      refine ⟨130165807403066670007110899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86777204935377780004740599 130165807403066670007110899)
      ·
        refine ⟨195248711104600005010666349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130165807403066670007110899 195248711104600005010666349)
        ·
          refine ⟨73218266664225001878999881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195248711104600005010666349 73218266664225001878999881)
          ·
            refine ⟨54913699998168751409249911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73218266664225001878999881 54913699998168751409249911)
            ·
              refine ⟨82370549997253127113874867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54913699998168751409249911 82370549997253127113874867)
              ·
                refine ⟨123555824995879690670812301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82370549997253127113874867 123555824995879690670812301)
                ·
                  refine ⟨46333434373454884001554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123555824995879690670812301 46333434373454884001554613)
                  ·
                    refine ⟨4343759472511395375145745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46333434373454884001554613 4343759472511395375145745)
                    ·
                      refine ⟨3257819604383546531359309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343759472511395375145745 3257819604383546531359309)
                      ·
                        rfl

theorem cell23_6344581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_6344581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344581 prefixEnd_6344581 := by exact prefixLift 6344581
  have htrace : WordTrace (prefixWord ++ tailWord_6344581) baseStart_6344581 baseEnd_6344581 := by
    simpa [prefixWord, tailWord_6344581, baseEnd_6344581] using wordTrace_append hprefix tailTrace_6344581
  have hstable : (prefixWord ++ tailWord_6344581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344581).length < 2 ^ (prefixWord ++ tailWord_6344581).sum := by decide
  have hdescent : baseEnd_6344581 < baseStart_6344581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344615 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6344615 : Nat := 118140960795 + 6344615 * 2 ^ 59
def prefixEnd_6344615 : Nat := 4983230072969 + 3 ^ 40 * 6344615 * 2
def baseEnd_6344615 : Nat := 3257837062725799398334153

theorem tailTrace_6344615 : CollatzResearch.WordTrace tailWord_6344615 prefixEnd_6344615 3257837062725799398334153 := by
  unfold tailWord_6344615
  simp only [CollatzResearch.WordTrace]
  refine ⟨231407119909550903819379299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154271413273033935879586199 231407119909550903819379299)
  ·
    refine ⟨347110679864326355729068949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231407119909550903819379299 347110679864326355729068949)
    ·
      refine ⟨16270813118640297924800107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 347110679864326355729068949 16270813118640297924800107)
      ·
        refine ⟨24406219677960446887200161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16270813118640297924800107 24406219677960446887200161)
        ·
          refine ⟨18304664758470335165400121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24406219677960446887200161 18304664758470335165400121)
          ·
            refine ⟨13728498568852751374050091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18304664758470335165400121 13728498568852751374050091)
            ·
              refine ⟨20592747853279127061075137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13728498568852751374050091 20592747853279127061075137)
              ·
                refine ⟨15444560889959345295806353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20592747853279127061075137 15444560889959345295806353)
                ·
                  refine ⟨11583420667469508971854765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15444560889959345295806353 11583420667469508971854765)
                  ·
                    refine ⟨4343782750301065864445537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11583420667469508971854765 4343782750301065864445537)
                    ·
                      refine ⟨3257837062725799398334153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343782750301065864445537 3257837062725799398334153)
                      ·
                        rfl

theorem cell23_6344615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6344615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344615 prefixEnd_6344615 := by exact prefixLift 6344615
  have htrace : WordTrace (prefixWord ++ tailWord_6344615) baseStart_6344615 baseEnd_6344615 := by
    simpa [prefixWord, tailWord_6344615, baseEnd_6344615] using wordTrace_append hprefix tailTrace_6344615
  have hstable : (prefixWord ++ tailWord_6344615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344615).length < 2 ^ (prefixWord ++ tailWord_6344615).sum := by decide
  have hdescent : baseEnd_6344615 < baseStart_6344615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344631 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_6344631 : Nat := 118140960795 + 6344631 * 2 ^ 59
def prefixEnd_6344631 : Nat := 4983230072969 + 3 ^ 40 * 6344631 * 2
def baseEnd_6344631 : Nat := 3257845278416271335734079

theorem tailTrace_6344631 : CollatzResearch.WordTrace tailWord_6344631 prefixEnd_6344631 3257845278416271335734079 := by
  unfold tailWord_6344631
  simp only [CollatzResearch.WordTrace]
  refine ⟨231407703477492938551961747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154271802318328625701307831 231407703477492938551961747)
  ·
    refine ⟨347111555216239407827942621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231407703477492938551961747 347111555216239407827942621)
    ·
      refine ⟨130166833206089777935478483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347111555216239407827942621 130166833206089777935478483)
      ·
        refine ⟨195250249809134666903217725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130166833206089777935478483 195250249809134666903217725)
        ·
          refine ⟨73218843678425500088706647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195250249809134666903217725 73218843678425500088706647)
          ·
            refine ⟨109828265517638250133059971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73218843678425500088706647 109828265517638250133059971)
            ·
              refine ⟨164742398276457375199589957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109828265517638250133059971 164742398276457375199589957)
              ·
                refine ⟨30889199676835757849923117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164742398276457375199589957 30889199676835757849923117)
                ·
                  refine ⟨11583449878813409193721169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30889199676835757849923117 11583449878813409193721169)
                  ·
                    refine ⟨8687587409110056895290877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11583449878813409193721169 8687587409110056895290877)
                    ·
                      refine ⟨3257845278416271335734079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687587409110056895290877 3257845278416271335734079)
                      ·
                        rfl

theorem cell23_6344631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_6344631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344631 prefixEnd_6344631 := by exact prefixLift 6344631
  have htrace : WordTrace (prefixWord ++ tailWord_6344631) baseStart_6344631 baseEnd_6344631 := by
    simpa [prefixWord, tailWord_6344631, baseEnd_6344631] using wordTrace_append hprefix tailTrace_6344631
  have hstable : (prefixWord ++ tailWord_6344631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344631).length < 2 ^ (prefixWord ++ tailWord_6344631).sum := by decide
  have hdescent : baseEnd_6344631 < baseStart_6344631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344648 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_6344648 : Nat := 118140960795 + 6344648 * 2 ^ 59
def prefixEnd_6344648 : Nat := 4983230072969 + 3 ^ 40 * 6344648 * 2
def baseEnd_6344648 : Nat := 3257854007587397769221501

theorem tailTrace_6344648 : CollatzResearch.WordTrace tailWord_6344648 prefixEnd_6344648 3257854007587397769221501 := by
  unfold tailWord_6344648
  simp only [CollatzResearch.WordTrace]
  refine ⟨115704161759215675227665299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154272215678954233636887065 115704161759215675227665299)
  ·
    refine ⟨173556242638823512841497949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115704161759215675227665299 173556242638823512841497949)
    ·
      refine ⟨65083590989558817315561731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173556242638823512841497949 65083590989558817315561731)
      ·
        refine ⟨97625386484338225973342597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65083590989558817315561731 97625386484338225973342597)
        ·
          refine ⟨18304759965813417370001737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97625386484338225973342597 18304759965813417370001737)
          ·
            refine ⟨13728569974360063027501303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18304759965813417370001737 13728569974360063027501303)
            ·
              refine ⟨20592854961540094541251955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13728569974360063027501303 20592854961540094541251955)
              ·
                refine ⟨30889282442310141811877933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20592854961540094541251955 30889282442310141811877933)
                ·
                  refine ⟨11583480915866303179454225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30889282442310141811877933 11583480915866303179454225)
                  ·
                    refine ⟨8687610686899727384590669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11583480915866303179454225 8687610686899727384590669)
                    ·
                      refine ⟨3257854007587397769221501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687610686899727384590669 3257854007587397769221501)
                      ·
                        rfl

theorem cell23_6344648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_6344648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344648 prefixEnd_6344648 := by exact prefixLift 6344648
  have htrace : WordTrace (prefixWord ++ tailWord_6344648) baseStart_6344648 baseEnd_6344648 := by
    simpa [prefixWord, tailWord_6344648, baseEnd_6344648] using wordTrace_append hprefix tailTrace_6344648
  have hstable : (prefixWord ++ tailWord_6344648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344648).length < 2 ^ (prefixWord ++ tailWord_6344648).sum := by decide
  have hdescent : baseEnd_6344648 < baseStart_6344648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344665 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 1, 5]
def baseStart_6344665 : Nat := 118140960795 + 6344665 * 2 ^ 59
def prefixEnd_6344665 : Nat := 4983230072969 + 3 ^ 40 * 6344665 * 2
def baseEnd_6344665 : Nat := 3257862736758524202708923

theorem tailTrace_6344665 : CollatzResearch.WordTrace tailWord_6344665 prefixEnd_6344665 3257862736758524202708923 := by
  unfold tailWord_6344665
  simp only [CollatzResearch.WordTrace]
  refine ⟨231408943559369762358699449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154272629039579841572466299 231408943559369762358699449)
  ·
    refine ⟨173556707669527321769024587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231408943559369762358699449 173556707669527321769024587)
    ·
      refine ⟨260335061504290982653536881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173556707669527321769024587 260335061504290982653536881)
      ·
        refine ⟨195251296128218236990152661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260335061504290982653536881 195251296128218236990152661)
        ·
          refine ⟨4576202253005114929456703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 195251296128218236990152661 4576202253005114929456703)
          ·
            refine ⟨6864303379507672394185055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576202253005114929456703 6864303379507672394185055)
            ·
              refine ⟨10296455069261508591277583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864303379507672394185055 10296455069261508591277583)
              ·
                refine ⟨15444682603892262886916375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10296455069261508591277583 15444682603892262886916375)
                ·
                  refine ⟨23167023905838394330374563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15444682603892262886916375 23167023905838394330374563)
                  ·
                    refine ⟨34750535858757591495561845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23167023905838394330374563 34750535858757591495561845)
                    ·
                      refine ⟨3257862736758524202708923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34750535858757591495561845 3257862736758524202708923)
                      ·
                        rfl

theorem cell23_6344665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_6344665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344665 prefixEnd_6344665 := by exact prefixLift 6344665
  have htrace : WordTrace (prefixWord ++ tailWord_6344665) baseStart_6344665 baseEnd_6344665 := by
    simpa [prefixWord, tailWord_6344665, baseEnd_6344665] using wordTrace_append hprefix tailTrace_6344665
  have hstable : (prefixWord ++ tailWord_6344665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344665).length < 2 ^ (prefixWord ++ tailWord_6344665).sum := by decide
  have hdescent : baseEnd_6344665 < baseStart_6344665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344668 : List Nat := [2, 2, 6, 1, 12]
def baseStart_6344668 : Nat := 118140960795 + 6344668 * 2 ^ 59
def prefixEnd_6344668 : Nat := 4983230072969 + 3 ^ 40 * 6344668 * 2
def baseEnd_6344668 : Nat := 4468949625789420700921

theorem tailTrace_6344668 : CollatzResearch.WordTrace tailWord_6344668 prefixEnd_6344668 4468949625789420700921 := by
  unfold tailWord_6344668
  simp only [CollatzResearch.WordTrace]
  refine ⟨115704526489179446935529329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154272701985572595914039105 115704526489179446935529329)
  ·
    refine ⟨86778394866884585201646997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115704526489179446935529329 86778394866884585201646997)
    ·
      refine ⟨4067737259385214931327203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86778394866884585201646997 4067737259385214931327203)
      ·
        refine ⟨6101605889077822396990805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067737259385214931327203 6101605889077822396990805)
        ·
          refine ⟨4468949625789420700921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6101605889077822396990805 4468949625789420700921)
          ·
            rfl

theorem cell23_6344668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 12].length) (baseStart_6344668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344668 prefixEnd_6344668 := by exact prefixLift 6344668
  have htrace : WordTrace (prefixWord ++ tailWord_6344668) baseStart_6344668 baseEnd_6344668 := by
    simpa [prefixWord, tailWord_6344668, baseEnd_6344668] using wordTrace_append hprefix tailTrace_6344668
  have hstable : (prefixWord ++ tailWord_6344668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344668).length < 2 ^ (prefixWord ++ tailWord_6344668).sum := by decide
  have hdescent : baseEnd_6344668 < baseStart_6344668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344679 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6344679 : Nat := 118140960795 + 6344679 * 2 ^ 59
def prefixEnd_6344679 : Nat := 4983230072969 + 3 ^ 40 * 6344679 * 2
def baseEnd_6344679 : Nat := 3257869925487687147933859

theorem tailTrace_6344679 : CollatzResearch.WordTrace tailWord_6344679 prefixEnd_6344679 3257869925487687147933859 := by
  unfold tailWord_6344679
  simp only [CollatzResearch.WordTrace]
  refine ⟨231409454181319042749709091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154272969454212695166472727 231409454181319042749709091)
  ·
    refine ⟨347114181271978564124563637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231409454181319042749709091 347114181271978564124563637)
    ·
      refine ⟨32541954494247990386677841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 347114181271978564124563637 32541954494247990386677841)
      ·
        refine ⟨24406465870685992790008381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32541954494247990386677841 24406465870685992790008381)
        ·
          refine ⟨9152424701507247296253143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24406465870685992790008381 9152424701507247296253143)
          ·
            refine ⟨13728637052260870944379715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9152424701507247296253143 13728637052260870944379715)
            ·
              refine ⟨20592955578391306416569573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13728637052260870944379715 20592955578391306416569573)
              ·
                refine ⟨3861179170948369953106795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20592955578391306416569573 3861179170948369953106795)
                ·
                  refine ⟨5791768756422554929660193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861179170948369953106795 5791768756422554929660193)
                  ·
                    refine ⟨4343826567316916197245145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791768756422554929660193 4343826567316916197245145)
                    ·
                      refine ⟨3257869925487687147933859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343826567316916197245145 3257869925487687147933859)
                      ·
                        rfl

theorem cell23_6344679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6344679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344679 prefixEnd_6344679 := by exact prefixLift 6344679
  have htrace : WordTrace (prefixWord ++ tailWord_6344679) baseStart_6344679 baseEnd_6344679 := by
    simpa [prefixWord, tailWord_6344679, baseEnd_6344679] using wordTrace_append hprefix tailTrace_6344679
  have hstable : (prefixWord ++ tailWord_6344679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344679).length < 2 ^ (prefixWord ++ tailWord_6344679).sum := by decide
  have hdescent : baseEnd_6344679 < baseStart_6344679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344685 : List Nat := [1, 5, 1, 4, 1, 2, 1, 8]
def baseStart_6344685 : Nat := 118140960795 + 6344685 * 2 ^ 59
def prefixEnd_6344685 : Nat := 4983230072969 + 3 ^ 40 * 6344685 * 2
def baseEnd_6344685 : Nat := 120661963198948671276253

theorem tailTrace_6344685 : CollatzResearch.WordTrace tailWord_6344685 prefixEnd_6344685 120661963198948671276253 := by
  unfold tailWord_6344685
  simp only [CollatzResearch.WordTrace]
  refine ⟨231409673019297305774427509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154273115346198203849618339 231409673019297305774427509)
  ·
    refine ⟨21694656845559122416352579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231409673019297305774427509 21694656845559122416352579)
    ·
      refine ⟨32541985268338683624528869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21694656845559122416352579 32541985268338683624528869)
      ·
        refine ⟨6101622237813503179599163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32541985268338683624528869 6101622237813503179599163)
        ·
          refine ⟨9152433356720254769398745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101622237813503179599163 9152433356720254769398745)
          ·
            refine ⟨6864325017540191077049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152433356720254769398745 6864325017540191077049059)
            ·
              refine ⟨10296487526310286615573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864325017540191077049059 10296487526310286615573589)
              ·
                refine ⟨120661963198948671276253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10296487526310286615573589 120661963198948671276253)
                ·
                  rfl

theorem cell23_6344685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 8].length) (baseStart_6344685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344685 prefixEnd_6344685 := by exact prefixLift 6344685
  have htrace : WordTrace (prefixWord ++ tailWord_6344685) baseStart_6344685 baseEnd_6344685 := by
    simpa [prefixWord, tailWord_6344685, baseEnd_6344685] using wordTrace_append hprefix tailTrace_6344685
  have hstable : (prefixWord ++ tailWord_6344685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344685).length < 2 ^ (prefixWord ++ tailWord_6344685).sum := by decide
  have hdescent : baseEnd_6344685 < baseStart_6344685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344688 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2]
def baseStart_6344688 : Nat := 118140960795 + 6344688 * 2 ^ 59
def prefixEnd_6344688 : Nat := 4983230072969 + 3 ^ 40 * 6344688 * 2
def baseEnd_6344688 : Nat := 3257874546813577612721317

theorem tailTrace_6344688 : CollatzResearch.WordTrace tailWord_6344688 prefixEnd_6344688 3257874546813577612721317 := by
  unfold tailWord_6344688
  simp only [CollatzResearch.WordTrace]
  refine ⟨115704891219143218643393359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154273188292190958191191145 115704891219143218643393359)
  ·
    refine ⟨173557336828714827965090039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115704891219143218643393359 173557336828714827965090039)
    ·
      refine ⟨260336005243072241947635059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173557336828714827965090039 260336005243072241947635059)
      ·
        refine ⟨390504007864608362921452589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260336005243072241947635059 390504007864608362921452589)
        ·
          refine ⟨146439002949228136095544721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390504007864608362921452589 146439002949228136095544721)
          ·
            refine ⟨109829252211921102071658541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146439002949228136095544721 109829252211921102071658541)
            ·
              refine ⟨41185969579470413276871953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109829252211921102071658541 41185969579470413276871953)
              ·
                refine ⟨30889477184602809957653965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41185969579470413276871953 30889477184602809957653965)
                ·
                  refine ⟨11583553944226053734120237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30889477184602809957653965 11583553944226053734120237)
                  ·
                    refine ⟨4343832729084770150295089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11583553944226053734120237 4343832729084770150295089)
                    ·
                      refine ⟨3257874546813577612721317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343832729084770150295089 3257874546813577612721317)
                      ·
                        rfl

theorem cell23_6344688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2].length) (baseStart_6344688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344688 prefixEnd_6344688 := by exact prefixLift 6344688
  have htrace : WordTrace (prefixWord ++ tailWord_6344688) baseStart_6344688 baseEnd_6344688 := by
    simpa [prefixWord, tailWord_6344688, baseEnd_6344688] using wordTrace_append hprefix tailTrace_6344688
  have hstable : (prefixWord ++ tailWord_6344688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344688).length < 2 ^ (prefixWord ++ tailWord_6344688).sum := by decide
  have hdescent : baseEnd_6344688 < baseStart_6344688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344705 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6344705 : Nat := 118140960795 + 6344705 * 2 ^ 59
def prefixEnd_6344705 : Nat := 4983230072969 + 3 ^ 40 * 6344705 * 2
def baseEnd_6344705 : Nat := 3257883275984704046208739

theorem tailTrace_6344705 : CollatzResearch.WordTrace tailWord_6344705 prefixEnd_6344705 3257883275984704046208739 := by
  unfold tailWord_6344705
  simp only [CollatzResearch.WordTrace]
  refine ⟨231410402479224849190155569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154273601652816566126770379 231410402479224849190155569)
  ·
    refine ⟨173557801859418636892616677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231410402479224849190155569 173557801859418636892616677)
    ·
      refine ⟨32542087848640994417365627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173557801859418636892616677 32542087848640994417365627)
      ·
        refine ⟨48813131772961491626048441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32542087848640994417365627 48813131772961491626048441)
        ·
          refine ⟨36609848829721118719536331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48813131772961491626048441 36609848829721118719536331)
          ·
            refine ⟨54914773244581678079304497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36609848829721118719536331 54914773244581678079304497)
            ·
              refine ⟨41186079933436258559478373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54914773244581678079304497 41186079933436258559478373)
              ·
                refine ⟨7722389987519298479902195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41186079933436258559478373 7722389987519298479902195)
                ·
                  refine ⟨11583584981278947719853293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722389987519298479902195 11583584981278947719853293)
                  ·
                    refine ⟨4343844367979605394944985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11583584981278947719853293 4343844367979605394944985)
                    ·
                      refine ⟨3257883275984704046208739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343844367979605394944985 3257883275984704046208739)
                      ·
                        rfl

theorem cell23_6344705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6344705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344705 prefixEnd_6344705 := by exact prefixLift 6344705
  have htrace : WordTrace (prefixWord ++ tailWord_6344705) baseStart_6344705 baseEnd_6344705 := by
    simpa [prefixWord, tailWord_6344705, baseEnd_6344705] using wordTrace_append hprefix tailTrace_6344705
  have hstable : (prefixWord ++ tailWord_6344705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344705).length < 2 ^ (prefixWord ++ tailWord_6344705).sum := by decide
  have hdescent : baseEnd_6344705 < baseStart_6344705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344735 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 4, 2, 2]
def baseStart_6344735 : Nat := 118140960795 + 6344735 * 2 ^ 59
def prefixEnd_6344735 : Nat := 4983230072969 + 3 ^ 40 * 6344735 * 2
def baseEnd_6344735 : Nat := 3257898680404338928833601

theorem tailTrace_6344735 : CollatzResearch.WordTrace tailWord_6344735 prefixEnd_6344735 3257898680404338928833601 := by
  unfold tailWord_6344735
  simp only [CollatzResearch.WordTrace]
  refine ⟨231411496669116164313747659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154274331112744109542498439 231411496669116164313747659)
  ·
    refine ⟨347117245003674246470621489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231411496669116164313747659 347117245003674246470621489)
    ·
      refine ⟨260337933752755684852966117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347117245003674246470621489 260337933752755684852966117)
      ·
        refine ⟨48813362578641690909931147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260337933752755684852966117 48813362578641690909931147)
        ·
          refine ⟨73220043867962536364896721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48813362578641690909931147 73220043867962536364896721)
          ·
            refine ⟨54915032900971902273672541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73220043867962536364896721 54915032900971902273672541)
            ·
              refine ⟨20593137337864463352627203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54915032900971902273672541 20593137337864463352627203)
              ·
                refine ⟨30889706006796695028940805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20593137337864463352627203 30889706006796695028940805)
                ·
                  refine ⟨5791819876274380317926401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30889706006796695028940805 5791819876274380317926401)
                  ·
                    refine ⟨4343864907205785238444801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791819876274380317926401 4343864907205785238444801)
                    ·
                      refine ⟨3257898680404338928833601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343864907205785238444801 3257898680404338928833601)
                      ·
                        rfl

theorem cell23_6344735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_6344735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344735 prefixEnd_6344735 := by exact prefixLift 6344735
  have htrace : WordTrace (prefixWord ++ tailWord_6344735) baseStart_6344735 baseEnd_6344735 := by
    simpa [prefixWord, tailWord_6344735, baseEnd_6344735] using wordTrace_append hprefix tailTrace_6344735
  have hstable : (prefixWord ++ tailWord_6344735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344735).length < 2 ^ (prefixWord ++ tailWord_6344735).sum := by decide
  have hdescent : baseEnd_6344735 < baseStart_6344735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344741 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 7]
def baseStart_6344741 : Nat := 118140960795 + 6344741 * 2 ^ 59
def prefixEnd_6344741 : Nat := 4983230072969 + 3 ^ 40 * 6344741 * 2
def baseEnd_6344741 : Nat := 361989084587585100595397

theorem tailTrace_6344741 : CollatzResearch.WordTrace tailWord_6344741 prefixEnd_6344741 361989084587585100595397 := by
  unfold tailWord_6344741
  simp only [CollatzResearch.WordTrace]
  refine ⟨231411715507094427338466077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154274477004729618225644051 231411715507094427338466077)
  ·
    refine ⟨86779393315160410251924779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231411715507094427338466077 86779393315160410251924779)
    ·
      refine ⟨130169089972740615377887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86779393315160410251924779 130169089972740615377887169)
      ·
        refine ⟨97626817479555461533415377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130169089972740615377887169 97626817479555461533415377)
        ·
          refine ⟨73220113109666596150061533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97626817479555461533415377 73220113109666596150061533)
          ·
            refine ⟨27457542416124973556273075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73220113109666596150061533 27457542416124973556273075)
            ·
              refine ⟨41186313624187460334409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27457542416124973556273075 41186313624187460334409613)
              ·
                refine ⟨15444867609070297625403605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41186313624187460334409613 15444867609070297625403605)
                ·
                  refine ⟨361989084587585100595397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15444867609070297625403605 361989084587585100595397)
                  ·
                    rfl

theorem cell23_6344741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_6344741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344741 prefixEnd_6344741 := by exact prefixLift 6344741
  have htrace : WordTrace (prefixWord ++ tailWord_6344741) baseStart_6344741 baseEnd_6344741 := by
    simpa [prefixWord, tailWord_6344741, baseEnd_6344741] using wordTrace_append hprefix tailTrace_6344741
  have hstable : (prefixWord ++ tailWord_6344741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344741).length < 2 ^ (prefixWord ++ tailWord_6344741).sum := by decide
  have hdescent : baseEnd_6344741 < baseStart_6344741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_6344751 : Nat := 118140960795 + 6344751 * 2 ^ 59
def prefixEnd_6344751 : Nat := 4983230072969 + 3 ^ 40 * 6344751 * 2
def baseEnd_6344751 : Nat := 3257906896094810866233527

theorem tailTrace_6344751 : CollatzResearch.WordTrace tailWord_6344751 prefixEnd_6344751 3257906896094810866233527 := by
  unfold tailWord_6344751
  simp only [CollatzResearch.WordTrace]
  refine ⟨231412080237058199046330107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154274720158038799364220071 231412080237058199046330107)
  ·
    refine ⟨347118120355587298569495161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231412080237058199046330107 347118120355587298569495161)
    ·
      refine ⟨260338590266690473927121371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347118120355587298569495161 260338590266690473927121371)
      ·
        refine ⟨390507885400035710890682057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260338590266690473927121371 390507885400035710890682057)
        ·
          refine ⟨292880914050026783168011543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390507885400035710890682057 292880914050026783168011543)
          ·
            refine ⟨439321371075040174752017315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292880914050026783168011543 439321371075040174752017315)
            ·
              refine ⟨658982056612560262128025973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439321371075040174752017315 658982056612560262128025973)
              ·
                refine ⟨61779567807427524574502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658982056612560262128025973 61779567807427524574502435)
                ·
                  refine ⟨92669351711141286861753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61779567807427524574502435 92669351711141286861753653)
                  ·
                    refine ⟨8687751722919495643289405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92669351711141286861753653 8687751722919495643289405)
                    ·
                      refine ⟨3257906896094810866233527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8687751722919495643289405 3257906896094810866233527)
                      ·
                        rfl

theorem cell23_6344751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_6344751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344751 prefixEnd_6344751 := by exact prefixLift 6344751
  have htrace : WordTrace (prefixWord ++ tailWord_6344751) baseStart_6344751 baseEnd_6344751 := by
    simpa [prefixWord, tailWord_6344751, baseEnd_6344751] using wordTrace_append hprefix tailTrace_6344751
  have hstable : (prefixWord ++ tailWord_6344751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344751).length < 2 ^ (prefixWord ++ tailWord_6344751).sum := by decide
  have hdescent : baseEnd_6344751 < baseStart_6344751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344758 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_6344758 : Nat := 118140960795 + 6344758 * 2 ^ 59
def prefixEnd_6344758 : Nat := 4983230072969 + 3 ^ 40 * 6344758 * 2
def baseEnd_6344758 : Nat := 361990054495488037649555

theorem tailTrace_6344758 : CollatzResearch.WordTrace tailWord_6344758 prefixEnd_6344758 361990054495488037649555 := by
  unfold tailWord_6344758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463270971752052452614683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154274890365355226161223285 14463270971752052452614683)
  ·
    refine ⟨21694906457628078678922025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14463270971752052452614683 21694906457628078678922025)
    ·
      refine ⟨16271179843221059009191519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21694906457628078678922025 16271179843221059009191519)
      ·
        refine ⟨24406769764831588513787279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16271179843221059009191519 24406769764831588513787279)
        ·
          refine ⟨36610154647247382770680919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24406769764831588513787279 36610154647247382770680919)
          ·
            refine ⟨54915231970871074156021379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36610154647247382770680919 54915231970871074156021379)
            ·
              refine ⟨82372847956306611234032069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54915231970871074156021379 82372847956306611234032069)
              ·
                refine ⟨15444908991807489606381013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82372847956306611234032069 15444908991807489606381013)
                ·
                  refine ⟨361990054495488037649555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15444908991807489606381013 361990054495488037649555)
                  ·
                    rfl

theorem cell23_6344758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_6344758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344758 prefixEnd_6344758 := by exact prefixLift 6344758
  have htrace : WordTrace (prefixWord ++ tailWord_6344758) baseStart_6344758 baseEnd_6344758 := by
    simpa [prefixWord, tailWord_6344758, baseEnd_6344758] using wordTrace_append hprefix tailTrace_6344758
  have hstable : (prefixWord ++ tailWord_6344758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344758).length < 2 ^ (prefixWord ++ tailWord_6344758).sum := by decide
  have hdescent : baseEnd_6344758 < baseStart_6344758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344778 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_6344778 : Nat := 118140960795 + 6344778 * 2 ^ 59
def prefixEnd_6344778 : Nat := 4983230072969 + 3 ^ 40 * 6344778 * 2
def baseEnd_6344778 : Nat := 3257920760072482260595903

theorem tailTrace_6344778 : CollatzResearch.WordTrace tailWord_6344778 prefixEnd_6344778 3257920760072482260595903 := by
  unfold tailWord_6344778
  simp only [CollatzResearch.WordTrace]
  refine ⟨57853266251990095664390747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154275376671973588438375325 57853266251990095664390747)
  ·
    refine ⟨86779899377985143496586121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57853266251990095664390747 86779899377985143496586121)
    ·
      refine ⟨65084924533488857622439591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86779899377985143496586121 65084924533488857622439591)
      ·
        refine ⟨97627386800233286433659387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65084924533488857622439591 97627386800233286433659387)
        ·
          refine ⟨146441080200349929650489081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97627386800233286433659387 146441080200349929650489081)
          ·
            refine ⟨109830810150262447237866811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146441080200349929650489081 109830810150262447237866811)
            ·
              refine ⟨164746215225393670856800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109830810150262447237866811 164746215225393670856800217)
              ·
                refine ⟨123559661419045253142600163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164746215225393670856800217 123559661419045253142600163)
                ·
                  refine ⟨185339492128567879713900245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123559661419045253142600163 185339492128567879713900245)
                  ·
                    refine ⟨4343894346763309680794537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185339492128567879713900245 4343894346763309680794537)
                    ·
                      refine ⟨3257920760072482260595903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4343894346763309680794537 3257920760072482260595903)
                      ·
                        rfl

theorem cell23_6344778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_6344778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344778 prefixEnd_6344778 := by exact prefixLift 6344778
  have htrace : WordTrace (prefixWord ++ tailWord_6344778) baseStart_6344778 baseEnd_6344778 := by
    simpa [prefixWord, tailWord_6344778, baseEnd_6344778] using wordTrace_append hprefix tailTrace_6344778
  have hstable : (prefixWord ++ tailWord_6344778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344778).length < 2 ^ (prefixWord ++ tailWord_6344778).sum := by decide
  have hdescent : baseEnd_6344778 < baseStart_6344778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344825 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_6344825 : Nat := 118140960795 + 6344825 * 2 ^ 59
def prefixEnd_6344825 : Nat := 4983230072969 + 3 ^ 40 * 6344825 * 2
def baseEnd_6344825 : Nat := 3257944893663243576708187

theorem tailTrace_6344825 : CollatzResearch.WordTrace tailWord_6344825 prefixEnd_6344825 3257944893663243576708187 := by
  unfold tailWord_6344825
  simp only [CollatzResearch.WordTrace]
  refine ⟨231414779238790109684523929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154276519492526739789682619 231414779238790109684523929)
  ·
    refine ⟨173561084429092582263392947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231414779238790109684523929 173561084429092582263392947)
    ·
      refine ⟨260341626643638873395089421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173561084429092582263392947 260341626643638873395089421)
      ·
        refine ⟨97628109991364577523158533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260341626643638873395089421 97628109991364577523158533)
        ·
          refine ⟨18305270623380858285592225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97628109991364577523158533 18305270623380858285592225)
          ·
            refine ⟨13728952967535643714194169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18305270623380858285592225 13728952967535643714194169)
            ·
              refine ⟨10296714725651732785645627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13728952967535643714194169 10296714725651732785645627)
              ·
                refine ⟨15445072088477599178468441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10296714725651732785645627 15445072088477599178468441)
                ·
                  refine ⟨11583804066358199383851331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15445072088477599178468441 11583804066358199383851331)
                  ·
                    refine ⟨17375706099537299075776997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11583804066358199383851331 17375706099537299075776997)
                    ·
                      refine ⟨3257944893663243576708187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17375706099537299075776997 3257944893663243576708187)
                      ·
                        rfl

theorem cell23_6344825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_6344825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344825 prefixEnd_6344825 := by exact prefixLift 6344825
  have htrace : WordTrace (prefixWord ++ tailWord_6344825) baseStart_6344825 baseEnd_6344825 := by
    simpa [prefixWord, tailWord_6344825, baseEnd_6344825] using wordTrace_append hprefix tailTrace_6344825
  have hstable : (prefixWord ++ tailWord_6344825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344825).length < 2 ^ (prefixWord ++ tailWord_6344825).sum := by decide
  have hdescent : baseEnd_6344825 < baseStart_6344825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344848 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 6]
def baseStart_6344848 : Nat := 118140960795 + 6344848 * 2 ^ 59
def prefixEnd_6344848 : Nat := 4983230072969 + 3 ^ 40 * 6344848 * 2
def baseEnd_6344848 : Nat := 361995189302032998524509

theorem tailTrace_6344848 : CollatzResearch.WordTrace tailWord_6344848 prefixEnd_6344848 361995189302032998524509 := by
  unfold tailWord_6344848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115707809058853392306305599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154277078745137856408407465 115707809058853392306305599)
  ·
    refine ⟨173561713588280088459458399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115707809058853392306305599 173561713588280088459458399)
    ·
      refine ⟨260342570382420132689187599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173561713588280088459458399 260342570382420132689187599)
      ·
        refine ⟨390513855573630199033781399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260342570382420132689187599 390513855573630199033781399)
        ·
          refine ⟨585770783360445298550672099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390513855573630199033781399 585770783360445298550672099)
          ·
            refine ⟨878656175040667947826008149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585770783360445298550672099 878656175040667947826008149)
            ·
              refine ⟨10296752051257827513586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 878656175040667947826008149 10296752051257827513586033)
              ·
                refine ⟨7722564038443370635189525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296752051257827513586033 7722564038443370635189525)
                ·
                  refine ⟨361995189302032998524509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7722564038443370635189525 361995189302032998524509)
                  ·
                    rfl

theorem cell23_6344848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_6344848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344848 prefixEnd_6344848 := by exact prefixLift 6344848
  have htrace : WordTrace (prefixWord ++ tailWord_6344848) baseStart_6344848 baseEnd_6344848 := by
    simpa [prefixWord, tailWord_6344848, baseEnd_6344848] using wordTrace_append hprefix tailTrace_6344848
  have hstable : (prefixWord ++ tailWord_6344848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344848).length < 2 ^ (prefixWord ++ tailWord_6344848).sum := by decide
  have hdescent : baseEnd_6344848 < baseStart_6344848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344851 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_6344851 : Nat := 118140960795 + 6344851 * 2 ^ 59
def prefixEnd_6344851 : Nat := 4983230072969 + 3 ^ 40 * 6344851 * 2
def baseEnd_6344851 : Nat := 3257958244160260474983067

theorem tailTrace_6344851 : CollatzResearch.WordTrace tailWord_6344851 prefixEnd_6344851 3257958244160260474983067 := by
  unfold tailWord_6344851
  simp only [CollatzResearch.WordTrace]
  refine ⟨231415727536695916124970407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154277151691130610749980271 231415727536695916124970407)
  ·
    refine ⟨347123591305043874187455611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231415727536695916124970407 347123591305043874187455611)
    ·
      refine ⟨520685386957565811281183417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347123591305043874187455611 520685386957565811281183417)
      ·
        refine ⟨390514040218174358460887563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520685386957565811281183417 390514040218174358460887563)
        ·
          refine ⟨585771060327261537691331345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390514040218174358460887563 585771060327261537691331345)
          ·
            refine ⟨439328295245446153268498509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585771060327261537691331345 439328295245446153268498509)
            ·
              refine ⟨164748110717042307475686941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439328295245446153268498509 164748110717042307475686941)
              ·
                refine ⟨61780541518890865303382603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164748110717042307475686941 61780541518890865303382603)
                ·
                  refine ⟨92670812278336297955073905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61780541518890865303382603 92670812278336297955073905)
                  ·
                    refine ⟨69503109208752223466305429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92670812278336297955073905 69503109208752223466305429)
                    ·
                      refine ⟨3257958244160260474983067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69503109208752223466305429 3257958244160260474983067)
                      ·
                        rfl

theorem cell23_6344851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_6344851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344851 prefixEnd_6344851 := by exact prefixLift 6344851
  have htrace : WordTrace (prefixWord ++ tailWord_6344851) baseStart_6344851 baseEnd_6344851 := by
    simpa [prefixWord, tailWord_6344851, baseEnd_6344851] using wordTrace_append hprefix tailTrace_6344851
  have hstable : (prefixWord ++ tailWord_6344851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344851).length < 2 ^ (prefixWord ++ tailWord_6344851).sum := by decide
  have hdescent : baseEnd_6344851 < baseStart_6344851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344928 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6344928 : Nat := 118140960795 + 6344928 * 2 ^ 59
def prefixEnd_6344928 : Nat := 4983230072969 + 3 ^ 40 * 6344928 * 2
def baseEnd_6344928 : Nat := 3257997782170656673720213

theorem tailTrace_6344928 : CollatzResearch.WordTrace tailWord_6344928 prefixEnd_6344928 3257997782170656673720213 := by
  unfold tailWord_6344928
  simp only [CollatzResearch.WordTrace]
  refine ⟨115709267978708479137761719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154279023971611305517015625 115709267978708479137761719)
  ·
    refine ⟨173563901968062718706642579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115709267978708479137761719 173563901968062718706642579)
    ·
      refine ⟨260345852952094078059963869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173563901968062718706642579 260345852952094078059963869)
      ·
        refine ⟨97629694857035279272486451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260345852952094078059963869 97629694857035279272486451)
        ·
          refine ⟨146444542285552918908729677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97629694857035279272486451 146444542285552918908729677)
          ·
            refine ⟨54916703357082344590773629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146444542285552918908729677 54916703357082344590773629)
            ·
              refine ⟨20593763758905879221540111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54916703357082344590773629 20593763758905879221540111)
              ·
                refine ⟨30890645638358818832310167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20593763758905879221540111 30890645638358818832310167)
                ·
                  refine ⟨46335968457538228248465251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30890645638358818832310167 46335968457538228248465251)
                  ·
                    refine ⟨69503952686307342372697877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46335968457538228248465251 69503952686307342372697877)
                    ·
                      refine ⟨3257997782170656673720213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69503952686307342372697877 3257997782170656673720213)
                      ·
                        rfl

theorem cell23_6344928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6344928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344928 prefixEnd_6344928 := by exact prefixLift 6344928
  have htrace : WordTrace (prefixWord ++ tailWord_6344928) baseStart_6344928 baseEnd_6344928 := by
    simpa [prefixWord, tailWord_6344928, baseEnd_6344928] using wordTrace_append hprefix tailTrace_6344928
  have hstable : (prefixWord ++ tailWord_6344928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344928).length < 2 ^ (prefixWord ++ tailWord_6344928).sum := by decide
  have hdescent : baseEnd_6344928 < baseStart_6344928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344938 : List Nat := [3, 1, 3, 1, 1, 2, 3, 9]
def baseStart_6344938 : Nat := 118140960795 + 6344938 * 2 ^ 59
def prefixEnd_6344938 : Nat := 4983230072969 + 3 ^ 40 * 6344938 * 2
def baseEnd_6344938 : Nat := 120666774702859319799821

theorem tailTrace_6344938 : CollatzResearch.WordTrace tailWord_6344938 prefixEnd_6344938 120666774702859319799821 := by
  unfold tailWord_6344938
  simp only [CollatzResearch.WordTrace]
  refine ⟨57854725171845182495846867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154279267124920486655591645 57854725171845182495846867)
  ·
    refine ⟨86782087757767773743770301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57854725171845182495846867 86782087757767773743770301)
    ·
      refine ⟨32543282909162915153913863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86782087757767773743770301 32543282909162915153913863)
      ·
        refine ⟨48814924363744372730870795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32543282909162915153913863 48814924363744372730870795)
        ·
          refine ⟨73222386545616559096306193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48814924363744372730870795 73222386545616559096306193)
          ·
            refine ⟨54916789909212419322229645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73222386545616559096306193 54916789909212419322229645)
            ·
              refine ⟨20593796215954657245836117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54916789909212419322229645 20593796215954657245836117)
              ·
                refine ⟨120666774702859319799821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20593796215954657245836117 120666774702859319799821)
                ·
                  rfl

theorem cell23_6344938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_6344938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344938 prefixEnd_6344938 := by exact prefixLift 6344938
  have htrace : WordTrace (prefixWord ++ tailWord_6344938) baseStart_6344938 baseEnd_6344938 := by
    simpa [prefixWord, tailWord_6344938, baseEnd_6344938] using wordTrace_append hprefix tailTrace_6344938
  have hstable : (prefixWord ++ tailWord_6344938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344938).length < 2 ^ (prefixWord ++ tailWord_6344938).sum := by decide
  have hdescent : baseEnd_6344938 < baseStart_6344938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344986 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_6344986 : Nat := 118140960795 + 6344986 * 2 ^ 59
def prefixEnd_6344986 : Nat := 4983230072969 + 3 ^ 40 * 6344986 * 2
def baseEnd_6344986 : Nat := 3258027564048617446794947

theorem tailTrace_6344986 : CollatzResearch.WordTrace tailWord_6344986 prefixEnd_6344986 3258027564048617446794947 := by
  unfold tailWord_6344986
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855162847801708545283703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154280434260804556120756541 57855162847801708545283703)
  ·
    refine ⟨86782744271702562817925555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57855162847801708545283703 86782744271702562817925555)
    ·
      refine ⟨130174116407553844226888333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86782744271702562817925555 130174116407553844226888333)
      ·
        refine ⟨48815293652832691585083125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130174116407553844226888333 48815293652832691585083125)
        ·
          refine ⟨4576433779953064836101543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48815293652832691585083125 4576433779953064836101543)
          ·
            refine ⟨6864650669929597254152315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576433779953064836101543 6864650669929597254152315)
            ·
              refine ⟨10296976004894395881228473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864650669929597254152315 10296976004894395881228473)
              ·
                refine ⟨7722732003670796910921355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296976004894395881228473 7722732003670796910921355)
                ·
                  refine ⟨11584098005506195366382033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722732003670796910921355 11584098005506195366382033)
                  ·
                    refine ⟨8688073504129646524786525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11584098005506195366382033 8688073504129646524786525)
                    ·
                      refine ⟨3258027564048617446794947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688073504129646524786525 3258027564048617446794947)
                      ·
                        rfl

theorem cell23_6344986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_6344986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344986 prefixEnd_6344986 := by exact prefixLift 6344986
  have htrace : WordTrace (prefixWord ++ tailWord_6344986) baseStart_6344986 baseEnd_6344986 := by
    simpa [prefixWord, tailWord_6344986, baseEnd_6344986] using wordTrace_append hprefix tailTrace_6344986
  have hstable : (prefixWord ++ tailWord_6344986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344986).length < 2 ^ (prefixWord ++ tailWord_6344986).sum := by decide
  have hdescent : baseEnd_6344986 < baseStart_6344986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6344988 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6344988 : Nat := 118140960795 + 6344988 * 2 ^ 59
def prefixEnd_6344988 : Nat := 4983230072969 + 3 ^ 40 * 6344988 * 2
def baseEnd_6344988 : Nat := 3258028591009926438969937

theorem tailTrace_6344988 : CollatzResearch.WordTrace tailWord_6344988 prefixEnd_6344988 3258028591009926438969937 := by
  unfold tailWord_6344988
  simp only [CollatzResearch.WordTrace]
  refine ⟨115710362168599794261353809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154280482891466392348471745 115710362168599794261353809)
  ·
    refine ⟨86782771626449845696015357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115710362168599794261353809 86782771626449845696015357)
    ·
      refine ⟨32543539359918692136005759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86782771626449845696015357 32543539359918692136005759)
      ·
        refine ⟨48815309039878038204008639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32543539359918692136005759 48815309039878038204008639)
        ·
          refine ⟨73222963559817057306012959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48815309039878038204008639 73222963559817057306012959)
          ·
            refine ⟨109834445339725585959019439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73222963559817057306012959 109834445339725585959019439)
            ·
              refine ⟨164751668009588378938529159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109834445339725585959019439 164751668009588378938529159)
              ·
                refine ⟨247127502014382568407793739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164751668009588378938529159 247127502014382568407793739)
                ·
                  refine ⟨370691253021573852611690609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247127502014382568407793739 370691253021573852611690609)
                  ·
                    refine ⟨278018439766180389458767957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 370691253021573852611690609 278018439766180389458767957)
                    ·
                      refine ⟨3258028591009926438969937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278018439766180389458767957 3258028591009926438969937)
                      ·
                        rfl

theorem cell23_6344988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6344988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6344988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6344988 prefixEnd_6344988 := by exact prefixLift 6344988
  have htrace : WordTrace (prefixWord ++ tailWord_6344988) baseStart_6344988 baseEnd_6344988 := by
    simpa [prefixWord, tailWord_6344988, baseEnd_6344988] using wordTrace_append hprefix tailTrace_6344988
  have hstable : (prefixWord ++ tailWord_6344988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6344988).length < 2 ^ (prefixWord ++ tailWord_6344988).sum := by decide
  have hdescent : baseEnd_6344988 < baseStart_6344988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6344988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345008 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_6345008 : Nat := 118140960795 + 6345008 * 2 ^ 59
def prefixEnd_6345008 : Nat := 4983230072969 + 3 ^ 40 * 6345008 * 2
def baseEnd_6345008 : Nat := 3258038860623016360719845

theorem tailTrace_6345008 : CollatzResearch.WordTrace tailWord_6345008 prefixEnd_6345008 3258038860623016360719845 := by
  unfold tailWord_6345008
  simp only [CollatzResearch.WordTrace]
  refine ⟨115710726898563565969217839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154280969198084754625623785 115710726898563565969217839)
  ·
    refine ⟨173566090347845348953826759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115710726898563565969217839 173566090347845348953826759)
    ·
      refine ⟨260349135521768023430740139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173566090347845348953826759 260349135521768023430740139)
      ·
        refine ⟨390523703282652035146110209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260349135521768023430740139 390523703282652035146110209)
        ·
          refine ⟨292892777461989026359582657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390523703282652035146110209 292892777461989026359582657)
          ·
            refine ⟨219669583096491769769686993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292892777461989026359582657 219669583096491769769686993)
            ·
              refine ⟨164752187322368827327265245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219669583096491769769686993 164752187322368827327265245)
              ·
                refine ⟨61782070245888310247724467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164752187322368827327265245 61782070245888310247724467)
                ·
                  refine ⟨92673105368832465371586701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61782070245888310247724467 92673105368832465371586701)
                  ·
                    refine ⟨34752414513312174514345013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92673105368832465371586701 34752414513312174514345013)
                    ·
                      refine ⟨3258038860623016360719845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34752414513312174514345013 3258038860623016360719845)
                      ·
                        rfl

theorem cell23_6345008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_6345008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345008 prefixEnd_6345008 := by exact prefixLift 6345008
  have htrace : WordTrace (prefixWord ++ tailWord_6345008) baseStart_6345008 baseEnd_6345008 := by
    simpa [prefixWord, tailWord_6345008, baseEnd_6345008] using wordTrace_append hprefix tailTrace_6345008
  have hstable : (prefixWord ++ tailWord_6345008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345008).length < 2 ^ (prefixWord ++ tailWord_6345008).sum := by decide
  have hdescent : baseEnd_6345008 < baseStart_6345008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345054 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_6345054 : Nat := 118140960795 + 6345054 * 2 ^ 59
def prefixEnd_6345054 : Nat := 4983230072969 + 3 ^ 40 * 6345054 * 2
def baseEnd_6345054 : Nat := 3258062480733123180744635

theorem tailTrace_6345054 : CollatzResearch.WordTrace tailWord_6345054 prefixEnd_6345054 3258062480733123180744635 := by
  unfold tailWord_6345054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28927891444370060224326277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154282087703306987863073477 28927891444370060224326277)
  ·
    refine ⟨5423979645819386292061177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28927891444370060224326277 5423979645819386292061177)
    ·
      refine ⟨4067984734364539719045883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5423979645819386292061177 4067984734364539719045883)
      ·
        refine ⟨6101977101546809578568825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067984734364539719045883 6101977101546809578568825)
        ·
          refine ⟨4576482826160107183926619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101977101546809578568825 4576482826160107183926619)
          ·
            refine ⟨6864724239240160775889929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576482826160107183926619 6864724239240160775889929)
            ·
              refine ⟨5148543179430120581917447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6864724239240160775889929 5148543179430120581917447)
              ·
                refine ⟨7722814769145180872876171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5148543179430120581917447 7722814769145180872876171)
                ·
                  refine ⟨11584222153717771309314257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722814769145180872876171 11584222153717771309314257)
                  ·
                    refine ⟨8688166615288328481985693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11584222153717771309314257 8688166615288328481985693)
                    ·
                      refine ⟨3258062480733123180744635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688166615288328481985693 3258062480733123180744635)
                      ·
                        rfl

theorem cell23_6345054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_6345054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345054 prefixEnd_6345054 := by exact prefixLift 6345054
  have htrace : WordTrace (prefixWord ++ tailWord_6345054) baseStart_6345054 baseEnd_6345054 := by
    simpa [prefixWord, tailWord_6345054, baseEnd_6345054] using wordTrace_append hprefix tailTrace_6345054
  have hstable : (prefixWord ++ tailWord_6345054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345054).length < 2 ^ (prefixWord ++ tailWord_6345054).sum := by decide
  have hdescent : baseEnd_6345054 < baseStart_6345054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345090 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6345090 : Nat := 118140960795 + 6345090 * 2 ^ 59
def prefixEnd_6345090 : Nat := 4983230072969 + 3 ^ 40 * 6345090 * 2
def baseEnd_6345090 : Nat := 3258080966036685039894469

theorem tailTrace_6345090 : CollatzResearch.WordTrace tailWord_6345090 prefixEnd_6345090 3258080966036685039894469 := by
  unfold tailWord_6345090
  simp only [CollatzResearch.WordTrace]
  refine ⟨57856111145707514985730181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154282963055220039961947149 57856111145707514985730181)
  ·
    refine ⟨10848020839820159059824409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57856111145707514985730181 10848020839820159059824409)
    ·
      refine ⟨8136015629865119294868307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10848020839820159059824409 8136015629865119294868307)
      ·
        refine ⟨12204023444797678942302461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136015629865119294868307 12204023444797678942302461)
        ·
          refine ⟨4576508791799129603363423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12204023444797678942302461 4576508791799129603363423)
          ·
            refine ⟨6864763187698694405045135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576508791799129603363423 6864763187698694405045135)
            ·
              refine ⟨10297144781548041607567703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864763187698694405045135 10297144781548041607567703)
              ·
                refine ⟨15445717172322062411351555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297144781548041607567703 15445717172322062411351555)
                ·
                  refine ⟨23168575758483093617027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15445717172322062411351555 23168575758483093617027333)
                  ·
                    refine ⟨4344107954715580053192625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23168575758483093617027333 4344107954715580053192625)
                    ·
                      refine ⟨3258080966036685039894469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344107954715580053192625 3258080966036685039894469)
                      ·
                        rfl

theorem cell23_6345090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6345090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345090 prefixEnd_6345090 := by exact prefixLift 6345090
  have htrace : WordTrace (prefixWord ++ tailWord_6345090) baseStart_6345090 baseEnd_6345090 := by
    simpa [prefixWord, tailWord_6345090, baseEnd_6345090] using wordTrace_append hprefix tailTrace_6345090
  have hstable : (prefixWord ++ tailWord_6345090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345090).length < 2 ^ (prefixWord ++ tailWord_6345090).sum := by decide
  have hdescent : baseEnd_6345090 < baseStart_6345090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345095 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_6345095 : Nat := 118140960795 + 6345095 * 2 ^ 59
def prefixEnd_6345095 : Nat := 4983230072969 + 3 ^ 40 * 6345095 * 2
def baseEnd_6345095 : Nat := 3258083533439957520331945

theorem tailTrace_6345095 : CollatzResearch.WordTrace tailWord_6345095 prefixEnd_6345095 3258083533439957520331945 := by
  unfold tailWord_6345095
  simp only [CollatzResearch.WordTrace]
  refine ⟨231424626947811945796852739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154283084631874630531235159 231424626947811945796852739)
  ·
    refine ⟨347136940421717918695279109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231424626947811945796852739 347136940421717918695279109)
    ·
      refine ⟨65088176329072109755364833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347136940421717918695279109 65088176329072109755364833)
      ·
        refine ⟨48816132246804082316523625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65088176329072109755364833 48816132246804082316523625)
        ·
          refine ⟨36612099185103061737392719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48816132246804082316523625 36612099185103061737392719)
          ·
            refine ⟨54918148777654592606089079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36612099185103061737392719 54918148777654592606089079)
            ·
              refine ⟨82377223166481888909133619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54918148777654592606089079 82377223166481888909133619)
              ·
                refine ⟨123565834749722833363700429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82377223166481888909133619 123565834749722833363700429)
                ·
                  refine ⟨46337188031146062511387661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123565834749722833363700429 46337188031146062511387661)
                  ·
                    refine ⟨17376445511679773441770373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46337188031146062511387661 17376445511679773441770373)
                    ·
                      refine ⟨3258083533439957520331945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17376445511679773441770373 3258083533439957520331945)
                      ·
                        rfl

theorem cell23_6345095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_6345095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345095 prefixEnd_6345095 := by exact prefixLift 6345095
  have htrace : WordTrace (prefixWord ++ tailWord_6345095) baseStart_6345095 baseEnd_6345095 := by
    simpa [prefixWord, tailWord_6345095, baseEnd_6345095] using wordTrace_append hprefix tailTrace_6345095
  have hstable : (prefixWord ++ tailWord_6345095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345095).length < 2 ^ (prefixWord ++ tailWord_6345095).sum := by decide
  have hdescent : baseEnd_6345095 < baseStart_6345095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345112 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6345112 : Nat := 118140960795 + 6345112 * 2 ^ 59
def prefixEnd_6345112 : Nat := 4983230072969 + 3 ^ 40 * 6345112 * 2
def baseEnd_6345112 : Nat := 3258092262611083953819367

theorem tailTrace_6345112 : CollatzResearch.WordTrace tailWord_6345112 prefixEnd_6345112 3258092262611083953819367 := by
  unfold tailWord_6345112
  simp only [CollatzResearch.WordTrace]
  refine ⟨115712623494375178850110795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154283497992500238466814393 115712623494375178850110795)
  ·
    refine ⟨173568935241562768275166193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115712623494375178850110795 173568935241562768275166193)
    ·
      refine ⟨130176701431172076206374645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173568935241562768275166193 130176701431172076206374645)
      ·
        refine ⟨12204065759172382144347623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130176701431172076206374645 12204065759172382144347623)
        ·
          refine ⟨18306098638758573216521435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12204065759172382144347623 18306098638758573216521435)
          ·
            refine ⟨27459147958137859824782153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18306098638758573216521435 27459147958137859824782153)
            ·
              refine ⟨20594360968603394868586615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27459147958137859824782153 20594360968603394868586615)
              ·
                refine ⟨30891541452905092302879923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20594360968603394868586615 30891541452905092302879923)
                ·
                  refine ⟨46337312179357638454319885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30891541452905092302879923 46337312179357638454319885)
                  ·
                    refine ⟨17376492067259114420369957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46337312179357638454319885 17376492067259114420369957)
                    ·
                      refine ⟨3258092262611083953819367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17376492067259114420369957 3258092262611083953819367)
                      ·
                        rfl

theorem cell23_6345112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6345112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345112 prefixEnd_6345112 := by exact prefixLift 6345112
  have htrace : WordTrace (prefixWord ++ tailWord_6345112) baseStart_6345112 baseEnd_6345112 := by
    simpa [prefixWord, tailWord_6345112, baseEnd_6345112] using wordTrace_append hprefix tailTrace_6345112
  have hstable : (prefixWord ++ tailWord_6345112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345112).length < 2 ^ (prefixWord ++ tailWord_6345112).sum := by decide
  have hdescent : baseEnd_6345112 < baseStart_6345112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345130 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_6345130 : Nat := 118140960795 + 6345130 * 2 ^ 59
def prefixEnd_6345130 : Nat := 4983230072969 + 3 ^ 40 * 6345130 * 2
def baseEnd_6345130 : Nat := 362011278362540542599365

theorem tailTrace_6345130 : CollatzResearch.WordTrace tailWord_6345130 prefixEnd_6345130 362011278362540542599365 := by
  unfold tailWord_6345130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57856475875671286693594211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154283935668456764516251229 57856475875671286693594211)
  ·
    refine ⟨86784713813506930040391317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57856475875671286693594211 86784713813506930040391317)
    ·
      refine ⟨4068033460008137345643343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86784713813506930040391317 4068033460008137345643343)
      ·
        refine ⟨6102050190012206018465015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068033460008137345643343 6102050190012206018465015)
        ·
          refine ⟨9153075285018309027697523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102050190012206018465015 9153075285018309027697523)
          ·
            refine ⟨13729612927527463541546285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153075285018309027697523 13729612927527463541546285)
            ·
              refine ⟨5148604847822798828079857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13729612927527463541546285 5148604847822798828079857)
              ·
                refine ⟨3861453635867099121059893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5148604847822798828079857 3861453635867099121059893)
                ·
                  refine ⟨362011278362540542599365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3861453635867099121059893 362011278362540542599365)
                  ·
                    rfl

theorem cell23_6345130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_6345130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345130 prefixEnd_6345130 := by exact prefixLift 6345130
  have htrace : WordTrace (prefixWord ++ tailWord_6345130) baseStart_6345130 baseEnd_6345130 := by
    simpa [prefixWord, tailWord_6345130, baseEnd_6345130] using wordTrace_append hprefix tailTrace_6345130
  have hstable : (prefixWord ++ tailWord_6345130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345130).length < 2 ^ (prefixWord ++ tailWord_6345130).sum := by decide
  have hdescent : baseEnd_6345130 < baseStart_6345130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345195 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 6]
def baseStart_6345195 : Nat := 118140960795 + 6345195 * 2 ^ 59
def prefixEnd_6345195 : Nat := 4983230072969 + 3 ^ 40 * 6345195 * 2
def baseEnd_6345195 : Nat := 1086044960501802376360495

theorem tailTrace_6345195 : CollatzResearch.WordTrace tailWord_6345195 prefixEnd_6345195 1086044960501802376360495 := by
  unfold tailWord_6345195
  simp only [CollatzResearch.WordTrace]
  refine ⟨231428274247449662875493039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154285516164966441916995359 231428274247449662875493039)
  ·
    refine ⟨347142411371174494313239559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231428274247449662875493039 347142411371174494313239559)
    ·
      refine ⟨520713617056761741469859339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347142411371174494313239559 520713617056761741469859339)
      ·
        refine ⟨781070425585142612204789009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520713617056761741469859339 781070425585142612204789009)
        ·
          refine ⟨585802819188856959153591757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781070425585142612204789009 585802819188856959153591757)
          ·
            refine ⟨219676057195821359682596909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585802819188856959153591757 219676057195821359682596909)
            ·
              refine ⟨82378521448433009880973841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219676057195821359682596909 82378521448433009880973841)
              ·
                refine ⟨61783891086324757410730381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82378521448433009880973841 61783891086324757410730381)
                ·
                  refine ⟨23168959157371784029023893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61783891086324757410730381 23168959157371784029023893)
                  ·
                    refine ⟨1086044960501802376360495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23168959157371784029023893 1086044960501802376360495)
                    ·
                      rfl

theorem cell23_6345195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_6345195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345195 prefixEnd_6345195 := by exact prefixLift 6345195
  have htrace : WordTrace (prefixWord ++ tailWord_6345195) baseStart_6345195 baseEnd_6345195 := by
    simpa [prefixWord, tailWord_6345195, baseEnd_6345195] using wordTrace_append hprefix tailTrace_6345195
  have hstable : (prefixWord ++ tailWord_6345195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345195).length < 2 ^ (prefixWord ++ tailWord_6345195).sum := by decide
  have hdescent : baseEnd_6345195 < baseStart_6345195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345196 : List Nat := [2, 2, 1, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_6345196 : Nat := 118140960795 + 6345196 * 2 ^ 59
def prefixEnd_6345196 : Nat := 4983230072969 + 3 ^ 40 * 6345196 * 2
def baseEnd_6345196 : Nat := 3258135394986061625168981

theorem tailTrace_6345196 : CollatzResearch.WordTrace tailWord_6345196 prefixEnd_6345196 3258135394986061625168981 := by
  unfold tailWord_6345196
  simp only [CollatzResearch.WordTrace]
  refine ⟨115714155360223020023139721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154285540480297360030852961 115714155360223020023139721)
  ·
    refine ⟨86785616520167265017354791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115714155360223020023139721 86785616520167265017354791)
    ·
      refine ⟨130178424780250897526032187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86785616520167265017354791 130178424780250897526032187)
      ·
        refine ⟨195267637170376346289048281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130178424780250897526032187 195267637170376346289048281)
        ·
          refine ⟨146450727877782259716786211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195267637170376346289048281 146450727877782259716786211)
          ·
            refine ⟨219676091816673389575179317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146450727877782259716786211 219676091816673389575179317)
            ·
              refine ⟨20594633607813130272673061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219676091816673389575179317 20594633607813130272673061)
              ·
                refine ⟨3861493801464961926126199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20594633607813130272673061 3861493801464961926126199)
                ·
                  refine ⟨5792240702197442889189299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861493801464961926126199 5792240702197442889189299)
                  ·
                    refine ⟨8688361053296164333783949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792240702197442889189299 8688361053296164333783949)
                    ·
                      refine ⟨3258135394986061625168981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688361053296164333783949 3258135394986061625168981)
                      ·
                        rfl

theorem cell23_6345196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_6345196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345196 prefixEnd_6345196 := by exact prefixLift 6345196
  have htrace : WordTrace (prefixWord ++ tailWord_6345196) baseStart_6345196 baseEnd_6345196 := by
    simpa [prefixWord, tailWord_6345196, baseEnd_6345196] using wordTrace_append hprefix tailTrace_6345196
  have hstable : (prefixWord ++ tailWord_6345196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345196).length < 2 ^ (prefixWord ++ tailWord_6345196).sum := by decide
  have hdescent : baseEnd_6345196 < baseStart_6345196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345212 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_6345212 : Nat := 118140960795 + 6345212 * 2 ^ 59
def prefixEnd_6345212 : Nat := 4983230072969 + 3 ^ 40 * 6345212 * 2
def baseEnd_6345212 : Nat := 1086047870225511187522969

theorem tailTrace_6345212 : CollatzResearch.WordTrace tailWord_6345212 prefixEnd_6345212 1086047870225511187522969 := by
  unfold tailWord_6345212
  simp only [CollatzResearch.WordTrace]
  refine ⟨115714447144194037389430945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154285929525592049852574593 115714447144194037389430945)
  ·
    refine ⟨86785835358145528042073209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115714447144194037389430945 86785835358145528042073209)
    ·
      refine ⟨65089376518609146031554907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86785835358145528042073209 65089376518609146031554907)
      ·
        refine ⟨97634064777913719047332361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65089376518609146031554907 97634064777913719047332361)
        ·
          refine ⟨73225548583435289285499271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97634064777913719047332361 73225548583435289285499271)
          ·
            refine ⟨109838322875152933928248907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73225548583435289285499271 109838322875152933928248907)
            ·
              refine ⟨164757484312729400892373361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109838322875152933928248907 164757484312729400892373361)
              ·
                refine ⟨123568113234547050669280021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164757484312729400892373361 123568113234547050669280021)
                ·
                  refine ⟨5792255307869393000122501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123568113234547050669280021 5792255307869393000122501)
                  ·
                    refine ⟨1086047870225511187522969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792255307869393000122501 1086047870225511187522969)
                    ·
                      rfl

theorem cell23_6345212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_6345212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345212 prefixEnd_6345212 := by exact prefixLift 6345212
  have htrace : WordTrace (prefixWord ++ tailWord_6345212) baseStart_6345212 baseEnd_6345212 := by
    simpa [prefixWord, tailWord_6345212, baseEnd_6345212] using wordTrace_append hprefix tailTrace_6345212
  have hstable : (prefixWord ++ tailWord_6345212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345212).length < 2 ^ (prefixWord ++ tailWord_6345212).sum := by decide
  have hdescent : baseEnd_6345212 < baseStart_6345212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345223 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6345223 : Nat := 118140960795 + 6345223 * 2 ^ 59
def prefixEnd_6345223 : Nat := 4983230072969 + 3 ^ 40 * 6345223 * 2
def baseEnd_6345223 : Nat := 3258149258963733019531357

theorem tailTrace_6345223 : CollatzResearch.WordTrace tailWord_6345223 prefixEnd_6345223 3258149258963733019531357 := by
  unfold tailWord_6345223
  simp only [CollatzResearch.WordTrace]
  refine ⟨231429295491348223657512323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154286196994232149105008215 231429295491348223657512323)
  ·
    refine ⟨347143943237022335486268485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231429295491348223657512323 347143943237022335486268485)
    ·
      refine ⟨65089489356941687903675341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347143943237022335486268485 65089489356941687903675341)
      ·
        refine ⟨24408558508853132963878253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65089489356941687903675341 24408558508853132963878253)
        ·
          refine ⟨9153209440819924861454345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24408558508853132963878253 9153209440819924861454345)
          ·
            refine ⟨6864907080614943646090759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9153209440819924861454345 6864907080614943646090759)
            ·
              refine ⟨10297360620922415469136139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864907080614943646090759 10297360620922415469136139)
              ·
                refine ⟨15446040931383623203704209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297360620922415469136139 15446040931383623203704209)
                ·
                  refine ⟨11584530698537717402778157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15446040931383623203704209 11584530698537717402778157)
                  ·
                    refine ⟨4344199011951644026041809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11584530698537717402778157 4344199011951644026041809)
                    ·
                      refine ⟨3258149258963733019531357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344199011951644026041809 3258149258963733019531357)
                      ·
                        rfl

theorem cell23_6345223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6345223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345223 prefixEnd_6345223 := by exact prefixLift 6345223
  have htrace : WordTrace (prefixWord ++ tailWord_6345223) baseStart_6345223 baseEnd_6345223 := by
    simpa [prefixWord, tailWord_6345223, baseEnd_6345223] using wordTrace_append hprefix tailTrace_6345223
  have hstable : (prefixWord ++ tailWord_6345223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345223).length < 2 ^ (prefixWord ++ tailWord_6345223).sum := by decide
  have hdescent : baseEnd_6345223 < baseStart_6345223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345253 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_6345253 : Nat := 118140960795 + 6345253 * 2 ^ 59
def prefixEnd_6345253 : Nat := 4983230072969 + 3 ^ 40 * 6345253 * 2
def baseEnd_6345253 : Nat := 3258164663383367902156219

theorem tailTrace_6345253 : CollatzResearch.WordTrace tailWord_6345253 prefixEnd_6345253 3258164663383367902156219 := by
  unfold tailWord_6345253
  simp only [CollatzResearch.WordTrace]
  refine ⟨231430389681239538781104413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154286926454159692520736275 231430389681239538781104413)
  ·
    refine ⟨86786396130464827042914155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231430389681239538781104413 86786396130464827042914155)
    ·
      refine ⟨130179594195697240564371233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86786396130464827042914155 130179594195697240564371233)
      ·
        refine ⟨97634695646772930423278425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130179594195697240564371233 97634695646772930423278425)
        ·
          refine ⟨73226021735079697817458819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97634695646772930423278425 73226021735079697817458819)
          ·
            refine ⟨109839032602619546726188229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73226021735079697817458819 109839032602619546726188229)
            ·
              refine ⟨20594818612991165011160293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109839032602619546726188229 20594818612991165011160293)
              ·
                refine ⟨3861528489935843439592555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20594818612991165011160293 3861528489935843439592555)
                ·
                  refine ⟨5792292734903765159388833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861528489935843439592555 5792292734903765159388833)
                  ·
                    refine ⟨4344219551177823869541625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5792292734903765159388833 4344219551177823869541625)
                    ·
                      refine ⟨3258164663383367902156219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344219551177823869541625 3258164663383367902156219)
                      ·
                        rfl

theorem cell23_6345253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_6345253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345253 prefixEnd_6345253 := by exact prefixLift 6345253
  have htrace : WordTrace (prefixWord ++ tailWord_6345253) baseStart_6345253 baseEnd_6345253 := by
    simpa [prefixWord, tailWord_6345253, baseEnd_6345253] using wordTrace_append hprefix tailTrace_6345253
  have hstable : (prefixWord ++ tailWord_6345253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345253).length < 2 ^ (prefixWord ++ tailWord_6345253).sum := by decide
  have hdescent : baseEnd_6345253 < baseStart_6345253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345330 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6345330 : Nat := 118140960795 + 6345330 * 2 ^ 59
def prefixEnd_6345330 : Nat := 4983230072969 + 3 ^ 40 * 6345330 * 2
def baseEnd_6345330 : Nat := 3258204201393764100893365

theorem tailTrace_6345330 : CollatzResearch.WordTrace tailWord_6345330 prefixEnd_6345330 3258204201393764100893365 := by
  unfold tailWord_6345330
  simp only [CollatzResearch.WordTrace]
  refine ⟨57858299525490145232914361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154288798734640387287771629 57858299525490145232914361)
  ·
    refine ⟨43393724644117608924685771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57858299525490145232914361 43393724644117608924685771)
    ·
      refine ⟨65090586966176413387028657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43393724644117608924685771 65090586966176413387028657)
      ·
        refine ⟨48817940224632310040271493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65090586966176413387028657 48817940224632310040271493)
        ·
          refine ⟨9153363792118558132550905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48817940224632310040271493 9153363792118558132550905)
          ·
            refine ⟨6865022844088918599413179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9153363792118558132550905 6865022844088918599413179)
            ·
              refine ⟨10297534266133377899119769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865022844088918599413179 10297534266133377899119769)
              ·
                refine ⟨7723150699600033424339827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10297534266133377899119769 7723150699600033424339827)
                ·
                  refine ⟨11584726049400050136509741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7723150699600033424339827 11584726049400050136509741)
                  ·
                    refine ⟨4344272268525018801191153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11584726049400050136509741 4344272268525018801191153)
                    ·
                      refine ⟨3258204201393764100893365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344272268525018801191153 3258204201393764100893365)
                      ·
                        rfl

theorem cell23_6345330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6345330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345330 prefixEnd_6345330 := by exact prefixLift 6345330
  have htrace : WordTrace (prefixWord ++ tailWord_6345330) baseStart_6345330 baseEnd_6345330 := by
    simpa [prefixWord, tailWord_6345330, baseEnd_6345330] using wordTrace_append hprefix tailTrace_6345330
  have hstable : (prefixWord ++ tailWord_6345330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345330).length < 2 ^ (prefixWord ++ tailWord_6345330).sum := by decide
  have hdescent : baseEnd_6345330 < baseStart_6345330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345369 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 7, 2]
def baseStart_6345369 : Nat := 118140960795 + 6345369 * 2 ^ 59
def prefixEnd_6345369 : Nat := 4983230072969 + 3 ^ 40 * 6345369 * 2
def baseEnd_6345369 : Nat := 3258224227139289448305685

theorem tailTrace_6345369 : CollatzResearch.WordTrace tailWord_6345369 prefixEnd_6345369 3258224227139289448305685 := by
  unfold tailWord_6345369
  simp only [CollatzResearch.WordTrace]
  refine ⟨231434620548819290592327161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154289747032546193728218107 231434620548819290592327161)
  ·
    refine ⟨173575965411614467944245371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231434620548819290592327161 173575965411614467944245371)
    ·
      refine ⟨260363948117421701916368057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173575965411614467944245371 260363948117421701916368057)
      ·
        refine ⟨195272961088066276437276043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260363948117421701916368057 195272961088066276437276043)
        ·
          refine ⟨292909441632099414655914065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195272961088066276437276043 292909441632099414655914065)
          ·
            refine ⟨219682081224074560991935549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292909441632099414655914065 219682081224074560991935549)
            ·
              refine ⟨82380780459027960371975831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219682081224074560991935549 82380780459027960371975831)
              ·
                refine ⟨123571170688541940557963747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82380780459027960371975831 123571170688541940557963747)
                ·
                  refine ⟨185356756032812910836945621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123571170688541940557963747 185356756032812910836945621)
                  ·
                    refine ⟨4344298969519052597740913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185356756032812910836945621 4344298969519052597740913)
                    ·
                      refine ⟨3258224227139289448305685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344298969519052597740913 3258224227139289448305685)
                      ·
                        rfl

theorem cell23_6345369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_6345369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345369 prefixEnd_6345369 := by exact prefixLift 6345369
  have htrace : WordTrace (prefixWord ++ tailWord_6345369) baseStart_6345369 baseEnd_6345369 := by
    simpa [prefixWord, tailWord_6345369, baseEnd_6345369] using wordTrace_append hprefix tailTrace_6345369
  have hstable : (prefixWord ++ tailWord_6345369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345369).length < 2 ^ (prefixWord ++ tailWord_6345369).sum := by decide
  have hdescent : baseEnd_6345369 < baseStart_6345369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345376 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_6345376 : Nat := 118140960795 + 6345376 * 2 ^ 59
def prefixEnd_6345376 : Nat := 4983230072969 + 3 ^ 40 * 6345376 * 2
def baseEnd_6345376 : Nat := 3258227821503870920918153

theorem tailTrace_6345376 : CollatzResearch.WordTrace tailWord_6345376 prefixEnd_6345376 3258227821503870920918153 := by
  unfold tailWord_6345376
  simp only [CollatzResearch.WordTrace]
  refine ⟨115717437929896965393915991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154289917239862620525221321 115717437929896965393915991)
  ·
    refine ⟨173576156894845448090873987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115717437929896965393915991 173576156894845448090873987)
    ·
      refine ⟨260364235342268172136310981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173576156894845448090873987 260364235342268172136310981)
      ·
        refine ⟨48818294126675282275558309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260364235342268172136310981 48818294126675282275558309)
        ·
          refine ⟨9153430148751615426667183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48818294126675282275558309 9153430148751615426667183)
          ·
            refine ⟨13730145223127423140000775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153430148751615426667183 13730145223127423140000775)
            ·
              refine ⟨20595217834691134710001163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13730145223127423140000775 20595217834691134710001163)
              ·
                refine ⟨30892826752036702065001745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20595217834691134710001163 30892826752036702065001745)
                ·
                  refine ⟨23169620064027526548751309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30892826752036702065001745 23169620064027526548751309)
                  ·
                    refine ⟨8688607524010322455781741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23169620064027526548751309 8688607524010322455781741)
                    ·
                      refine ⟨3258227821503870920918153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688607524010322455781741 3258227821503870920918153)
                      ·
                        rfl

theorem cell23_6345376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_6345376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345376 prefixEnd_6345376 := by exact prefixLift 6345376
  have htrace : WordTrace (prefixWord ++ tailWord_6345376) baseStart_6345376 baseEnd_6345376 := by
    simpa [prefixWord, tailWord_6345376, baseEnd_6345376] using wordTrace_append hprefix tailTrace_6345376
  have hstable : (prefixWord ++ tailWord_6345376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345376).length < 2 ^ (prefixWord ++ tailWord_6345376).sum := by decide
  have hdescent : baseEnd_6345376 < baseStart_6345376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345416 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_6345416 : Nat := 118140960795 + 6345416 * 2 ^ 59
def prefixEnd_6345416 : Nat := 4983230072969 + 3 ^ 40 * 6345416 * 2
def baseEnd_6345416 : Nat := 3258248360730050764417969

theorem tailTrace_6345416 : CollatzResearch.WordTrace tailWord_6345416 prefixEnd_6345416 3258248360730050764417969 := by
  unfold tailWord_6345416
  simp only [CollatzResearch.WordTrace]
  refine ⟨115718167389824508809644051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154290889853099345079525401 115718167389824508809644051)
  ·
    refine ⟨173577251084736763214466077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115718167389824508809644051 173577251084736763214466077)
    ·
      refine ⟨65091469156776286205424779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173577251084736763214466077 65091469156776286205424779)
      ·
        refine ⟨97637203735164429308137169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65091469156776286205424779 97637203735164429308137169)
        ·
          refine ⟨73227902801373321981102877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97637203735164429308137169 73227902801373321981102877)
          ·
            refine ⟨27460463550514995742913579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73227902801373321981102877 27460463550514995742913579)
            ·
              refine ⟨41190695325772493614370369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27460463550514995742913579 41190695325772493614370369)
              ·
                refine ⟨30893021494329370210777777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41190695325772493614370369 30893021494329370210777777)
                ·
                  refine ⟨23169766120747027658083333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30893021494329370210777777 23169766120747027658083333)
                  ·
                    refine ⟨4344331147640067685890625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23169766120747027658083333 4344331147640067685890625)
                    ·
                      refine ⟨3258248360730050764417969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344331147640067685890625 3258248360730050764417969)
                      ·
                        rfl

theorem cell23_6345416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_6345416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345416 prefixEnd_6345416 := by exact prefixLift 6345416
  have htrace : WordTrace (prefixWord ++ tailWord_6345416) baseStart_6345416 baseEnd_6345416 := by
    simpa [prefixWord, tailWord_6345416, baseEnd_6345416] using wordTrace_append hprefix tailTrace_6345416
  have hstable : (prefixWord ++ tailWord_6345416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345416).length < 2 ^ (prefixWord ++ tailWord_6345416).sum := by decide
  have hdescent : baseEnd_6345416 < baseStart_6345416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345466 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_6345466 : Nat := 118140960795 + 6345466 * 2 ^ 59
def prefixEnd_6345466 : Nat := 4983230072969 + 3 ^ 40 * 6345466 * 2
def baseEnd_6345466 : Nat := 3258274034762775568792739

theorem tailTrace_6345466 : CollatzResearch.WordTrace tailWord_6345466 prefixEnd_6345466 3258274034762775568792739 := by
  unfold tailWord_6345466
  simp only [CollatzResearch.WordTrace]
  refine ⟨57859539607366969039652063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154292105619645250772405501 57859539607366969039652063)
  ·
    refine ⟨86789309411050453559478095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57859539607366969039652063 86789309411050453559478095)
    ·
      refine ⟨130183964116575680339217143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86789309411050453559478095 130183964116575680339217143)
      ·
        refine ⟨195275946174863520508825715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130183964116575680339217143 195275946174863520508825715)
        ·
          refine ⟨292913919262295280763238573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195275946174863520508825715 292913919262295280763238573)
          ·
            refine ⟨109842719723360730286214465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292913919262295280763238573 109842719723360730286214465)
            ·
              refine ⟨82382039792520547714660849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109842719723360730286214465 82382039792520547714660849)
              ·
                refine ⟨61786529844390410785995637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82382039792520547714660849 61786529844390410785995637)
                ·
                  refine ⟨5792487172911601011187091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61786529844390410785995637 5792487172911601011187091)
                  ·
                    refine ⟨8688730759367401516780637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792487172911601011187091 8688730759367401516780637)
                    ·
                      refine ⟨3258274034762775568792739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688730759367401516780637 3258274034762775568792739)
                      ·
                        rfl

theorem cell23_6345466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_6345466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345466 prefixEnd_6345466 := by exact prefixLift 6345466
  have htrace : WordTrace (prefixWord ++ tailWord_6345466) baseStart_6345466 baseEnd_6345466 := by
    simpa [prefixWord, tailWord_6345466, baseEnd_6345466] using wordTrace_append hprefix tailTrace_6345466
  have hstable : (prefixWord ++ tailWord_6345466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345466).length < 2 ^ (prefixWord ++ tailWord_6345466).sum := by decide
  have hdescent : baseEnd_6345466 < baseStart_6345466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345503 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 1, 5]
def baseStart_6345503 : Nat := 118140960795 + 6345503 * 2 ^ 59
def prefixEnd_6345503 : Nat := 4983230072969 + 3 ^ 40 * 6345503 * 2
def baseEnd_6345503 : Nat := 1086097677848997308010023

theorem tailTrace_6345503 : CollatzResearch.WordTrace tailWord_6345503 prefixEnd_6345503 1086097677848997308010023 := by
  unfold tailWord_6345503
  simp only [CollatzResearch.WordTrace]
  refine ⟨231439507930333831477705163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154293005286889220985136775 231439507930333831477705163)
  ·
    refine ⟨347159261895500747216557745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231439507930333831477705163 347159261895500747216557745)
    ·
      refine ⟨260369446421625560412418309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347159261895500747216557745 260369446421625560412418309)
      ·
        refine ⟨48819271204054792577328433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260369446421625560412418309 48819271204054792577328433)
        ·
          refine ⟨36614453403041094432996325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48819271204054792577328433 36614453403041094432996325)
          ·
            refine ⟨6865210013070205206186811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36614453403041094432996325 6865210013070205206186811)
            ·
              refine ⟨10297815019605307809280217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865210013070205206186811 10297815019605307809280217)
              ·
                refine ⟨7723361264703980856960163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10297815019605307809280217 7723361264703980856960163)
                ·
                  refine ⟨11585041897055971285440245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7723361264703980856960163 11585041897055971285440245)
                  ·
                    refine ⟨1086097677848997308010023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11585041897055971285440245 1086097677848997308010023)
                    ·
                      rfl

theorem cell23_6345503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_6345503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345503 prefixEnd_6345503 := by exact prefixLift 6345503
  have htrace : WordTrace (prefixWord ++ tailWord_6345503) baseStart_6345503 baseEnd_6345503 := by
    simpa [prefixWord, tailWord_6345503, baseEnd_6345503] using wordTrace_append hprefix tailTrace_6345503
  have hstable : (prefixWord ++ tailWord_6345503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345503).length < 2 ^ (prefixWord ++ tailWord_6345503).sum := by decide
  have hdescent : baseEnd_6345503 < baseStart_6345503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345553 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_6345553 : Nat := 118140960795 + 6345553 * 2 ^ 59
def prefixEnd_6345553 : Nat := 4983230072969 + 3 ^ 40 * 6345553 * 2
def baseEnd_6345553 : Nat := 3258318707579716728404839

theorem tailTrace_6345553 : CollatzResearch.WordTrace tailWord_6345553 prefixEnd_6345553 3258318707579716728404839 := by
  unfold tailWord_6345553
  simp only [CollatzResearch.WordTrace]
  refine ⟨231441331580152690017025313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154294221053435126678016875 231441331580152690017025313)
  ·
    refine ⟨173580998685114517512768985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231441331580152690017025313 173580998685114517512768985)
    ·
      refine ⟨130185749013835888134576739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173580998685114517512768985 130185749013835888134576739)
      ·
        refine ⟨195278623520753832201865109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130185749013835888134576739 195278623520753832201865109)
        ·
          refine ⟨9153685477535335884462427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195278623520753832201865109 9153685477535335884462427)
          ·
            refine ⟨13730528216303003826693641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153685477535335884462427 13730528216303003826693641)
            ·
              refine ⟨10297896162227252870020231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13730528216303003826693641 10297896162227252870020231)
              ·
                refine ⟨15446844243340879305030347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297896162227252870020231 15446844243340879305030347)
                ·
                  refine ⟨23170266365011318957545521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15446844243340879305030347 23170266365011318957545521)
                  ·
                    refine ⟨17377699773758489218159141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23170266365011318957545521 17377699773758489218159141)
                    ·
                      refine ⟨3258318707579716728404839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17377699773758489218159141 3258318707579716728404839)
                      ·
                        rfl

theorem cell23_6345553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_6345553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345553 prefixEnd_6345553 := by exact prefixLift 6345553
  have htrace : WordTrace (prefixWord ++ tailWord_6345553) baseStart_6345553 baseEnd_6345553 := by
    simpa [prefixWord, tailWord_6345553, baseEnd_6345553] using wordTrace_append hprefix tailTrace_6345553
  have hstable : (prefixWord ++ tailWord_6345553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345553).length < 2 ^ (prefixWord ++ tailWord_6345553).sum := by decide
  have hdescent : baseEnd_6345553 < baseStart_6345553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345607 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_6345607 : Nat := 118140960795 + 6345607 * 2 ^ 59
def prefixEnd_6345607 : Nat := 4983230072969 + 3 ^ 40 * 6345607 * 2
def baseEnd_6345607 : Nat := 3258346435535059517129591

theorem tailTrace_6345607 : CollatzResearch.WordTrace tailWord_6345607 prefixEnd_6345607 3258346435535059517129591 := by
  unfold tailWord_6345607
  simp only [CollatzResearch.WordTrace]
  refine ⟨231443301121957057239491075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154295534081304704826327383 231443301121957057239491075)
  ·
    refine ⟨347164951682935585859236613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231443301121957057239491075 347164951682935585859236613)
    ·
      refine ⟨65093428440550422348606865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347164951682935585859236613 65093428440550422348606865)
      ·
        refine ⟨48820071330412816761455149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65093428440550422348606865 48820071330412816761455149)
        ·
          refine ⟨18307526748904806285545681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48820071330412816761455149 18307526748904806285545681)
          ·
            refine ⟨13730645061678604714159261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18307526748904806285545681 13730645061678604714159261)
            ·
              refine ⟨5148991898129476767809723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13730645061678604714159261 5148991898129476767809723)
              ·
                refine ⟨7723487847194215151714585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5148991898129476767809723 7723487847194215151714585)
                ·
                  refine ⟨5792615885395661363785939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723487847194215151714585 5792615885395661363785939)
                  ·
                    refine ⟨8688923828093492045678909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792615885395661363785939 8688923828093492045678909)
                    ·
                      refine ⟨3258346435535059517129591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8688923828093492045678909 3258346435535059517129591)
                      ·
                        rfl

theorem cell23_6345607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_6345607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345607 prefixEnd_6345607 := by exact prefixLift 6345607
  have htrace : WordTrace (prefixWord ++ tailWord_6345607) baseStart_6345607 baseEnd_6345607 := by
    simpa [prefixWord, tailWord_6345607, baseEnd_6345607] using wordTrace_append hprefix tailTrace_6345607
  have hstable : (prefixWord ++ tailWord_6345607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345607).length < 2 ^ (prefixWord ++ tailWord_6345607).sum := by decide
  have hdescent : baseEnd_6345607 < baseStart_6345607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345619 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 9]
def baseStart_6345619 : Nat := 118140960795 + 6345619 * 2 ^ 59
def prefixEnd_6345619 : Nat := 4983230072969 + 3 ^ 40 * 6345619 * 2
def baseEnd_6345619 : Nat := 362039177478101496686615

theorem tailTrace_6345619 : CollatzResearch.WordTrace tailWord_6345619 prefixEnd_6345619 362039177478101496686615 := by
  unfold tailWord_6345619
  simp only [CollatzResearch.WordTrace]
  refine ⟨231443738797913583288927911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154295825865275722192618607 231443738797913583288927911)
  ·
    refine ⟨347165608196870374933391867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231443738797913583288927911 347165608196870374933391867)
    ·
      refine ⟨520748412295305562400087801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347165608196870374933391867 520748412295305562400087801)
      ·
        refine ⟨390561309221479171800065851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520748412295305562400087801 390561309221479171800065851)
        ·
          refine ⟨585841963832218757700098777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390561309221479171800065851 585841963832218757700098777)
          ·
            refine ⟨439381472874164068275074083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585841963832218757700098777 439381472874164068275074083)
            ·
              refine ⟨659072209311246102412611125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439381472874164068275074083 659072209311246102412611125)
              ·
                refine ⟨61788019622929322101182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659072209311246102412611125 61788019622929322101182293)
                ·
                  refine ⟨362039177478101496686615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61788019622929322101182293 362039177478101496686615)
                  ·
                    rfl

theorem cell23_6345619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 9].length) (baseStart_6345619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345619 prefixEnd_6345619 := by exact prefixLift 6345619
  have htrace : WordTrace (prefixWord ++ tailWord_6345619) baseStart_6345619 baseEnd_6345619 := by
    simpa [prefixWord, tailWord_6345619, baseEnd_6345619] using wordTrace_append hprefix tailTrace_6345619
  have hstable : (prefixWord ++ tailWord_6345619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345619).length < 2 ^ (prefixWord ++ tailWord_6345619).sum := by decide
  have hdescent : baseEnd_6345619 < baseStart_6345619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345633 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6345633 : Nat := 118140960795 + 6345633 * 2 ^ 59
def prefixEnd_6345633 : Nat := 4983230072969 + 3 ^ 40 * 6345633 * 2
def baseEnd_6345633 : Nat := 3258359786032076415404471

theorem tailTrace_6345633 : CollatzResearch.WordTrace tailWord_6345633 prefixEnd_6345633 3258359786032076415404471 := by
  unfold tailWord_6345633
  simp only [CollatzResearch.WordTrace]
  refine ⟨231444249419862863679937553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154296166279908575786625035 231444249419862863679937553)
  ·
    refine ⟨173583187064897147759953165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231444249419862863679937553 173583187064897147759953165)
    ·
      refine ⟨65093695149336430409982437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173583187064897147759953165 65093695149336430409982437)
      ·
        refine ⟨12205067840500580701871707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65093695149336430409982437 12205067840500580701871707)
        ·
          refine ⟨18307601760750871052807561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205067840500580701871707 18307601760750871052807561)
          ·
            refine ⟨13730701320563153289605671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18307601760750871052807561 13730701320563153289605671)
            ·
              refine ⟨20596051980844729934408507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13730701320563153289605671 20596051980844729934408507)
              ·
                refine ⟨30894077971267094901612761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20596051980844729934408507 30894077971267094901612761)
                ·
                  refine ⟨23170558478450321176209571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30894077971267094901612761 23170558478450321176209571)
                  ·
                    refine ⟨34755837717675481764314357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23170558478450321176209571 34755837717675481764314357)
                    ·
                      refine ⟨3258359786032076415404471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34755837717675481764314357 3258359786032076415404471)
                      ·
                        rfl

theorem cell23_6345633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6345633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345633 prefixEnd_6345633 := by exact prefixLift 6345633
  have htrace : WordTrace (prefixWord ++ tailWord_6345633) baseStart_6345633 baseEnd_6345633 := by
    simpa [prefixWord, tailWord_6345633, baseEnd_6345633] using wordTrace_append hprefix tailTrace_6345633
  have hstable : (prefixWord ++ tailWord_6345633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345633).length < 2 ^ (prefixWord ++ tailWord_6345633).sum := by decide
  have hdescent : baseEnd_6345633 < baseStart_6345633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345664 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2]
def baseStart_6345664 : Nat := 118140960795 + 6345664 * 2 ^ 59
def prefixEnd_6345664 : Nat := 4983230072969 + 3 ^ 40 * 6345664 * 2
def baseEnd_6345664 : Nat := 3258375703932365794116829

theorem tailTrace_6345664 : CollatzResearch.WordTrace tailWord_6345664 prefixEnd_6345664 3258375703932365794116829 := by
  unfold tailWord_6345664
  simp only [CollatzResearch.WordTrace]
  refine ⟨115722690041375277987158023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154296920055167037316210697 115722690041375277987158023)
  ·
    refine ⟨173584035062062916980737035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115722690041375277987158023 173584035062062916980737035)
    ·
      refine ⟨260376052593094375471105553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173584035062062916980737035 260376052593094375471105553)
      ·
        refine ⟨195282039444820781603329165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260376052593094375471105553 195282039444820781603329165)
        ·
          refine ⟨73230764791807793101248437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195282039444820781603329165 73230764791807793101248437)
          ·
            refine ⟨6865384199231980603242041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73230764791807793101248437 6865384199231980603242041)
            ·
              refine ⟨5149038149423985452431531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865384199231980603242041 5149038149423985452431531)
              ·
                refine ⟨7723557224135978178647297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149038149423985452431531 7723557224135978178647297)
                ·
                  refine ⟨5792667918101983633985473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723557224135978178647297 5792667918101983633985473)
                  ·
                    refine ⟨4344500938576487725489105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5792667918101983633985473 4344500938576487725489105)
                    ·
                      refine ⟨3258375703932365794116829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344500938576487725489105 3258375703932365794116829)
                      ·
                        rfl

theorem cell23_6345664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_6345664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345664 prefixEnd_6345664 := by exact prefixLift 6345664
  have htrace : WordTrace (prefixWord ++ tailWord_6345664) baseStart_6345664 baseEnd_6345664 := by
    simpa [prefixWord, tailWord_6345664, baseEnd_6345664] using wordTrace_append hprefix tailTrace_6345664
  have hstable : (prefixWord ++ tailWord_6345664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345664).length < 2 ^ (prefixWord ++ tailWord_6345664).sum := by decide
  have hdescent : baseEnd_6345664 < baseStart_6345664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345676 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6345676 : Nat := 118140960795 + 6345676 * 2 ^ 59
def prefixEnd_6345676 : Nat := 4983230072969 + 3 ^ 40 * 6345676 * 2
def baseEnd_6345676 : Nat := 3258381865700219747166773

theorem tailTrace_6345676 : CollatzResearch.WordTrace tailWord_6345676 prefixEnd_6345676 3258381865700219747166773 := by
  unfold tailWord_6345676
  simp only [CollatzResearch.WordTrace]
  refine ⟨115722908879353541011876441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154297211839138054682501921 115722908879353541011876441)
  ·
    refine ⟨86792181659515155758907331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115722908879353541011876441 86792181659515155758907331)
    ·
      refine ⟨130188272489272733638360997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86792181659515155758907331 130188272489272733638360997)
      ·
        refine ⟨24410301091738637557192687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130188272489272733638360997 24410301091738637557192687)
        ·
          refine ⟨36615451637607956335789031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24410301091738637557192687 36615451637607956335789031)
          ·
            refine ⟨54923177456411934503683547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36615451637607956335789031 54923177456411934503683547)
            ·
              refine ⟨82384766184617901755525321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54923177456411934503683547 82384766184617901755525321)
              ·
                refine ⟨61788574638463426316643991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82384766184617901755525321 61788574638463426316643991)
                ·
                  refine ⟨92682861957695139474965987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61788574638463426316643991 92682861957695139474965987)
                  ·
                    refine ⟨139024292936542709212448981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92682861957695139474965987 139024292936542709212448981)
                    ·
                      refine ⟨3258381865700219747166773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139024292936542709212448981 3258381865700219747166773)
                      ·
                        rfl

theorem cell23_6345676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6345676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345676 prefixEnd_6345676 := by exact prefixLift 6345676
  have htrace : WordTrace (prefixWord ++ tailWord_6345676) baseStart_6345676 baseEnd_6345676 := by
    simpa [prefixWord, tailWord_6345676, baseEnd_6345676] using wordTrace_append hprefix tailTrace_6345676
  have hstable : (prefixWord ++ tailWord_6345676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345676).length < 2 ^ (prefixWord ++ tailWord_6345676).sum := by decide
  have hdescent : baseEnd_6345676 < baseStart_6345676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345693 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6345693 : Nat := 118140960795 + 6345693 * 2 ^ 59
def prefixEnd_6345693 : Nat := 4983230072969 + 3 ^ 40 * 6345693 * 2
def baseEnd_6345693 : Nat := 3258390594871346180654195

theorem tailTrace_6345693 : CollatzResearch.WordTrace tailWord_6345693 prefixEnd_6345693 3258390594871346180654195 := by
  unfold tailWord_6345693
  simp only [CollatzResearch.WordTrace]
  refine ⟨231446437799645493927121733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154297625199763662618081155 231446437799645493927121733)
  ·
    refine ⟨43396207087433530111335325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231446437799645493927121733 43396207087433530111335325)
    ·
      refine ⟨16273577657787573791750747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43396207087433530111335325 16273577657787573791750747)
      ·
        refine ⟨24410366486681360687626121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16273577657787573791750747 24410366486681360687626121)
        ·
          refine ⟨18307774865011020515719591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24410366486681360687626121 18307774865011020515719591)
          ·
            refine ⟨27461662297516530773579387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18307774865011020515719591 27461662297516530773579387)
            ·
              refine ⟨41192493446274796160369081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27461662297516530773579387 41192493446274796160369081)
              ·
                refine ⟨30894370084706097120276811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41192493446274796160369081 30894370084706097120276811)
                ·
                  refine ⟨46341555127059145680415217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30894370084706097120276811 46341555127059145680415217)
                  ·
                    refine ⟨34756166345294359260311413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46341555127059145680415217 34756166345294359260311413)
                    ·
                      refine ⟨3258390594871346180654195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34756166345294359260311413 3258390594871346180654195)
                      ·
                        rfl

theorem cell23_6345693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6345693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345693 prefixEnd_6345693 := by exact prefixLift 6345693
  have htrace : WordTrace (prefixWord ++ tailWord_6345693) baseStart_6345693 baseEnd_6345693 := by
    simpa [prefixWord, tailWord_6345693, baseEnd_6345693] using wordTrace_append hprefix tailTrace_6345693
  have hstable : (prefixWord ++ tailWord_6345693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345693).length < 2 ^ (prefixWord ++ tailWord_6345693).sum := by decide
  have hdescent : baseEnd_6345693 < baseStart_6345693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345740 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_6345740 : Nat := 118140960795 + 6345740 * 2 ^ 59
def prefixEnd_6345740 : Nat := 4983230072969 + 3 ^ 40 * 6345740 * 2
def baseEnd_6345740 : Nat := 3258414728462107496766479

theorem tailTrace_6345740 : CollatzResearch.WordTrace tailWord_6345740 prefixEnd_6345740 3258414728462107496766479 := by
  unfold tailWord_6345740
  simp only [CollatzResearch.WordTrace]
  refine ⟨115724076015237610477041337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154298768020316813969388449 115724076015237610477041337)
  ·
    refine ⟨86793057011428207857781003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115724076015237610477041337 86793057011428207857781003)
    ·
      refine ⟨130189585517142311786671505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86793057011428207857781003 130189585517142311786671505)
      ·
        refine ⟨97642189137856733840003629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130189585517142311786671505 97642189137856733840003629)
        ·
          refine ⟨36615820926696275190001361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97642189137856733840003629 36615820926696275190001361)
          ·
            refine ⟨27461865695022206392501021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36615820926696275190001361 27461865695022206392501021)
            ·
              refine ⟨10298199635633327397187883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27461865695022206392501021 10298199635633327397187883)
              ·
                refine ⟨15447299453449991095781825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298199635633327397187883 15447299453449991095781825)
                ·
                  refine ⟨11585474590087493321836369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15447299453449991095781825 11585474590087493321836369)
                  ·
                    refine ⟨8689105942565619991377277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11585474590087493321836369 8689105942565619991377277)
                    ·
                      refine ⟨3258414728462107496766479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689105942565619991377277 3258414728462107496766479)
                      ·
                        rfl

theorem cell23_6345740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_6345740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345740 prefixEnd_6345740 := by exact prefixLift 6345740
  have htrace : WordTrace (prefixWord ++ tailWord_6345740) baseStart_6345740 baseEnd_6345740 := by
    simpa [prefixWord, tailWord_6345740, baseEnd_6345740] using wordTrace_append hprefix tailTrace_6345740
  have hstable : (prefixWord ++ tailWord_6345740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345740).length < 2 ^ (prefixWord ++ tailWord_6345740).sum := by decide
  have hdescent : baseEnd_6345740 < baseStart_6345740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345760 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 8]
def baseStart_6345760 : Nat := 118140960795 + 6345760 * 2 ^ 59
def prefixEnd_6345760 : Nat := 4983230072969 + 3 ^ 40 * 6345760 * 2
def baseEnd_6345760 : Nat := 362047222008355268724043

theorem tailTrace_6345760 : CollatzResearch.WordTrace tailWord_6345760 prefixEnd_6345760 362047222008355268724043 := by
  unfold tailWord_6345760
  simp only [CollatzResearch.WordTrace]
  refine ⟨115724440745201382184905367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154299254326935176246540489 115724440745201382184905367)
  ·
    refine ⟨173586661117802073277358051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115724440745201382184905367 173586661117802073277358051)
    ·
      refine ⟨260379991676703109916037077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173586661117802073277358051 260379991676703109916037077)
      ·
        refine ⟨6102656054922729138657119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 260379991676703109916037077 6102656054922729138657119)
        ·
          refine ⟨9153984082384093707985679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102656054922729138657119 9153984082384093707985679)
          ·
            refine ⟨13730976123576140561978519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153984082384093707985679 13730976123576140561978519)
            ·
              refine ⟨20596464185364210842967779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13730976123576140561978519 20596464185364210842967779)
              ·
                refine ⟨30894696278046316264451669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20596464185364210842967779 30894696278046316264451669)
                ·
                  refine ⟨362047222008355268724043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30894696278046316264451669 362047222008355268724043)
                  ·
                    rfl

theorem cell23_6345760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_6345760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345760 prefixEnd_6345760 := by exact prefixLift 6345760
  have htrace : WordTrace (prefixWord ++ tailWord_6345760) baseStart_6345760 baseEnd_6345760 := by
    simpa [prefixWord, tailWord_6345760, baseEnd_6345760] using wordTrace_append hprefix tailTrace_6345760
  have hstable : (prefixWord ++ tailWord_6345760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345760).length < 2 ^ (prefixWord ++ tailWord_6345760).sum := by decide
  have hdescent : baseEnd_6345760 < baseStart_6345760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345820 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6345820 : Nat := 118140960795 + 6345820 * 2 ^ 59
def prefixEnd_6345820 : Nat := 4983230072969 + 3 ^ 40 * 6345820 * 2
def baseEnd_6345820 : Nat := 1086151935638155727922037

theorem tailTrace_6345820 : CollatzResearch.WordTrace tailWord_6345820 prefixEnd_6345820 1086151935638155727922037 := by
  unfold tailWord_6345820
  simp only [CollatzResearch.WordTrace]
  refine ⟨115725534935092697308497457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154300713246790263077996609 115725534935092697308497457)
  ·
    refine ⟨86794151201319522981373093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115725534935092697308497457 86794151201319522981373093)
    ·
      refine ⟨16273903350247410559007455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86794151201319522981373093 16273903350247410559007455)
      ·
        refine ⟨24410855025371115838511183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16273903350247410559007455 24410855025371115838511183)
        ·
          refine ⟨36616282538056673757766775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24410855025371115838511183 36616282538056673757766775)
          ·
            refine ⟨54924423807085010636650163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36616282538056673757766775 54924423807085010636650163)
            ·
              refine ⟨82386635710627515954975245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54924423807085010636650163 82386635710627515954975245)
              ·
                refine ⟨30894988391485318483115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82386635710627515954975245 30894988391485318483115717)
                ·
                  refine ⟨5792810323403497215584197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30894988391485318483115717 5792810323403497215584197)
                  ·
                    refine ⟨1086151935638155727922037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792810323403497215584197 1086151935638155727922037)
                    ·
                      rfl

theorem cell23_6345820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6345820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345820 prefixEnd_6345820 := by exact prefixLift 6345820
  have htrace : WordTrace (prefixWord ++ tailWord_6345820) baseStart_6345820 baseEnd_6345820 := by
    simpa [prefixWord, tailWord_6345820, baseEnd_6345820] using wordTrace_append hprefix tailTrace_6345820
  have hstable : (prefixWord ++ tailWord_6345820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345820).length < 2 ^ (prefixWord ++ tailWord_6345820).sum := by decide
  have hdescent : baseEnd_6345820 < baseStart_6345820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345821 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6345821 : Nat := 118140960795 + 6345821 * 2 ^ 59
def prefixEnd_6345821 : Nat := 4983230072969 + 3 ^ 40 * 6345821 * 2
def baseEnd_6345821 : Nat := 3258456320395121679853607

theorem tailTrace_6345821 : CollatzResearch.WordTrace tailWord_6345821 prefixEnd_6345821 3258456320395121679853607 := by
  unfold tailWord_6345821
  simp only [CollatzResearch.WordTrace]
  refine ⟨231451106343181771787781317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154300737562121181191854211 231451106343181771787781317)
  ·
    refine ⟨43397082439346582210208997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231451106343181771787781317 43397082439346582210208997)
    ·
      refine ⟨8136952957377484164414187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43397082439346582210208997 8136952957377484164414187)
      ·
        refine ⟨12205429436066226246621281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136952957377484164414187 12205429436066226246621281)
        ·
          refine ⟨9154072077049669684965961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12205429436066226246621281 9154072077049669684965961)
          ·
            refine ⟨6865554057787252263724471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154072077049669684965961 6865554057787252263724471)
            ·
              refine ⟨10298331086680878395586707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865554057787252263724471 10298331086680878395586707)
              ·
                refine ⟨15447496630021317593380061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298331086680878395586707 15447496630021317593380061)
                ·
                  refine ⟨5792811236257994097517523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15447496630021317593380061 5792811236257994097517523)
                  ·
                    refine ⟨8689216854386991146276285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792811236257994097517523 8689216854386991146276285)
                    ·
                      refine ⟨3258456320395121679853607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689216854386991146276285 3258456320395121679853607)
                      ·
                        rfl

theorem cell23_6345821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6345821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345821 prefixEnd_6345821 := by exact prefixLift 6345821
  have htrace : WordTrace (prefixWord ++ tailWord_6345821) baseStart_6345821 baseEnd_6345821 := by
    simpa [prefixWord, tailWord_6345821, baseEnd_6345821] using wordTrace_append hprefix tailTrace_6345821
  have hstable : (prefixWord ++ tailWord_6345821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345821).length < 2 ^ (prefixWord ++ tailWord_6345821).sum := by decide
  have hdescent : baseEnd_6345821 < baseStart_6345821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345833 : List Nat := [1, 2, 1, 1, 1, 7, 2, 8]
def baseStart_6345833 : Nat := 118140960795 + 6345833 * 2 ^ 59
def prefixEnd_6345833 : Nat := 4983230072969 + 3 ^ 40 * 6345833 * 2
def baseEnd_6345833 : Nat := 120683795635665764181613

theorem tailTrace_6345833 : CollatzResearch.WordTrace tailWord_6345833 prefixEnd_6345833 120683795635665764181613 := by
  unfold tailWord_6345833
  simp only [CollatzResearch.WordTrace]
  refine ⟨231451544019138297837218153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154301029346092198558145435 231451544019138297837218153)
  ·
    refine ⟨173588658014353723377913615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231451544019138297837218153 173588658014353723377913615)
    ·
      refine ⟨260382987021530585066870423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173588658014353723377913615 260382987021530585066870423)
      ·
        refine ⟨390574480532295877600305635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260382987021530585066870423 390574480532295877600305635)
        ·
          refine ⟨585861720798443816400458453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390574480532295877600305635 585861720798443816400458453)
          ·
            refine ⟨13731134081213526946885745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 585861720798443816400458453 13731134081213526946885745)
            ·
              refine ⟨10298350560910145210164309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13731134081213526946885745 10298350560910145210164309)
              ·
                refine ⟨120683795635665764181613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10298350560910145210164309 120683795635665764181613)
                ·
                  rfl

theorem cell23_6345833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 8].length) (baseStart_6345833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345833 prefixEnd_6345833 := by exact prefixLift 6345833
  have htrace : WordTrace (prefixWord ++ tailWord_6345833) baseStart_6345833 baseEnd_6345833 := by
    simpa [prefixWord, tailWord_6345833, baseEnd_6345833] using wordTrace_append hprefix tailTrace_6345833
  have hstable : (prefixWord ++ tailWord_6345833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345833).length < 2 ^ (prefixWord ++ tailWord_6345833).sum := by decide
  have hdescent : baseEnd_6345833 < baseStart_6345833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345837 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_6345837 : Nat := 118140960795 + 6345837 * 2 ^ 59
def prefixEnd_6345837 : Nat := 4983230072969 + 3 ^ 40 * 6345837 * 2
def baseEnd_6345837 : Nat := 1086154845361864539084511

theorem tailTrace_6345837 : CollatzResearch.WordTrace tailWord_6345837 prefixEnd_6345837 1086154845361864539084511 := by
  unfold tailWord_6345837
  simp only [CollatzResearch.WordTrace]
  refine ⟨231451689911123806520363765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154301126607415871013575843 231451689911123806520363765)
  ·
    refine ⟨21698595929167856861284103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231451689911123806520363765 21698595929167856861284103)
    ·
      refine ⟨32547893893751785291926155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21698595929167856861284103 32547893893751785291926155)
      ·
        refine ⟨48821840840627677937889233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32547893893751785291926155 48821840840627677937889233)
        ·
          refine ⟨36616380630470758453416925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48821840840627677937889233 36616380630470758453416925)
          ·
            refine ⟨13731142736426534420031347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36616380630470758453416925 13731142736426534420031347)
            ·
              refine ⟨20596714104639801630047021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731142736426534420031347 20596714104639801630047021)
              ·
                refine ⟨7723767789239925611267633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20596714104639801630047021 7723767789239925611267633)
                ·
                  refine ⟨5792825841929944208450725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723767789239925611267633 5792825841929944208450725)
                  ·
                    refine ⟨1086154845361864539084511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5792825841929944208450725 1086154845361864539084511)
                    ·
                      rfl

theorem cell23_6345837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_6345837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345837 prefixEnd_6345837 := by exact prefixLift 6345837
  have htrace : WordTrace (prefixWord ++ tailWord_6345837) baseStart_6345837 baseEnd_6345837 := by
    simpa [prefixWord, tailWord_6345837, baseEnd_6345837] using wordTrace_append hprefix tailTrace_6345837
  have hstable : (prefixWord ++ tailWord_6345837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345837).length < 2 ^ (prefixWord ++ tailWord_6345837).sum := by decide
  have hdescent : baseEnd_6345837 < baseStart_6345837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345843 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3]
def baseStart_6345843 : Nat := 118140960795 + 6345843 * 2 ^ 59
def prefixEnd_6345843 : Nat := 4983230072969 + 3 ^ 40 * 6345843 * 2
def baseEnd_6345843 : Nat := 3258467616969520593778505

theorem tailTrace_6345843 : CollatzResearch.WordTrace tailWord_6345843 prefixEnd_6345843 3258467616969520593778505 := by
  unfold tailWord_6345843
  simp only [CollatzResearch.WordTrace]
  refine ⟨231451908749102069545082183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154301272499401379696721455 231451908749102069545082183)
  ·
    refine ⟨347177863123653104317623275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231451908749102069545082183 347177863123653104317623275)
    ·
      refine ⟨520766794685479656476434913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347177863123653104317623275 520766794685479656476434913)
      ·
        refine ⟨390575096014109742357326185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520766794685479656476434913 390575096014109742357326185)
        ·
          refine ⟨292931322010582306767994639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390575096014109742357326185 292931322010582306767994639)
          ·
            refine ⟨439396983015873460151991959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292931322010582306767994639 439396983015873460151991959)
            ·
              refine ⟨659095474523810190227987939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439396983015873460151991959 659095474523810190227987939)
              ·
                refine ⟨988643211785715285341981909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659095474523810190227987939 988643211785715285341981909)
                ·
                  refine ⟨23171325276227702000202701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 988643211785715285341981909 23171325276227702000202701)
                  ·
                    refine ⟨8689246978585388250076013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23171325276227702000202701 8689246978585388250076013)
                    ·
                      refine ⟨3258467616969520593778505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689246978585388250076013 3258467616969520593778505)
                      ·
                        rfl

theorem cell23_6345843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_6345843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345843 prefixEnd_6345843 := by exact prefixLift 6345843
  have htrace : WordTrace (prefixWord ++ tailWord_6345843) baseStart_6345843 baseEnd_6345843 := by
    simpa [prefixWord, tailWord_6345843, baseEnd_6345843] using wordTrace_append hprefix tailTrace_6345843
  have hstable : (prefixWord ++ tailWord_6345843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345843).length < 2 ^ (prefixWord ++ tailWord_6345843).sum := by decide
  have hdescent : baseEnd_6345843 < baseStart_6345843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345860 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_6345860 : Nat := 118140960795 + 6345860 * 2 ^ 59
def prefixEnd_6345860 : Nat := 4983230072969 + 3 ^ 40 * 6345860 * 2
def baseEnd_6345860 : Nat := 3258476346140647027265927

theorem tailTrace_6345860 : CollatzResearch.WordTrace tailWord_6345860 prefixEnd_6345860 3258476346140647027265927 := by
  unfold tailWord_6345860
  simp only [CollatzResearch.WordTrace]
  refine ⟨115726264395020240724225517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154301685860026987632300689 115726264395020240724225517)
  ·
    refine ⟨43397349148132590271584569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115726264395020240724225517 43397349148132590271584569)
    ·
      refine ⟨32548011861099442703688427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43397349148132590271584569 32548011861099442703688427)
      ·
        refine ⟨48822017791649164055532641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32548011861099442703688427 48822017791649164055532641)
        ·
          refine ⟨36616513343736873041649481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48822017791649164055532641 36616513343736873041649481)
          ·
            refine ⟨27462385007802654781237111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36616513343736873041649481 27462385007802654781237111)
            ·
              refine ⟨41193577511703982171855667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27462385007802654781237111 41193577511703982171855667)
              ·
                refine ⟨61790366267555973257783501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41193577511703982171855667 61790366267555973257783501)
                ·
                  refine ⟨23171387350333489971668813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61790366267555973257783501 23171387350333489971668813)
                  ·
                    refine ⟨8689270256375058739375805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23171387350333489971668813 8689270256375058739375805)
                    ·
                      refine ⟨3258476346140647027265927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689270256375058739375805 3258476346140647027265927)
                      ·
                        rfl

theorem cell23_6345860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_6345860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345860 prefixEnd_6345860 := by exact prefixLift 6345860
  have htrace : WordTrace (prefixWord ++ tailWord_6345860) baseStart_6345860 baseEnd_6345860 := by
    simpa [prefixWord, tailWord_6345860, baseEnd_6345860] using wordTrace_append hprefix tailTrace_6345860
  have hstable : (prefixWord ++ tailWord_6345860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345860).length < 2 ^ (prefixWord ++ tailWord_6345860).sum := by decide
  have hdescent : baseEnd_6345860 < baseStart_6345860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345864 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6345864 : Nat := 118140960795 + 6345864 * 2 ^ 59
def prefixEnd_6345864 : Nat := 4983230072969 + 3 ^ 40 * 6345864 * 2
def baseEnd_6345864 : Nat := 3258478400063265011615909

theorem tailTrace_6345864 : CollatzResearch.WordTrace tailWord_6345864 prefixEnd_6345864 3258478400063265011615909 := by
  unfold tailWord_6345864
  simp only [CollatzResearch.WordTrace]
  refine ⟨115726337341012995065798323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154301783121350660087731097 115726337341012995065798323)
  ·
    refine ⟨173589506011519492598697485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115726337341012995065798323 173589506011519492598697485)
    ·
      refine ⟨65096064754319809724511557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173589506011519492598697485 65096064754319809724511557)
      ·
        refine ⟨12205512141434964323345917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65096064754319809724511557 12205512141434964323345917)
        ·
          refine ⟨4577067053038111621254719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12205512141434964323345917 4577067053038111621254719)
          ·
            refine ⟨6865600579557167431882079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577067053038111621254719 6865600579557167431882079)
            ·
              refine ⟨10298400869335751147823119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865600579557167431882079 10298400869335751147823119)
              ·
                refine ⟨15447601304003626721734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298400869335751147823119 15447601304003626721734679)
                ·
                  refine ⟨23171401956005440082602019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447601304003626721734679 23171401956005440082602019)
                  ·
                    refine ⟨34757102934008160123903029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23171401956005440082602019 34757102934008160123903029)
                    ·
                      refine ⟨3258478400063265011615909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34757102934008160123903029 3258478400063265011615909)
                      ·
                        rfl

theorem cell23_6345864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6345864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345864 prefixEnd_6345864 := by exact prefixLift 6345864
  have htrace : WordTrace (prefixWord ++ tailWord_6345864) baseStart_6345864 baseEnd_6345864 := by
    simpa [prefixWord, tailWord_6345864, baseEnd_6345864] using wordTrace_append hprefix tailTrace_6345864
  have hstable : (prefixWord ++ tailWord_6345864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345864).length < 2 ^ (prefixWord ++ tailWord_6345864).sum := by decide
  have hdescent : baseEnd_6345864 < baseStart_6345864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345893 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_6345893 : Nat := 118140960795 + 6345893 * 2 ^ 59
def prefixEnd_6345893 : Nat := 4983230072969 + 3 ^ 40 * 6345893 * 2
def baseEnd_6345893 : Nat := 1086164430334081799384425

theorem tailTrace_6345893 : CollatzResearch.WordTrace tailWord_6345893 prefixEnd_6345893 1086164430334081799384425 := by
  unfold tailWord_6345893
  simp only [CollatzResearch.WordTrace]
  refine ⟨231453732398920928084402333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154302488265947285389601555 231453732398920928084402333)
  ·
    refine ⟨86795149649595348031650875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231453732398920928084402333 86795149649595348031650875)
    ·
      refine ⟨130192724474393022047476313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86795149649595348031650875 130192724474393022047476313)
      ·
        refine ⟨97644543355794766535607235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130192724474393022047476313 97644543355794766535607235)
        ·
          refine ⟨146466815033692149803410853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97644543355794766535607235 146466815033692149803410853)
          ·
            refine ⟨27462527818817278088139535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146466815033692149803410853 27462527818817278088139535)
            ·
              refine ⟨41193791728225917132209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27462527818817278088139535 41193791728225917132209303)
              ·
                refine ⟨61790687592338875698313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41193791728225917132209303 61790687592338875698313955)
                ·
                  refine ⟨92686031388508313547470933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61790687592338875698313955 92686031388508313547470933)
                  ·
                    refine ⟨1086164430334081799384425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92686031388508313547470933 1086164430334081799384425)
                    ·
                      rfl

theorem cell23_6345893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_6345893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345893 prefixEnd_6345893 := by exact prefixLift 6345893
  have htrace : WordTrace (prefixWord ++ tailWord_6345893) baseStart_6345893 baseEnd_6345893 := by
    simpa [prefixWord, tailWord_6345893, baseEnd_6345893] using wordTrace_append hprefix tailTrace_6345893
  have hstable : (prefixWord ++ tailWord_6345893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345893).length < 2 ^ (prefixWord ++ tailWord_6345893).sum := by decide
  have hdescent : baseEnd_6345893 < baseStart_6345893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345903 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_6345903 : Nat := 118140960795 + 6345903 * 2 ^ 59
def prefixEnd_6345903 : Nat := 4983230072969 + 3 ^ 40 * 6345903 * 2
def baseEnd_6345903 : Nat := 3258498425808790359028229

theorem tailTrace_6345903 : CollatzResearch.WordTrace tailWord_6345903 prefixEnd_6345903 3258498425808790359028229 := by
  unfold tailWord_6345903
  simp only [CollatzResearch.WordTrace]
  refine ⟨231454097128884699792266363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154302731419256466528177575 231454097128884699792266363)
  ·
    refine ⟨347181145693327049688399545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231454097128884699792266363 347181145693327049688399545)
    ·
      refine ⟨260385859269995287266299659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347181145693327049688399545 260385859269995287266299659)
      ·
        refine ⟨390578788904992930899449489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260385859269995287266299659 390578788904992930899449489)
        ·
          refine ⟨292934091678744698174587117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390578788904992930899449489 292934091678744698174587117)
          ·
            refine ⟨109850284379529261815470169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292934091678744698174587117 109850284379529261815470169)
            ·
              refine ⟨82387713284646946361602627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109850284379529261815470169 82387713284646946361602627)
              ·
                refine ⟨123581569926970419542403941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82387713284646946361602627 123581569926970419542403941)
                ·
                  refine ⟨23171544361306953664200739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123581569926970419542403941 23171544361306953664200739)
                  ·
                    refine ⟨34757316541960430496301109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23171544361306953664200739 34757316541960430496301109)
                    ·
                      refine ⟨3258498425808790359028229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34757316541960430496301109 3258498425808790359028229)
                      ·
                        rfl

theorem cell23_6345903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_6345903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345903 prefixEnd_6345903 := by exact prefixLift 6345903
  have htrace : WordTrace (prefixWord ++ tailWord_6345903) baseStart_6345903 baseEnd_6345903 := by
    simpa [prefixWord, tailWord_6345903, baseEnd_6345903] using wordTrace_append hprefix tailTrace_6345903
  have hstable : (prefixWord ++ tailWord_6345903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345903).length < 2 ^ (prefixWord ++ tailWord_6345903).sum := by decide
  have hdescent : baseEnd_6345903 < baseStart_6345903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345917 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_6345917 : Nat := 118140960795 + 6345917 * 2 ^ 59
def prefixEnd_6345917 : Nat := 4983230072969 + 3 ^ 40 * 6345917 * 2
def baseEnd_6345917 : Nat := 3258505614537953304253165

theorem tailTrace_6345917 : CollatzResearch.WordTrace tailWord_6345917 prefixEnd_6345917 3258505614537953304253165 := by
  unfold tailWord_6345917
  simp only [CollatzResearch.WordTrace]
  refine ⟨231454607750833980183276005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154303071833889320122184003 231454607750833980183276005)
  ·
    refine ⟨43397738953281371284364251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231454607750833980183276005 43397738953281371284364251)
    ·
      refine ⟨65096608429922056926546377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43397738953281371284364251 65096608429922056926546377)
      ·
        refine ⟨48822456322441542694909783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65096608429922056926546377 48822456322441542694909783)
        ·
          refine ⟨73233684483662314042364675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48822456322441542694909783 73233684483662314042364675)
          ·
            refine ⟨109850526725493471063547013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73233684483662314042364675 109850526725493471063547013)
            ·
              refine ⟨20596973761030025824415065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109850526725493471063547013 20596973761030025824415065)
              ·
                refine ⟨15447730320772519368311299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20596973761030025824415065 15447730320772519368311299)
                ·
                  refine ⟨23171595481158779052466949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447730320772519368311299 23171595481158779052466949)
                  ·
                    refine ⟨4344674152717271072337553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23171595481158779052466949 4344674152717271072337553)
                    ·
                      refine ⟨3258505614537953304253165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344674152717271072337553 3258505614537953304253165)
                      ·
                        rfl

theorem cell23_6345917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_6345917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345917 prefixEnd_6345917 := by exact prefixLift 6345917
  have htrace : WordTrace (prefixWord ++ tailWord_6345917) baseStart_6345917 baseEnd_6345917 := by
    simpa [prefixWord, tailWord_6345917, baseEnd_6345917] using wordTrace_append hprefix tailTrace_6345917
  have hstable : (prefixWord ++ tailWord_6345917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345917).length < 2 ^ (prefixWord ++ tailWord_6345917).sum := by decide
  have hdescent : baseEnd_6345917 < baseStart_6345917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345921 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6345921 : Nat := 118140960795 + 6345921 * 2 ^ 59
def prefixEnd_6345921 : Nat := 4983230072969 + 3 ^ 40 * 6345921 * 2
def baseEnd_6345921 : Nat := 3258507668460571288603147

theorem tailTrace_6345921 : CollatzResearch.WordTrace tailWord_6345921 prefixEnd_6345921 3258507668460571288603147 := by
  unfold tailWord_6345921
  simp only [CollatzResearch.WordTrace]
  refine ⟨231454753642819488866421617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154303169095212992577614411 231454753642819488866421617)
  ·
    refine ⟨173591065232114616649816213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231454753642819488866421617 173591065232114616649816213)
    ·
      refine ⟨8137081182755372655460135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173591065232114616649816213 8137081182755372655460135)
      ·
        refine ⟨12205621774133058983190203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137081182755372655460135 12205621774133058983190203)
        ·
          refine ⟨18308432661199588474785305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205621774133058983190203 18308432661199588474785305)
          ·
            refine ⟨13731324495899691356088979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18308432661199588474785305 13731324495899691356088979)
            ·
              refine ⟨20596986743849537034133469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731324495899691356088979 20596986743849537034133469)
              ·
                refine ⟨7723870028943576387800051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20596986743849537034133469 7723870028943576387800051)
                ·
                  refine ⟨11585805043415364581700077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7723870028943576387800051 11585805043415364581700077)
                  ·
                    refine ⟨4344676891280761718137529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11585805043415364581700077 4344676891280761718137529)
                    ·
                      refine ⟨3258507668460571288603147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344676891280761718137529 3258507668460571288603147)
                      ·
                        rfl

theorem cell23_6345921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6345921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345921 prefixEnd_6345921 := by exact prefixLift 6345921
  have htrace : WordTrace (prefixWord ++ tailWord_6345921) baseStart_6345921 baseEnd_6345921 := by
    simpa [prefixWord, tailWord_6345921, baseEnd_6345921] using wordTrace_append hprefix tailTrace_6345921
  have hstable : (prefixWord ++ tailWord_6345921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345921).length < 2 ^ (prefixWord ++ tailWord_6345921).sum := by decide
  have hdescent : baseEnd_6345921 < baseStart_6345921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6345930 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_6345930 : Nat := 118140960795 + 6345930 * 2 ^ 59
def prefixEnd_6345930 : Nat := 4983230072969 + 3 ^ 40 * 6345930 * 2
def baseEnd_6345930 : Nat := 3258512289786461753390605

theorem tailTrace_6345930 : CollatzResearch.WordTrace tailWord_6345930 prefixEnd_6345930 3258512289786461753390605 := by
  unfold tailWord_6345930
  simp only [CollatzResearch.WordTrace]
  refine ⟨57863770474946720850874811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154303387933191255602332829 57863770474946720850874811)
  ·
    refine ⟨86795655712420081276312217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57863770474946720850874811 86795655712420081276312217)
    ·
      refine ⟨65096741784315060957234163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86795655712420081276312217 65096741784315060957234163)
      ·
        refine ⟨97645112676472591435851245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65096741784315060957234163 97645112676472591435851245)
        ·
          refine ⟨36616917253677221788444217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97645112676472591435851245 36616917253677221788444217)
          ·
            refine ⟨27462687940257916341333163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36616917253677221788444217 27462687940257916341333163)
            ·
              refine ⟨41194031910386874511999745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27462687940257916341333163 41194031910386874511999745)
              ·
                refine ⟨30895523932790155883999809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41194031910386874511999745 30895523932790155883999809)
                ·
                  refine ⟨23171642949592616912999857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30895523932790155883999809 23171642949592616912999857)
                  ·
                    refine ⟨17378732212194462684749893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23171642949592616912999857 17378732212194462684749893)
                    ·
                      refine ⟨3258512289786461753390605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17378732212194462684749893 3258512289786461753390605)
                      ·
                        rfl

theorem cell23_6345930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_6345930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6345930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6345930 prefixEnd_6345930 := by exact prefixLift 6345930
  have htrace : WordTrace (prefixWord ++ tailWord_6345930) baseStart_6345930 baseEnd_6345930 := by
    simpa [prefixWord, tailWord_6345930, baseEnd_6345930] using wordTrace_append hprefix tailTrace_6345930
  have hstable : (prefixWord ++ tailWord_6345930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6345930).length < 2 ^ (prefixWord ++ tailWord_6345930).sum := by decide
  have hdescent : baseEnd_6345930 < baseStart_6345930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6345930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346002 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6346002 : Nat := 118140960795 + 6346002 * 2 ^ 59
def prefixEnd_6346002 : Nat := 4983230072969 + 3 ^ 40 * 6346002 * 2
def baseEnd_6346002 : Nat := 3258549260393585471690275

theorem tailTrace_6346002 : CollatzResearch.WordTrace tailWord_6346002 prefixEnd_6346002 3258549260393585471690275 := by
  unfold tailWord_6346002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57864426988881509925030065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154305138637017359800080173 57864426988881509925030065)
  ·
    refine ⟨43398320241661132443772549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57864426988881509925030065 43398320241661132443772549)
    ·
      refine ⟨8137185045311462333207353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43398320241661132443772549 8137185045311462333207353)
      ·
        refine ⟨6102888783983596749905515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8137185045311462333207353 6102888783983596749905515)
        ·
          refine ⟨9154333175975395124858273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102888783983596749905515 9154333175975395124858273)
          ·
            refine ⟨6865749881981546343643705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154333175975395124858273 6865749881981546343643705)
            ·
              refine ⟨5149312411486159757732779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865749881981546343643705 5149312411486159757732779)
              ·
                refine ⟨7723968617229239636599169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149312411486159757732779 7723968617229239636599169)
                ·
                  refine ⟨5792976462921929727449377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723968617229239636599169 5792976462921929727449377)
                  ·
                    refine ⟨4344732347191447295587033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5792976462921929727449377 4344732347191447295587033)
                    ·
                      refine ⟨3258549260393585471690275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344732347191447295587033 3258549260393585471690275)
                      ·
                        rfl

theorem cell23_6346002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6346002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346002 prefixEnd_6346002 := by exact prefixLift 6346002
  have htrace : WordTrace (prefixWord ++ tailWord_6346002) baseStart_6346002 baseEnd_6346002 := by
    simpa [prefixWord, tailWord_6346002, baseEnd_6346002] using wordTrace_append hprefix tailTrace_6346002
  have hstable : (prefixWord ++ tailWord_6346002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346002).length < 2 ^ (prefixWord ++ tailWord_6346002).sum := by decide
  have hdescent : baseEnd_6346002 < baseStart_6346002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346007 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6346007 : Nat := 118140960795 + 6346007 * 2 ^ 59
def prefixEnd_6346007 : Nat := 4983230072969 + 3 ^ 40 * 6346007 * 2
def baseEnd_6346007 : Nat := 3258551827796857952127751

theorem tailTrace_6346007 : CollatzResearch.WordTrace tailWord_6346007 prefixEnd_6346007 3258551827796857952127751 := by
  unfold tailWord_6346007
  simp only [CollatzResearch.WordTrace]
  refine ⟨231457890320507925554052275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154305260213671950369368183 231457890320507925554052275)
  ·
    refine ⟨347186835480761888331078413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231457890320507925554052275 347186835480761888331078413)
    ·
      refine ⟨130195063305285708124154405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347186835480761888331078413 130195063305285708124154405)
      ·
        refine ⟨24411574369741070273278951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130195063305285708124154405 24411574369741070273278951)
        ·
          refine ⟨36617361554611605409918427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24411574369741070273278951 36617361554611605409918427)
          ·
            refine ⟨54926042331917408114877641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36617361554611605409918427 54926042331917408114877641)
            ·
              refine ⟨41194531748938056086158231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54926042331917408114877641 41194531748938056086158231)
              ·
                refine ⟨61791797623407084129237347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41194531748938056086158231 61791797623407084129237347)
                ·
                  refine ⟨92687696435110626193856021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61791797623407084129237347 92687696435110626193856021)
                  ·
                    refine ⟨4344735770395810602837001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92687696435110626193856021 4344735770395810602837001)
                    ·
                      refine ⟨3258551827796857952127751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344735770395810602837001 3258551827796857952127751)
                      ·
                        rfl

theorem cell23_6346007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6346007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346007 prefixEnd_6346007 := by exact prefixLift 6346007
  have htrace : WordTrace (prefixWord ++ tailWord_6346007) baseStart_6346007 baseEnd_6346007 := by
    simpa [prefixWord, tailWord_6346007, baseEnd_6346007] using wordTrace_append hprefix tailTrace_6346007
  have hstable : (prefixWord ++ tailWord_6346007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346007).length < 2 ^ (prefixWord ++ tailWord_6346007).sum := by decide
  have hdescent : baseEnd_6346007 < baseStart_6346007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346024 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6346024 : Nat := 118140960795 + 6346024 * 2 ^ 59
def prefixEnd_6346024 : Nat := 4983230072969 + 3 ^ 40 * 6346024 * 2
def baseEnd_6346024 : Nat := 3258560556967984385615173

theorem tailTrace_6346024 : CollatzResearch.WordTrace tailWord_6346024 prefixEnd_6346024 3258560556967984385615173 := by
  unfold tailWord_6346024
  simp only [CollatzResearch.WordTrace]
  refine ⟨115729255180723168728710563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154305673574297558304947417 115729255180723168728710563)
  ·
    refine ⟨173593882771084753093065845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115729255180723168728710563 173593882771084753093065845)
    ·
      refine ⟨16274426509789195602474923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173593882771084753093065845 16274426509789195602474923)
      ·
        refine ⟨24411639764683793403712385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16274426509789195602474923 24411639764683793403712385)
        ·
          refine ⟨18308729823512845052784289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24411639764683793403712385 18308729823512845052784289)
          ·
            refine ⟨13731547367634633789588217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18308729823512845052784289 13731547367634633789588217)
            ·
              refine ⟨10298660525725975342191163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13731547367634633789588217 10298660525725975342191163)
              ·
                refine ⟨15447990788588963013286745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298660525725975342191163 15447990788588963013286745)
                ·
                  refine ⟨11585993091441722259965059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15447990788588963013286745 11585993091441722259965059)
                  ·
                    refine ⟨17378989637162583389947589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11585993091441722259965059 17378989637162583389947589)
                    ·
                      refine ⟨3258560556967984385615173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17378989637162583389947589 3258560556967984385615173)
                      ·
                        rfl

theorem cell23_6346024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6346024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346024 prefixEnd_6346024 := by exact prefixLift 6346024
  have htrace : WordTrace (prefixWord ++ tailWord_6346024) baseStart_6346024 baseEnd_6346024 := by
    simpa [prefixWord, tailWord_6346024, baseEnd_6346024] using wordTrace_append hprefix tailTrace_6346024
  have hstable : (prefixWord ++ tailWord_6346024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346024).length < 2 ^ (prefixWord ++ tailWord_6346024).sum := by decide
  have hdescent : baseEnd_6346024 < baseStart_6346024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346047 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 6]
def baseStart_6346047 : Nat := 118140960795 + 6346047 * 2 ^ 59
def prefixEnd_6346047 : Nat := 4983230072969 + 3 ^ 40 * 6346047 * 2
def baseEnd_6346047 : Nat := 362063596335893088403063

theorem tailTrace_6346047 : CollatzResearch.WordTrace tailWord_6346047 prefixEnd_6346047 362063596335893088403063 := by
  unfold tailWord_6346047
  simp only [CollatzResearch.WordTrace]
  refine ⟨231459349240363012385508395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154306232826908674923672263 231459349240363012385508395)
  ·
    refine ⟨347189023860544518578262593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231459349240363012385508395 347189023860544518578262593)
    ·
      refine ⟨260391767895408388933696945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347189023860544518578262593 260391767895408388933696945)
      ·
        refine ⟨195293825921556291700272709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260391767895408388933696945 195293825921556291700272709)
        ·
          refine ⟨36617592360291804693801133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195293825921556291700272709 36617592360291804693801133)
          ·
            refine ⟨13731597135109426760175425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36617592360291804693801133 13731597135109426760175425)
            ·
              refine ⟨10298697851332070070131569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13731597135109426760175425 10298697851332070070131569)
              ·
                refine ⟨7724023388499052552598677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10298697851332070070131569 7724023388499052552598677)
                ·
                  refine ⟨362063596335893088403063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7724023388499052552598677 362063596335893088403063)
                  ·
                    rfl

theorem cell23_6346047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 6].length) (baseStart_6346047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346047 prefixEnd_6346047 := by exact prefixLift 6346047
  have htrace : WordTrace (prefixWord ++ tailWord_6346047) baseStart_6346047 baseEnd_6346047 := by
    simpa [prefixWord, tailWord_6346047, baseEnd_6346047] using wordTrace_append hprefix tailTrace_6346047
  have hstable : (prefixWord ++ tailWord_6346047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346047).length < 2 ^ (prefixWord ++ tailWord_6346047).sum := by decide
  have hdescent : baseEnd_6346047 < baseStart_6346047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346067 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 5, 2]
def baseStart_6346067 : Nat := 118140960795 + 6346067 * 2 ^ 59
def prefixEnd_6346067 : Nat := 4983230072969 + 3 ^ 40 * 6346067 * 2
def baseEnd_6346067 : Nat := 3258582636636127717377475

theorem tailTrace_6346067 : CollatzResearch.WordTrace tailWord_6346067 prefixEnd_6346067 3258582636636127717377475 := by
  unfold tailWord_6346067
  simp only [CollatzResearch.WordTrace]
  refine ⟨231460078700290555801236455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154306719133527037200824303 231460078700290555801236455)
  ·
    refine ⟨347190118050435833701854683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231460078700290555801236455 347190118050435833701854683)
    ·
      refine ⟨520785177075653750552782025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347190118050435833701854683 520785177075653750552782025)
      ·
        refine ⟨390588882806740312914586519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520785177075653750552782025 390588882806740312914586519)
        ·
          refine ⟨585883324210110469371879779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390588882806740312914586519 585883324210110469371879779)
          ·
            refine ⟨878824986315165704057819669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585883324210110469371879779 878824986315165704057819669)
            ·
              refine ⟨41194921233523392377710297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 878824986315165704057819669 41194921233523392377710297)
              ·
                refine ⟨30896190925142544283282723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41194921233523392377710297 30896190925142544283282723)
                ·
                  refine ⟨46344286387713816424924085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30896190925142544283282723 46344286387713816424924085)
                  ·
                    refine ⟨4344776848848170289836633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46344286387713816424924085 4344776848848170289836633)
                    ·
                      refine ⟨3258582636636127717377475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344776848848170289836633 3258582636636127717377475)
                      ·
                        rfl

theorem cell23_6346067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5, 2].length) (baseStart_6346067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346067 prefixEnd_6346067 := by exact prefixLift 6346067
  have htrace : WordTrace (prefixWord ++ tailWord_6346067) baseStart_6346067 baseEnd_6346067 := by
    simpa [prefixWord, tailWord_6346067, baseEnd_6346067] using wordTrace_append hprefix tailTrace_6346067
  have hstable : (prefixWord ++ tailWord_6346067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346067).length < 2 ^ (prefixWord ++ tailWord_6346067).sum := by decide
  have hdescent : baseEnd_6346067 < baseStart_6346067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346084 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_6346084 : Nat := 118140960795 + 6346084 * 2 ^ 59
def prefixEnd_6346084 : Nat := 4983230072969 + 3 ^ 40 * 6346084 * 2
def baseEnd_6346084 : Nat := 3258591365807254150864897

theorem tailTrace_6346084 : CollatzResearch.WordTrace tailWord_6346084 prefixEnd_6346084 3258591365807254150864897 := by
  unfold tailWord_6346084
  simp only [CollatzResearch.WordTrace]
  refine ⟨115730349370614483852302653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154307132494152645136403537 115730349370614483852302653)
  ·
    refine ⟨43398881013980431444613495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115730349370614483852302653 43398881013980431444613495)
    ·
      refine ⟨65098321520970647166920243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43398881013980431444613495 65098321520970647166920243)
      ·
        refine ⟨97647482281455970750380365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65098321520970647166920243 97647482281455970750380365)
        ·
          refine ⟨36617805855545989031392637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97647482281455970750380365 36617805855545989031392637)
          ·
            refine ⟨13731677195829745886772239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36617805855545989031392637 13731677195829745886772239)
            ·
              refine ⟨20597515793744618830158359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731677195829745886772239 20597515793744618830158359)
              ·
                refine ⟨30896273690616928245237539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20597515793744618830158359 30896273690616928245237539)
                ·
                  refine ⟨46344410535925392367856309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30896273690616928245237539 46344410535925392367856309)
                  ·
                    refine ⟨4344788487743005534486529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46344410535925392367856309 4344788487743005534486529)
                    ·
                      refine ⟨3258591365807254150864897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344788487743005534486529 3258591365807254150864897)
                      ·
                        rfl

theorem cell23_6346084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_6346084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346084 prefixEnd_6346084 := by exact prefixLift 6346084
  have htrace : WordTrace (prefixWord ++ tailWord_6346084) baseStart_6346084 baseEnd_6346084 := by
    simpa [prefixWord, tailWord_6346084, baseEnd_6346084] using wordTrace_append hprefix tailTrace_6346084
  have hstable : (prefixWord ++ tailWord_6346084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346084).length < 2 ^ (prefixWord ++ tailWord_6346084).sum := by decide
  have hdescent : baseEnd_6346084 < baseStart_6346084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346107 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 4, 4]
def baseStart_6346107 : Nat := 118140960795 + 6346107 * 2 ^ 59
def prefixEnd_6346107 : Nat := 4983230072969 + 3 ^ 40 * 6346107 * 2
def baseEnd_6346107 : Nat := 1086201058620769186959097

theorem tailTrace_6346107 : CollatzResearch.WordTrace tailWord_6346107 prefixEnd_6346107 1086201058620769186959097 := by
  unfold tailWord_6346107
  simp only [CollatzResearch.WordTrace]
  refine ⟨231461537620145642632692575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154307691746763761755128383 231461537620145642632692575)
  ·
    refine ⟨347192306430218463949038863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231461537620145642632692575 347192306430218463949038863)
    ·
      refine ⟨520788459645327695923558295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347192306430218463949038863 520788459645327695923558295)
      ·
        refine ⟨781182689467991543885337443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520788459645327695923558295 781182689467991543885337443)
        ·
          refine ⟨1171774034201987315828006165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781182689467991543885337443 1171774034201987315828006165)
          ·
            refine ⟨54926907853218155429437789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1171774034201987315828006165 54926907853218155429437789)
            ·
              refine ⟨20597590444956808286039171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54926907853218155429437789 20597590444956808286039171)
              ·
                refine ⟨30896385667435212429058757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20597590444956808286039171 30896385667435212429058757)
                ·
                  refine ⟨5793072312644102330448517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30896385667435212429058757 5793072312644102330448517)
                  ·
                    refine ⟨1086201058620769186959097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793072312644102330448517 1086201058620769186959097)
                    ·
                      rfl

theorem cell23_6346107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 4].length) (baseStart_6346107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346107 prefixEnd_6346107 := by exact prefixLift 6346107
  have htrace : WordTrace (prefixWord ++ tailWord_6346107) baseStart_6346107 baseEnd_6346107 := by
    simpa [prefixWord, tailWord_6346107, baseEnd_6346107] using wordTrace_append hprefix tailTrace_6346107
  have hstable : (prefixWord ++ tailWord_6346107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346107).length < 2 ^ (prefixWord ++ tailWord_6346107).sum := by decide
  have hdescent : baseEnd_6346107 < baseStart_6346107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346117 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_6346117 : Nat := 118140960795 + 6346117 * 2 ^ 59
def prefixEnd_6346117 : Nat := 4983230072969 + 3 ^ 40 * 6346117 * 2
def baseEnd_6346117 : Nat := 3258608310668852521752245

theorem tailTrace_6346117 : CollatzResearch.WordTrace tailWord_6346117 prefixEnd_6346117 3258608310668852521752245 := by
  unfold tailWord_6346117
  simp only [CollatzResearch.WordTrace]
  refine ⟨231461902350109414340556605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154307934900072942893704403 231461902350109414340556605)
  ·
    refine ⟨86798213381291030377708727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231461902350109414340556605 86798213381291030377708727)
    ·
      refine ⟨130197320071936545566563091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86798213381291030377708727 130197320071936545566563091)
      ·
        refine ⟨195295980107904818349844637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130197320071936545566563091 195295980107904818349844637)
        ·
          refine ⟨73235992540464306881191739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195295980107904818349844637 73235992540464306881191739)
          ·
            refine ⟨109853988810696460321787609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73235992540464306881191739 109853988810696460321787609)
            ·
              refine ⟨82390491608022345241340707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109853988810696460321787609 82390491608022345241340707)
              ·
                refine ⟨123585737412033517862011061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82390491608022345241340707 123585737412033517862011061)
                ·
                  refine ⟨11586162882378142299563537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123585737412033517862011061 11586162882378142299563537)
                  ·
                    refine ⟨8689622161783606724672653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11586162882378142299563537 8689622161783606724672653)
                    ·
                      refine ⟨3258608310668852521752245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689622161783606724672653 3258608310668852521752245)
                      ·
                        rfl

theorem cell23_6346117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_6346117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346117 prefixEnd_6346117 := by exact prefixLift 6346117
  have htrace : WordTrace (prefixWord ++ tailWord_6346117) baseStart_6346117 baseEnd_6346117 := by
    simpa [prefixWord, tailWord_6346117, baseEnd_6346117] using wordTrace_append hprefix tailTrace_6346117
  have hstable : (prefixWord ++ tailWord_6346117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346117).length < 2 ^ (prefixWord ++ tailWord_6346117).sum := by decide
  have hdescent : baseEnd_6346117 < baseStart_6346117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346137 : List Nat := [1, 2, 1, 2, 1, 5, 4, 7]
def baseStart_6346137 : Nat := 118140960795 + 6346137 * 2 ^ 59
def prefixEnd_6346137 : Nat := 4983230072969 + 3 ^ 40 * 6346137 * 2
def baseEnd_6346137 : Nat := 120689577047479349759339

theorem tailTrace_6346137 : CollatzResearch.WordTrace tailWord_6346137 prefixEnd_6346137 120689577047479349759339 := by
  unfold tailWord_6346137
  simp only [CollatzResearch.WordTrace]
  refine ⟨231462631810036957756284665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154308421206691305170856443 231462631810036957756284665)
  ·
    refine ⟨173596973857527718317213499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231462631810036957756284665 173596973857527718317213499)
    ·
      refine ⟨260395460786291577475820249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173596973857527718317213499 260395460786291577475820249)
      ·
        refine ⟨195296595589718683106865187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260395460786291577475820249 195296595589718683106865187)
        ·
          refine ⟨292944893384578024660297781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195296595589718683106865187 292944893384578024660297781)
          ·
            refine ⟨27463583754804189811902917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292944893384578024660297781 27463583754804189811902917)
            ·
              refine ⟨5149421954025785589731797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27463583754804189811902917 5149421954025785589731797)
              ·
                refine ⟨120689577047479349759339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5149421954025785589731797 120689577047479349759339)
                ·
                  rfl

theorem cell23_6346137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 7].length) (baseStart_6346137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346137 prefixEnd_6346137 := by exact prefixLift 6346137
  have htrace : WordTrace (prefixWord ++ tailWord_6346137) baseStart_6346137 baseEnd_6346137 := by
    simpa [prefixWord, tailWord_6346137, baseEnd_6346137] using wordTrace_append hprefix tailTrace_6346137
  have hstable : (prefixWord ++ tailWord_6346137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346137).length < 2 ^ (prefixWord ++ tailWord_6346137).sum := by decide
  have hdescent : baseEnd_6346137 < baseStart_6346137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346142 : List Nat := [4, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6346142 : Nat := 118140960795 + 6346142 * 2 ^ 59
def prefixEnd_6346142 : Nat := 4983230072969 + 3 ^ 40 * 6346142 * 2
def baseEnd_6346142 : Nat := 3258621147685214923939631

theorem tailTrace_6346142 : CollatzResearch.WordTrace tailWord_6346142 prefixEnd_6346142 3258621147685214923939631 := by
  unfold tailWord_6346142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28932851771877355451277085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154308542783345895740144453 28932851771877355451277085)
  ·
    refine ⟨10849819414454008294228907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28932851771877355451277085 10849819414454008294228907)
    ·
      refine ⟨16274729121681012441343361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849819414454008294228907 16274729121681012441343361)
      ·
        refine ⟨12206046841260759331007521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16274729121681012441343361 12206046841260759331007521)
        ·
          refine ⟨9154535130945569498255641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12206046841260759331007521 9154535130945569498255641)
          ·
            refine ⟨6865901348209177123691731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154535130945569498255641 6865901348209177123691731)
            ·
              refine ⟨10298852022313765685537597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865901348209177123691731 10298852022313765685537597)
              ·
                refine ⟨3862069508367662132076599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10298852022313765685537597 3862069508367662132076599)
                ·
                  refine ⟨5793104262551493198114899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862069508367662132076599 5793104262551493198114899)
                  ·
                    refine ⟨8689656393827239797172349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793104262551493198114899 8689656393827239797172349)
                    ·
                      refine ⟨3258621147685214923939631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689656393827239797172349 3258621147685214923939631)
                      ·
                        rfl

theorem cell23_6346142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6346142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346142 prefixEnd_6346142 := by exact prefixLift 6346142
  have htrace : WordTrace (prefixWord ++ tailWord_6346142) baseStart_6346142 baseEnd_6346142 := by
    simpa [prefixWord, tailWord_6346142, baseEnd_6346142] using wordTrace_append hprefix tailTrace_6346142
  have hstable : (prefixWord ++ tailWord_6346142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346142).length < 2 ^ (prefixWord ++ tailWord_6346142).sum := by decide
  have hdescent : baseEnd_6346142 < baseStart_6346142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346147 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3]
def baseStart_6346147 : Nat := 118140960795 + 6346147 * 2 ^ 59
def prefixEnd_6346147 : Nat := 4983230072969 + 3 ^ 40 * 6346147 * 2
def baseEnd_6346147 : Nat := 3258623715088487404377107

theorem tailTrace_6346147 : CollatzResearch.WordTrace tailWord_6346147 prefixEnd_6346147 3258623715088487404377107 := by
  unfold tailWord_6346147
  simp only [CollatzResearch.WordTrace]
  refine ⟨231462996540000729464148695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154308664360000486309432463 231462996540000729464148695)
  ·
    refine ⟨347194494810001094196223043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231462996540000729464148695 347194494810001094196223043)
    ·
      refine ⟨520791742215001641294334565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347194494810001094196223043 520791742215001641294334565)
      ·
        refine ⟨97648451665312807742687731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 520791742215001641294334565 97648451665312807742687731)
        ·
          refine ⟨146472677497969211614031597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97648451665312807742687731 146472677497969211614031597)
          ·
            refine ⟨54927254061738454355261849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146472677497969211614031597 54927254061738454355261849)
            ·
              refine ⟨41195440546303840766446387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54927254061738454355261849 41195440546303840766446387)
              ·
                refine ⟨61793160819455761149669581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41195440546303840766446387 61793160819455761149669581)
                ·
                  refine ⟨23172435307295910431126093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61793160819455761149669581 23172435307295910431126093)
                  ·
                    refine ⟨8689663240235966411672285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23172435307295910431126093 8689663240235966411672285)
                    ·
                      refine ⟨3258623715088487404377107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689663240235966411672285 3258623715088487404377107)
                      ·
                        rfl

theorem cell23_6346147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_6346147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346147 prefixEnd_6346147 := by exact prefixLift 6346147
  have htrace : WordTrace (prefixWord ++ tailWord_6346147) baseStart_6346147 baseEnd_6346147 := by
    simpa [prefixWord, tailWord_6346147, baseEnd_6346147] using wordTrace_append hprefix tailTrace_6346147
  have hstable : (prefixWord ++ tailWord_6346147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346147).length < 2 ^ (prefixWord ++ tailWord_6346147).sum := by decide
  have hdescent : baseEnd_6346147 < baseStart_6346147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346174 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_6346174 : Nat := 118140960795 + 6346174 * 2 ^ 59
def prefixEnd_6346174 : Nat := 4983230072969 + 3 ^ 40 * 6346174 * 2
def baseEnd_6346174 : Nat := 3258637579066158798739483

theorem tailTrace_6346174 : CollatzResearch.WordTrace tailWord_6346174 prefixEnd_6346174 3258637579066158798739483 := by
  unfold tailWord_6346174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28932997663862864134422697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154309320873935275383587717 28932997663862864134422697)
  ·
    refine ⟨21699748247897148100817023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28932997663862864134422697 21699748247897148100817023)
    ·
      refine ⟨32549622371845722151225535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21699748247897148100817023 32549622371845722151225535)
      ·
        refine ⟨48824433557768583226838303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32549622371845722151225535 48824433557768583226838303)
        ·
          refine ⟨73236650336652874840257455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48824433557768583226838303 73236650336652874840257455)
          ·
            refine ⟨109854975504979312260386183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73236650336652874840257455 109854975504979312260386183)
            ·
              refine ⟨164782463257468968390579275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109854975504979312260386183 164782463257468968390579275)
              ·
                refine ⟨247173694886203452585868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164782463257468968390579275 247173694886203452585868913)
                ·
                  refine ⟨185380271164652589439401685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247173694886203452585868913 185380271164652589439401685)
                  ·
                    refine ⟨4344850105421545064985977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185380271164652589439401685 4344850105421545064985977)
                    ·
                      refine ⟨3258637579066158798739483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344850105421545064985977 3258637579066158798739483)
                      ·
                        rfl

theorem cell23_6346174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_6346174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346174 prefixEnd_6346174 := by exact prefixLift 6346174
  have htrace : WordTrace (prefixWord ++ tailWord_6346174) baseStart_6346174 baseEnd_6346174 := by
    simpa [prefixWord, tailWord_6346174, baseEnd_6346174] using wordTrace_append hprefix tailTrace_6346174
  have hstable : (prefixWord ++ tailWord_6346174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346174).length < 2 ^ (prefixWord ++ tailWord_6346174).sum := by decide
  have hdescent : baseEnd_6346174 < baseStart_6346174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
