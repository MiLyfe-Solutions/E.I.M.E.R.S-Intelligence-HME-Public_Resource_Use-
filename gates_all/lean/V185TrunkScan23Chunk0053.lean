import V185TrunkScan23Chunk0052

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_313823 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 1, 2, 2]
def baseStart_313823 : Nat := 118140960795 + 313823 * 2 ^ 59
def prefixEnd_313823 : Nat := 4983230072969 + 3 ^ 40 * 313823 * 2
def baseEnd_313823 : Nat := 161142039436030899769261

theorem tailTrace_313823 : CollatzResearch.WordTrace tailWord_313823 prefixEnd_313823 161142039436030899769261 := by
  unfold tailWord_313823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446065142080342546458123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7630710094720228364305415 11446065142080342546458123)
  ·
    refine ⟨17169097713120513819687185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11446065142080342546458123 17169097713120513819687185)
    ·
      refine ⟨12876823284840385364765389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17169097713120513819687185 12876823284840385364765389)
      ·
        refine ⟨4828808731815144511787021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12876823284840385364765389 4828808731815144511787021)
        ·
          refine ⟨1810803274430679191920133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828808731815144511787021 1810803274430679191920133)
          ·
            refine ⟨339525613955752348485025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1810803274430679191920133 339525613955752348485025)
            ·
              refine ⟨254644210466814261363769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339525613955752348485025 254644210466814261363769)
              ·
                refine ⟨190983157850110696022827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254644210466814261363769 190983157850110696022827)
                ·
                  refine ⟨286474736775166044034241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190983157850110696022827 286474736775166044034241)
                  ·
                    refine ⟨214856052581374533025681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286474736775166044034241 214856052581374533025681)
                    ·
                      refine ⟨161142039436030899769261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214856052581374533025681 161142039436030899769261)
                      ·
                        rfl

theorem cell23_313823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_313823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313823 prefixEnd_313823 := by exact prefixLift 313823
  have htrace : WordTrace (prefixWord ++ tailWord_313823) baseStart_313823 baseEnd_313823 := by
    simpa [prefixWord, tailWord_313823, baseEnd_313823] using wordTrace_append hprefix tailTrace_313823
  have hstable : (prefixWord ++ tailWord_313823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313823).length < 2 ^ (prefixWord ++ tailWord_313823).sum := by decide
  have hdescent : baseEnd_313823 < baseStart_313823 := by decide
  rcases family_descends (prefixWord ++ tailWord_313823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313832 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_313832 : Nat := 118140960795 + 313832 * 2 ^ 59
def prefixEnd_313832 : Nat := 4983230072969 + 3 ^ 40 * 313832 * 2
def baseEnd_313832 : Nat := 161146660761921364556719

theorem tailTrace_313832 : CollatzResearch.WordTrace tailWord_313832 prefixEnd_313832 161146660761921364556719 := by
  unfold tailWord_313832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723196699523868541767875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7630928932698491389023833 5723196699523868541767875)
  ·
    refine ⟨8584795049285802812651813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723196699523868541767875 8584795049285802812651813)
    ·
      refine ⟨1609649071741088027372215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8584795049285802812651813 1609649071741088027372215)
      ·
        refine ⟨2414473607611632041058323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609649071741088027372215 2414473607611632041058323)
        ·
          refine ⟨3621710411417448061587485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414473607611632041058323 3621710411417448061587485)
          ·
            refine ⟨1358141404281543023095307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3621710411417448061587485 1358141404281543023095307)
            ·
              refine ⟨2037212106422314534642961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358141404281543023095307 2037212106422314534642961)
              ·
                refine ⟨1527909079816735900982221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037212106422314534642961 1527909079816735900982221)
                ·
                  refine ⟨572965904931275962868333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1527909079816735900982221 572965904931275962868333)
                  ·
                    refine ⟨214862214349228486075625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 572965904931275962868333 214862214349228486075625)
                    ·
                      refine ⟨161146660761921364556719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214862214349228486075625 161146660761921364556719)
                      ·
                        rfl

theorem cell23_313832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_313832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313832 prefixEnd_313832 := by exact prefixLift 313832
  have htrace : WordTrace (prefixWord ++ tailWord_313832) baseStart_313832 baseEnd_313832 := by
    simpa [prefixWord, tailWord_313832, baseEnd_313832] using wordTrace_append hprefix tailTrace_313832
  have hstable : (prefixWord ++ tailWord_313832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313832).length < 2 ^ (prefixWord ++ tailWord_313832).sum := by decide
  have hdescent : baseEnd_313832 < baseStart_313832 := by decide
  rcases family_descends (prefixWord ++ tailWord_313832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313885 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 7]
def baseStart_313885 : Nat := 118140960795 + 313885 * 2 ^ 59
def prefixEnd_313885 : Nat := 4983230072969 + 3 ^ 40 * 313885 * 2
def baseEnd_313885 : Nat := 17908208359623295243775

theorem tailTrace_313885 : CollatzResearch.WordTrace tailWord_313885 prefixEnd_313885 17908208359623295243775 := by
  unfold tailWord_313885
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448326467855727135215109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7632217645237151423476739 11448326467855727135215109)
  ·
    refine ⟨2146561212722948837852833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11448326467855727135215109 2146561212722948837852833)
    ·
      refine ⟨1609920909542211628389625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2146561212722948837852833 1609920909542211628389625)
      ·
        refine ⟨1207440682156658721292219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609920909542211628389625 1207440682156658721292219)
        ·
          refine ⟨1811161023234988081938329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207440682156658721292219 1811161023234988081938329)
          ·
            refine ⟨1358370767426241061453747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1811161023234988081938329 1358370767426241061453747)
            ·
              refine ⟨2037556151139361592180621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1358370767426241061453747 2037556151139361592180621)
              ·
                refine ⟨764083556677260597067733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2037556151139361592180621 764083556677260597067733)
                ·
                  refine ⟨17908208359623295243775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 764083556677260597067733 17908208359623295243775)
                  ·
                    rfl

theorem cell23_313885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_313885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313885 prefixEnd_313885 := by exact prefixLift 313885
  have htrace : WordTrace (prefixWord ++ tailWord_313885) baseStart_313885 baseEnd_313885 := by
    simpa [prefixWord, tailWord_313885, baseEnd_313885] using wordTrace_append hprefix tailTrace_313885
  have hstable : (prefixWord ++ tailWord_313885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313885).length < 2 ^ (prefixWord ++ tailWord_313885).sum := by decide
  have hdescent : baseEnd_313885 < baseStart_313885 := by decide
  rcases family_descends (prefixWord ++ tailWord_313885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313896 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_313896 : Nat := 118140960795 + 313896 * 2 ^ 59
def prefixEnd_313896 : Nat := 4983230072969 + 3 ^ 40 * 313896 * 2
def baseEnd_313896 : Nat := 161179523523809114156425

theorem tailTrace_313896 : CollatzResearch.WordTrace tailWord_313896 prefixEnd_313896 161179523523809114156425 := by
  unfold tailWord_313896
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724363835407938006932771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7632485113877250675910361 5724363835407938006932771)
  ·
    refine ⟨8586545753111907010399157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724363835407938006932771 8586545753111907010399157)
    ·
      refine ⟨804988664354241282224921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8586545753111907010399157 804988664354241282224921)
      ·
        refine ⟨603741498265680961668691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804988664354241282224921 603741498265680961668691)
        ·
          refine ⟨905612247398521442503037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603741498265680961668691 905612247398521442503037)
          ·
            refine ⟨339604592774445540938639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 905612247398521442503037 339604592774445540938639)
            ·
              refine ⟨509406889161668311407959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339604592774445540938639 509406889161668311407959)
              ·
                refine ⟨764110333742502467111939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509406889161668311407959 764110333742502467111939)
                ·
                  refine ⟨1146165500613753700667909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764110333742502467111939 1146165500613753700667909)
                  ·
                    refine ⟨214906031365078818875233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146165500613753700667909 214906031365078818875233)
                    ·
                      refine ⟨161179523523809114156425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214906031365078818875233 161179523523809114156425)
                      ·
                        rfl

theorem cell23_313896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_313896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313896 prefixEnd_313896 := by exact prefixLift 313896
  have htrace : WordTrace (prefixWord ++ tailWord_313896) baseStart_313896 baseEnd_313896 := by
    simpa [prefixWord, tailWord_313896, baseEnd_313896] using wordTrace_append hprefix tailTrace_313896
  have hstable : (prefixWord ++ tailWord_313896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313896).length < 2 ^ (prefixWord ++ tailWord_313896).sum := by decide
  have hdescent : baseEnd_313896 < baseStart_313896 := by decide
  rcases family_descends (prefixWord ++ tailWord_313896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313935 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_313935 : Nat := 118140960795 + 313935 * 2 ^ 59
def prefixEnd_313935 : Nat := 4983230072969 + 3 ^ 40 * 313935 * 2
def baseEnd_313935 : Nat := 161199549269334461568745

theorem tailTrace_313935 : CollatzResearch.WordTrace tailWord_313935 prefixEnd_313935 161199549269334461568745 := by
  unfold tailWord_313935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11450150117674585674535259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7633433411783057116356839 11450150117674585674535259)
  ·
    refine ⟨17175225176511878511802889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11450150117674585674535259 17175225176511878511802889)
    ·
      refine ⟨12881418882383908883852167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17175225176511878511802889 12881418882383908883852167)
      ·
        refine ⟨19322128323575863325778251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12881418882383908883852167 19322128323575863325778251)
        ·
          refine ⟨28983192485363794988667377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19322128323575863325778251 28983192485363794988667377)
          ·
            refine ⟨21737394364022846241500533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28983192485363794988667377 21737394364022846241500533)
            ·
              refine ⟨2037880721627141835140675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21737394364022846241500533 2037880721627141835140675)
              ·
                refine ⟨3056821082440712752711013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037880721627141835140675 3056821082440712752711013)
                ·
                  refine ⟨573153952957633641133315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3056821082440712752711013 573153952957633641133315)
                  ·
                    refine ⟨859730929436450461699973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573153952957633641133315 859730929436450461699973)
                    ·
                      refine ⟨161199549269334461568745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 859730929436450461699973 161199549269334461568745)
                      ·
                        rfl

theorem cell23_313935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_313935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313935 prefixEnd_313935 := by exact prefixLift 313935
  have htrace : WordTrace (prefixWord ++ tailWord_313935) baseStart_313935 baseEnd_313935 := by
    simpa [prefixWord, tailWord_313935, baseEnd_313935] using wordTrace_append hprefix tailTrace_313935
  have hstable : (prefixWord ++ tailWord_313935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313935).length < 2 ^ (prefixWord ++ tailWord_313935).sum := by decide
  have hdescent : baseEnd_313935 < baseStart_313935 := by decide
  rcases family_descends (prefixWord ++ tailWord_313935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313952 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2]
def baseStart_313952 : Nat := 118140960795 + 313952 * 2 ^ 59
def prefixEnd_313952 : Nat := 4983230072969 + 3 ^ 40 * 313952 * 2
def baseEnd_313952 : Nat := 161208278440460895056167

theorem tailTrace_313952 : CollatzResearch.WordTrace tailWord_313952 prefixEnd_313952 161208278440460895056167 := by
  unfold tailWord_313952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725385079306498788952055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7633846772408665051936073 5725385079306498788952055)
  ·
    refine ⟨8588077618959748183428083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5725385079306498788952055 8588077618959748183428083)
    ·
      refine ⟨12882116428439622275142125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8588077618959748183428083 12882116428439622275142125)
      ·
        refine ⟨4830793660664858353178297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12882116428439622275142125 4830793660664858353178297)
        ·
          refine ⟨3623095245498643764883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4830793660664858353178297 3623095245498643764883723)
          ·
            refine ⟨5434642868247965647325585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623095245498643764883723 5434642868247965647325585)
            ·
              refine ⟨4075982151185974235494189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434642868247965647325585 4075982151185974235494189)
              ·
                refine ⟨1528493306694740338310321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4075982151185974235494189 1528493306694740338310321)
                ·
                  refine ⟨1146369980021055253732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528493306694740338310321 1146369980021055253732741)
                  ·
                    refine ⟨214944371253947860074889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1146369980021055253732741 214944371253947860074889)
                    ·
                      refine ⟨161208278440460895056167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 214944371253947860074889 161208278440460895056167)
                      ·
                        rfl

theorem cell23_313952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_313952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313952 prefixEnd_313952 := by exact prefixLift 313952
  have htrace : WordTrace (prefixWord ++ tailWord_313952) baseStart_313952 baseEnd_313952 := by
    simpa [prefixWord, tailWord_313952, baseEnd_313952] using wordTrace_append hprefix tailTrace_313952
  have hstable : (prefixWord ++ tailWord_313952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313952).length < 2 ^ (prefixWord ++ tailWord_313952).sum := by decide
  have hdescent : baseEnd_313952 < baseStart_313952 := by decide
  rcases family_descends (prefixWord ++ tailWord_313952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313962 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_313962 : Nat := 118140960795 + 313962 * 2 ^ 59
def prefixEnd_313962 : Nat := 4983230072969 + 3 ^ 40 * 313962 * 2
def baseEnd_313962 : Nat := 53737804415668618643707

theorem tailTrace_313962 : CollatzResearch.WordTrace tailWord_313962 prefixEnd_313962 53737804415668618643707 := by
  unfold tailWord_313962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862783722144192321442035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7634089925717846190512093 2862783722144192321442035)
  ·
    refine ⟨4294175583216288482163053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2862783722144192321442035 4294175583216288482163053)
    ·
      refine ⟨1610315843706108180811145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4294175583216288482163053 1610315843706108180811145)
      ·
        refine ⟨1207736882779581135608359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1610315843706108180811145 1207736882779581135608359)
        ·
          refine ⟨1811605324169371703412539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207736882779581135608359 1811605324169371703412539)
          ·
            refine ⟨2717407986254057555118809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811605324169371703412539 2717407986254057555118809)
            ·
              refine ⟨2038055989690543166339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717407986254057555118809 2038055989690543166339107)
              ·
                refine ⟨3057083984535814749508661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038055989690543166339107 3057083984535814749508661)
                ·
                  refine ⟨286601623550232632766437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057083984535814749508661 286601623550232632766437)
                  ·
                    refine ⟨53737804415668618643707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286601623550232632766437 53737804415668618643707)
                    ·
                      rfl

theorem cell23_313962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_313962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_313962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_313962 prefixEnd_313962 := by exact prefixLift 313962
  have htrace : WordTrace (prefixWord ++ tailWord_313962) baseStart_313962 baseEnd_313962 := by
    simpa [prefixWord, tailWord_313962, baseEnd_313962] using wordTrace_append hprefix tailTrace_313962
  have hstable : (prefixWord ++ tailWord_313962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313962).length < 2 ^ (prefixWord ++ tailWord_313962).sum := by decide
  have hdescent : baseEnd_313962 < baseStart_313962 := by decide
  rcases family_descends (prefixWord ++ tailWord_313962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314023 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_314023 : Nat := 118140960795 + 314023 * 2 ^ 59
def prefixEnd_314023 : Nat := 4983230072969 + 3 ^ 40 * 314023 * 2
def baseEnd_314023 : Nat := 161244735566930117268341

theorem tailTrace_314023 : CollatzResearch.WordTrace tailWord_314023 prefixEnd_314023 161244735566930117268341 := by
  unfold tailWord_314023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453359741355776703738723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7635573160903851135825815 11453359741355776703738723)
  ·
    refine ⟨17180039612033665055608085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453359741355776703738723 17180039612033665055608085)
    ·
      refine ⟨805314356814078049481629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17180039612033665055608085 805314356814078049481629)
      ·
        refine ⟨301992883805279268555611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 805314356814078049481629 301992883805279268555611)
        ·
          refine ⟨452989325707918902833417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301992883805279268555611 452989325707918902833417)
          ·
            refine ⟨339741994280939177125063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452989325707918902833417 339741994280939177125063)
            ·
              refine ⟨509612991421408765687595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339741994280939177125063 509612991421408765687595)
              ·
                refine ⟨764419487132113148531393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509612991421408765687595 764419487132113148531393)
                ·
                  refine ⟨573314615349084861398545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 764419487132113148531393 573314615349084861398545)
                  ·
                    refine ⟨429985961511813646048909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573314615349084861398545 429985961511813646048909)
                    ·
                      refine ⟨161244735566930117268341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 429985961511813646048909 161244735566930117268341)
                      ·
                        rfl

theorem cell23_314023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_314023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314023 prefixEnd_314023 := by exact prefixLift 314023
  have htrace : WordTrace (prefixWord ++ tailWord_314023) baseStart_314023 baseEnd_314023 := by
    simpa [prefixWord, tailWord_314023, baseEnd_314023] using wordTrace_append hprefix tailTrace_314023
  have hstable : (prefixWord ++ tailWord_314023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314023).length < 2 ^ (prefixWord ++ tailWord_314023).sum := by decide
  have hdescent : baseEnd_314023 < baseStart_314023 := by decide
  rcases family_descends (prefixWord ++ tailWord_314023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314039 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 1, 5]
def baseStart_314039 : Nat := 118140960795 + 314039 * 2 ^ 59
def prefixEnd_314039 : Nat := 4983230072969 + 3 ^ 40 * 314039 * 2
def baseEnd_314039 : Nat := 53750983752467351556089

theorem tailTrace_314039 : CollatzResearch.WordTrace tailWord_314039 prefixEnd_314039 53750983752467351556089 := by
  unfold tailWord_314039
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453943309297811436321171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7635962206198540957547447 11453943309297811436321171)
  ·
    refine ⟨17180914963946717154481757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11453943309297811436321171 17180914963946717154481757)
    ·
      refine ⟨6442843111480018932930659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17180914963946717154481757 6442843111480018932930659)
      ·
        refine ⟨9664264667220028399395989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442843111480018932930659 9664264667220028399395989)
        ·
          refine ⟨453012406275938831221687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9664264667220028399395989 453012406275938831221687)
          ·
            refine ⟨679518609413908246832531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453012406275938831221687 679518609413908246832531)
            ·
              refine ⟨1019277914120862370248797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679518609413908246832531 1019277914120862370248797)
              ·
                refine ⟨382229217795323388843299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019277914120862370248797 382229217795323388843299)
                ·
                  refine ⟨573343826692985083264949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382229217795323388843299 573343826692985083264949)
                  ·
                    refine ⟨53750983752467351556089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 573343826692985083264949 53750983752467351556089)
                    ·
                      rfl

theorem cell23_314039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_314039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314039 prefixEnd_314039 := by exact prefixLift 314039
  have htrace : WordTrace (prefixWord ++ tailWord_314039) baseStart_314039 baseEnd_314039 := by
    simpa [prefixWord, tailWord_314039, baseEnd_314039] using wordTrace_append hprefix tailTrace_314039
  have hstable : (prefixWord ++ tailWord_314039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314039).length < 2 ^ (prefixWord ++ tailWord_314039).sum := by decide
  have hdescent : baseEnd_314039 < baseStart_314039 := by decide
  rcases family_descends (prefixWord ++ tailWord_314039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314062 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_314062 : Nat := 118140960795 + 314062 * 2 ^ 59
def prefixEnd_314062 : Nat := 4983230072969 + 3 ^ 40 * 314062 * 2
def baseEnd_314062 : Nat := 161264761312455464680661

theorem tailTrace_314062 : CollatzResearch.WordTrace tailWord_314062 prefixEnd_314062 161264761312455464680661 := by
  unfold tailWord_314062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431847773526810795551055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7636521458809657576272293 1431847773526810795551055)
  ·
    refine ⟨2147771660290216193326583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431847773526810795551055 2147771660290216193326583)
    ·
      refine ⟨3221657490435324289989875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147771660290216193326583 3221657490435324289989875)
      ·
        refine ⟨4832486235652986434984813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221657490435324289989875 4832486235652986434984813)
        ·
          refine ⟨1812182338369869913119305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4832486235652986434984813 1812182338369869913119305)
          ·
            refine ⟨1359136753777402434839479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1812182338369869913119305 1359136753777402434839479)
            ·
              refine ⟨2038705130666103652259219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359136753777402434839479 2038705130666103652259219)
              ·
                refine ⟨3058057695999155478388829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038705130666103652259219 3058057695999155478388829)
                ·
                  refine ⟨1146771635999683304395811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3058057695999155478388829 1146771635999683304395811)
                  ·
                    refine ⟨1720157453999524956593717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1146771635999683304395811 1720157453999524956593717)
                    ·
                      refine ⟨161264761312455464680661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1720157453999524956593717 161264761312455464680661)
                      ·
                        rfl

theorem cell23_314062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_314062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314062 prefixEnd_314062 := by exact prefixLift 314062
  have htrace : WordTrace (prefixWord ++ tailWord_314062) baseStart_314062 baseEnd_314062 := by
    simpa [prefixWord, tailWord_314062, baseEnd_314062] using wordTrace_append hprefix tailTrace_314062
  have hstable : (prefixWord ++ tailWord_314062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314062).length < 2 ^ (prefixWord ++ tailWord_314062).sum := by decide
  have hdescent : baseEnd_314062 < baseStart_314062 := by decide
  rcases family_descends (prefixWord ++ tailWord_314062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314065 : List Nat := [1, 2, 2, 1, 2, 3, 2, 10]
def baseStart_314065 : Nat := 118140960795 + 314065 * 2 ^ 59
def prefixEnd_314065 : Nat := 4983230072969 + 3 ^ 40 * 314065 * 2
def baseEnd_314065 : Nat := 5972825990904405664561

theorem tailTrace_314065 : CollatzResearch.WordTrace tailWord_314065 prefixEnd_314065 5972825990904405664561 := by
  unfold tailWord_314065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11454891607203617876767649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7636594404802411917845099 11454891607203617876767649)
  ·
    refine ⟨8591168705402713407575737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11454891607203617876767649 8591168705402713407575737)
    ·
      refine ⟨6443376529052035055681803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8591168705402713407575737 6443376529052035055681803)
      ·
        refine ⟨9665064793578052583522705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443376529052035055681803 9665064793578052583522705)
        ·
          refine ⟨7248798595183539437642029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9665064793578052583522705 7248798595183539437642029)
          ·
            refine ⟨2718299473193827289115761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7248798595183539437642029 2718299473193827289115761)
            ·
              refine ⟨2038724604895370466836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718299473193827289115761 2038724604895370466836821)
              ·
                refine ⟨5972825990904405664561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2038724604895370466836821 5972825990904405664561)
                ·
                  rfl

theorem cell23_314065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 10].length) (baseStart_314065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314065 prefixEnd_314065 := by exact prefixLift 314065
  have htrace : WordTrace (prefixWord ++ tailWord_314065) baseStart_314065 baseEnd_314065 := by
    simpa [prefixWord, tailWord_314065, baseEnd_314065] using wordTrace_append hprefix tailTrace_314065
  have hstable : (prefixWord ++ tailWord_314065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314065).length < 2 ^ (prefixWord ++ tailWord_314065).sum := by decide
  have hdescent : baseEnd_314065 < baseStart_314065 := by decide
  rcases family_descends (prefixWord ++ tailWord_314065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314072 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_314072 : Nat := 118140960795 + 314072 * 2 ^ 59
def prefixEnd_314072 : Nat := 4983230072969 + 3 ^ 40 * 314072 * 2
def baseEnd_314072 : Nat := 161269896119000425555615

theorem tailTrace_314072 : CollatzResearch.WordTrace tailWord_314072 prefixEnd_314072 161269896119000425555615 := by
  unfold tailWord_314072
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727573459089129036136235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7636764612118838714848313 5727573459089129036136235)
  ·
    refine ⟨8591360188633693554204353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727573459089129036136235 8591360188633693554204353)
    ·
      refine ⟨6443520141475270165653265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8591360188633693554204353 6443520141475270165653265)
      ·
        refine ⟨4832640106106452624239949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443520141475270165653265 4832640106106452624239949)
        ·
          refine ⟨1812240039789919734089981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4832640106106452624239949 1812240039789919734089981)
          ·
            refine ⟨679590014921219900283743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1812240039789919734089981 679590014921219900283743)
            ·
              refine ⟨1019385022381829850425615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679590014921219900283743 1019385022381829850425615)
              ·
                refine ⟨1529077533572744775638423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019385022381829850425615 1529077533572744775638423)
                ·
                  refine ⟨2293616300359117163457635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529077533572744775638423 2293616300359117163457635)
                  ·
                    refine ⟨3440424450538675745186453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293616300359117163457635 3440424450538675745186453)
                    ·
                      refine ⟨161269896119000425555615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3440424450538675745186453 161269896119000425555615)
                      ·
                        rfl

theorem cell23_314072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_314072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314072 prefixEnd_314072 := by exact prefixLift 314072
  have htrace : WordTrace (prefixWord ++ tailWord_314072) baseStart_314072 baseEnd_314072 := by
    simpa [prefixWord, tailWord_314072, baseEnd_314072] using wordTrace_append hprefix tailTrace_314072
  have hstable : (prefixWord ++ tailWord_314072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314072).length < 2 ^ (prefixWord ++ tailWord_314072).sum := by decide
  have hdescent : baseEnd_314072 < baseStart_314072 := by decide
  rcases family_descends (prefixWord ++ tailWord_314072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314076 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_314076 : Nat := 118140960795 + 314076 * 2 ^ 59
def prefixEnd_314076 : Nat := 4983230072969 + 3 ^ 40 * 314076 * 2
def baseEnd_314076 : Nat := 161271950041618409905597

theorem tailTrace_314076 : CollatzResearch.WordTrace tailWord_314076 prefixEnd_314076 161271950041618409905597 := by
  unfold tailWord_314076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727646405081883377709041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7636861873442511170278721 5727646405081883377709041)
  ·
    refine ⟨4295734803811412533281781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5727646405081883377709041 4295734803811412533281781)
    ·
      refine ⟨402725137857319924995167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4295734803811412533281781 402725137857319924995167)
      ·
        refine ⟨604087706785979887492751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402725137857319924995167 604087706785979887492751)
        ·
          refine ⟨906131560178969831239127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604087706785979887492751 906131560178969831239127)
          ·
            refine ⟨1359197340268454746858691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906131560178969831239127 1359197340268454746858691)
            ·
              refine ⟨2038796010402682120288037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359197340268454746858691 2038796010402682120288037)
              ·
                refine ⟨382274251950502897554007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2038796010402682120288037 382274251950502897554007)
                ·
                  refine ⟨573411377925754346331011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382274251950502897554007 573411377925754346331011)
                  ·
                    refine ⟨860117066888631519496517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573411377925754346331011 860117066888631519496517)
                    ·
                      refine ⟨161271950041618409905597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 860117066888631519496517 161271950041618409905597)
                      ·
                        rfl

theorem cell23_314076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_314076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314076 prefixEnd_314076 := by exact prefixLift 314076
  have htrace : WordTrace (prefixWord ++ tailWord_314076) baseStart_314076 baseEnd_314076 := by
    simpa [prefixWord, tailWord_314076, baseEnd_314076] using wordTrace_append hprefix tailTrace_314076
  have hstable : (prefixWord ++ tailWord_314076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314076).length < 2 ^ (prefixWord ++ tailWord_314076).sum := by decide
  have hdescent : baseEnd_314076 < baseStart_314076 := by decide
  rcases family_descends (prefixWord ++ tailWord_314076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314079 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_314079 : Nat := 118140960795 + 314079 * 2 ^ 59
def prefixEnd_314079 : Nat := 4983230072969 + 3 ^ 40 * 314079 * 2
def baseEnd_314079 : Nat := 161273490483581898168083

theorem tailTrace_314079 : CollatzResearch.WordTrace tailWord_314079 prefixEnd_314079 161273490483581898168083 := by
  unfold tailWord_314079
  simp only [CollatzResearch.WordTrace]
  refine ⟨11455402229152898267777291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7636934819435265511851527 11455402229152898267777291)
  ·
    refine ⟨17183103343729347401665937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11455402229152898267777291 17183103343729347401665937)
    ·
      refine ⟨12887327507797010551249453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17183103343729347401665937 12887327507797010551249453)
      ·
        refine ⟨4832747815423878956718545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12887327507797010551249453 4832747815423878956718545)
        ·
          refine ⟨3624560861567909217538909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832747815423878956718545 3624560861567909217538909)
          ·
            refine ⟨1359210323087965956577091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3624560861567909217538909 1359210323087965956577091)
            ·
              refine ⟨2038815484631948934865637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359210323087965956577091 2038815484631948934865637)
              ·
                refine ⟨382277903368490425287307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2038815484631948934865637 382277903368490425287307)
                ·
                  refine ⟨573416855052735637930961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382277903368490425287307 573416855052735637930961)
                  ·
                    refine ⟨430062641289551728448221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573416855052735637930961 430062641289551728448221)
                    ·
                      refine ⟨161273490483581898168083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430062641289551728448221 161273490483581898168083)
                      ·
                        rfl

theorem cell23_314079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_314079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314079 prefixEnd_314079 := by exact prefixLift 314079
  have htrace : WordTrace (prefixWord ++ tailWord_314079) baseStart_314079 baseEnd_314079 := by
    simpa [prefixWord, tailWord_314079, baseEnd_314079] using wordTrace_append hprefix tailTrace_314079
  have hstable : (prefixWord ++ tailWord_314079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314079).length < 2 ^ (prefixWord ++ tailWord_314079).sum := by decide
  have hdescent : baseEnd_314079 < baseStart_314079 := by decide
  rcases family_descends (prefixWord ++ tailWord_314079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314092 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_314092 : Nat := 118140960795 + 314092 * 2 ^ 59
def prefixEnd_314092 : Nat := 4983230072969 + 3 ^ 40 * 314092 * 2
def baseEnd_314092 : Nat := 161280165732090347305523

theorem tailTrace_314092 : CollatzResearch.WordTrace tailWord_314092 prefixEnd_314092 161280165732090347305523 := by
  unfold tailWord_314092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727938189052900744000265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7637250918737200992000353 5727938189052900744000265)
  ·
    refine ⟨4295953641789675558000199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5727938189052900744000265 4295953641789675558000199)
    ·
      refine ⟨6443930462684513337000299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295953641789675558000199 6443930462684513337000299)
      ·
        refine ⟨9665895694026770005500449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443930462684513337000299 9665895694026770005500449)
        ·
          refine ⟨7249421770520077504125337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9665895694026770005500449 7249421770520077504125337)
          ·
            refine ⟨5437066327890058128094003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7249421770520077504125337 5437066327890058128094003)
            ·
              refine ⟨8155599491835087192141005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437066327890058128094003 8155599491835087192141005)
              ·
                refine ⟨3058349809438157697052877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8155599491835087192141005 3058349809438157697052877)
                ·
                  refine ⟨1146881178539309136394829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3058349809438157697052877 1146881178539309136394829)
                  ·
                    refine ⟨430080441952240926148061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1146881178539309136394829 430080441952240926148061)
                    ·
                      refine ⟨161280165732090347305523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430080441952240926148061 161280165732090347305523)
                      ·
                        rfl

theorem cell23_314092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_314092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314092 prefixEnd_314092 := by exact prefixLift 314092
  have htrace : WordTrace (prefixWord ++ tailWord_314092) baseStart_314092 baseEnd_314092 := by
    simpa [prefixWord, tailWord_314092, baseEnd_314092] using wordTrace_append hprefix tailTrace_314092
  have hstable : (prefixWord ++ tailWord_314092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314092).length < 2 ^ (prefixWord ++ tailWord_314092).sum := by decide
  have hdescent : baseEnd_314092 < baseStart_314092 := by decide
  rcases family_descends (prefixWord ++ tailWord_314092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314109 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_314109 : Nat := 118140960795 + 314109 * 2 ^ 59
def prefixEnd_314109 : Nat := 4983230072969 + 3 ^ 40 * 314109 * 2
def baseEnd_314109 : Nat := 161288894903216780792945

theorem tailTrace_314109 : CollatzResearch.WordTrace tailWord_314109 prefixEnd_314109 161288894903216780792945 := by
  unfold tailWord_314109
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456496419044213391369381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7637664279362808927579587 11456496419044213391369381)
  ·
    refine ⟨2148093078570790010881759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11456496419044213391369381 2148093078570790010881759)
    ·
      refine ⟨3222139617856185016322639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148093078570790010881759 3222139617856185016322639)
      ·
        refine ⟨4833209426784277524483959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222139617856185016322639 4833209426784277524483959)
        ·
          refine ⟨7249814140176416286725939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833209426784277524483959 7249814140176416286725939)
          ·
            refine ⟨10874721210264624430088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249814140176416286725939 10874721210264624430088909)
            ·
              refine ⟨4078020453849234161283341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10874721210264624430088909 4078020453849234161283341)
              ·
                refine ⟨1529257670193462810481253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4078020453849234161283341 1529257670193462810481253)
                ·
                  refine ⟨286735813161274276965235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1529257670193462810481253 286735813161274276965235)
                  ·
                    refine ⟨430103719741911415447853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 286735813161274276965235 430103719741911415447853)
                    ·
                      refine ⟨161288894903216780792945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430103719741911415447853 161288894903216780792945)
                      ·
                        rfl

theorem cell23_314109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_314109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314109 prefixEnd_314109 := by exact prefixLift 314109
  have htrace : WordTrace (prefixWord ++ tailWord_314109) baseStart_314109 baseEnd_314109 := by
    simpa [prefixWord, tailWord_314109, baseEnd_314109] using wordTrace_append hprefix tailTrace_314109
  have hstable : (prefixWord ++ tailWord_314109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314109).length < 2 ^ (prefixWord ++ tailWord_314109).sum := by decide
  have hdescent : baseEnd_314109 < baseStart_314109 := by decide
  rcases family_descends (prefixWord ++ tailWord_314109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314110 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_314110 : Nat := 118140960795 + 314110 * 2 ^ 59
def prefixEnd_314110 : Nat := 4983230072969 + 3 ^ 40 * 314110 * 2
def baseEnd_314110 : Nat := 161289408383871276880441

theorem tailTrace_314110 : CollatzResearch.WordTrace tailWord_314110 prefixEnd_314110 161289408383871276880441 := by
  unfold tailWord_314110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432066611505073820269473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7637688594693727041437189 1432066611505073820269473)
  ·
    refine ⟨1074049958628805365202105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1432066611505073820269473 1074049958628805365202105)
    ·
      refine ⟨805537468971604023901579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074049958628805365202105 805537468971604023901579)
      ·
        refine ⟨1208306203457406035852369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805537468971604023901579 1208306203457406035852369)
        ·
          refine ⟨906229652593054526889277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1208306203457406035852369 906229652593054526889277)
          ·
            refine ⟨339836119722395447583479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906229652593054526889277 339836119722395447583479)
            ·
              refine ⟨509754179583593171375219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339836119722395447583479 509754179583593171375219)
              ·
                refine ⟨764631269375389757062829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509754179583593171375219 764631269375389757062829)
                ·
                  refine ⟨286736726015771158898561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 764631269375389757062829 286736726015771158898561)
                  ·
                    refine ⟨215052544511828369173921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286736726015771158898561 215052544511828369173921)
                    ·
                      refine ⟨161289408383871276880441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215052544511828369173921 161289408383871276880441)
                      ·
                        rfl

theorem cell23_314110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_314110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314110 prefixEnd_314110 := by exact prefixLift 314110
  have htrace : WordTrace (prefixWord ++ tailWord_314110) baseStart_314110 baseEnd_314110 := by
    simpa [prefixWord, tailWord_314110, baseEnd_314110] using wordTrace_append hprefix tailTrace_314110
  have hstable : (prefixWord ++ tailWord_314110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314110).length < 2 ^ (prefixWord ++ tailWord_314110).sum := by decide
  have hdescent : baseEnd_314110 < baseStart_314110 := by decide
  rcases family_descends (prefixWord ++ tailWord_314110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314130 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_314130 : Nat := 118140960795 + 314130 * 2 ^ 59
def prefixEnd_314130 : Nat := 4983230072969 + 3 ^ 40 * 314130 * 2
def baseEnd_314130 : Nat := 161299677996961198630349

theorem tailTrace_314130 : CollatzResearch.WordTrace tailWord_314130 prefixEnd_314130 161299677996961198630349 := by
  unfold tailWord_314130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864315587992033494470961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7638174901312089318589229 2864315587992033494470961)
  ·
    refine ⟨2148236690994025120853221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2864315587992033494470961 2148236690994025120853221)
    ·
      refine ⟨402794379561379710159979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2148236690994025120853221 402794379561379710159979)
      ·
        refine ⟨604191569342069565239969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402794379561379710159979 604191569342069565239969)
        ·
          refine ⟨453143677006552173929977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604191569342069565239969 453143677006552173929977)
          ·
            refine ⟨339857757754914130447483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453143677006552173929977 339857757754914130447483)
            ·
              refine ⟨509786636632371195671225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339857757754914130447483 509786636632371195671225)
              ·
                refine ⟨382339977474278396753419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509786636632371195671225 382339977474278396753419)
                ·
                  refine ⟨573509966211417595130129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382339977474278396753419 573509966211417595130129)
                  ·
                    refine ⟨430132474658563196347597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573509966211417595130129 430132474658563196347597)
                    ·
                      refine ⟨161299677996961198630349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430132474658563196347597 161299677996961198630349)
                      ·
                        rfl

theorem cell23_314130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_314130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314130 prefixEnd_314130 := by exact prefixLift 314130
  have htrace : WordTrace (prefixWord ++ tailWord_314130) baseStart_314130 baseEnd_314130 := by
    simpa [prefixWord, tailWord_314130, baseEnd_314130] using wordTrace_append hprefix tailTrace_314130
  have hstable : (prefixWord ++ tailWord_314130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314130).length < 2 ^ (prefixWord ++ tailWord_314130).sum := by decide
  have hdescent : baseEnd_314130 < baseStart_314130 := by decide
  rcases family_descends (prefixWord ++ tailWord_314130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314172 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 7]
def baseStart_314172 : Nat := 118140960795 + 314172 * 2 ^ 59
def prefixEnd_314172 : Nat := 4983230072969 + 3 ^ 40 * 314172 * 2
def baseEnd_314172 : Nat := 17924582687161114922795

theorem tailTrace_314172 : CollatzResearch.WordTrace tailWord_314172 prefixEnd_314172 17924582687161114922795 := by
  unfold tailWord_314172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5729397108907987575456385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7639196145210650100608513 5729397108907987575456385)
  ·
    refine ⟨4297047831680990681592289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5729397108907987575456385 4297047831680990681592289)
    ·
      refine ⟨3222785873760743011194217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4297047831680990681592289 3222785873760743011194217)
      ·
        refine ⟨2417089405320557258395663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222785873760743011194217 2417089405320557258395663)
        ·
          refine ⟨3625634107980835887593495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417089405320557258395663 3625634107980835887593495)
          ·
            refine ⟨5438451161971253831390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625634107980835887593495 5438451161971253831390243)
            ·
              refine ⟨8157676742956880747085365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438451161971253831390243 8157676742956880747085365)
              ·
                refine ⟨764782194652207570039253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8157676742956880747085365 764782194652207570039253)
                ·
                  refine ⟨17924582687161114922795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 764782194652207570039253 17924582687161114922795)
                  ·
                    rfl

theorem cell23_314172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_314172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314172 prefixEnd_314172 := by exact prefixLift 314172
  have htrace : WordTrace (prefixWord ++ tailWord_314172) baseStart_314172 baseEnd_314172 := by
    simpa [prefixWord, tailWord_314172, baseEnd_314172] using wordTrace_append hprefix tailTrace_314172
  have hstable : (prefixWord ++ tailWord_314172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314172).length < 2 ^ (prefixWord ++ tailWord_314172).sum := by decide
  have hdescent : baseEnd_314172 < baseStart_314172 := by decide
  rcases family_descends (prefixWord ++ tailWord_314172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314209 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_314209 : Nat := 118140960795 + 314209 * 2 ^ 59
def prefixEnd_314209 : Nat := 4983230072969 + 3 ^ 40 * 314209 * 2
def baseEnd_314209 : Nat := 161340242968666389542485

theorem tailTrace_314209 : CollatzResearch.WordTrace tailWord_314209 prefixEnd_314209 161340242968666389542485 := by
  unfold tailWord_314209
  simp only [CollatzResearch.WordTrace]
  refine ⟨11460143718681930470009681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7640095812454620313339787 11460143718681930470009681)
  ·
    refine ⟨8595107789011447852507261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11460143718681930470009681 8595107789011447852507261)
    ·
      refine ⟨3223165420879292944690223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8595107789011447852507261 3223165420879292944690223)
      ·
        refine ⟨4834748131318939417035335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223165420879292944690223 4834748131318939417035335)
        ·
          refine ⟨7252122196978409125553003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834748131318939417035335 7252122196978409125553003)
          ·
            refine ⟨10878183295467613688329505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7252122196978409125553003 10878183295467613688329505)
            ·
              refine ⟨8158637471600710266247129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10878183295467613688329505 8158637471600710266247129)
              ·
                refine ⟨6118978103700532699685347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8158637471600710266247129 6118978103700532699685347)
                ·
                  refine ⟨9178467155550799049528021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118978103700532699685347 9178467155550799049528021)
                  ·
                    refine ⟨215120323958221852723313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9178467155550799049528021 215120323958221852723313)
                    ·
                      refine ⟨161340242968666389542485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215120323958221852723313 161340242968666389542485)
                      ·
                        rfl

theorem cell23_314209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_314209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314209 prefixEnd_314209 := by exact prefixLift 314209
  have htrace : WordTrace (prefixWord ++ tailWord_314209) baseStart_314209 baseEnd_314209 := by
    simpa [prefixWord, tailWord_314209, baseEnd_314209] using wordTrace_append hprefix tailTrace_314209
  have hstable : (prefixWord ++ tailWord_314209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314209).length < 2 ^ (prefixWord ++ tailWord_314209).sum := by decide
  have hdescent : baseEnd_314209 < baseStart_314209 := by decide
  rcases family_descends (prefixWord ++ tailWord_314209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314276 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_314276 : Nat := 118140960795 + 314276 * 2 ^ 59
def prefixEnd_314276 : Nat := 4983230072969 + 3 ^ 40 * 314276 * 2
def baseEnd_314276 : Nat := 161374646172517627404677

theorem tailTrace_314276 : CollatzResearch.WordTrace tailWord_314276 prefixEnd_314276 161374646172517627404677 := by
  unfold tailWord_314276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731293704719600456349341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7641724939626133941799121 5731293704719600456349341)
  ·
    refine ⟨2149235139269850171131003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5731293704719600456349341 2149235139269850171131003)
    ·
      refine ⟨3223852708904775256696505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149235139269850171131003 3223852708904775256696505)
      ·
        refine ⟨2417889531678581442522379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223852708904775256696505 2417889531678581442522379)
        ·
          refine ⟨3626834297517872163783569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417889531678581442522379 3626834297517872163783569)
          ·
            refine ⟨2720125723138404122837677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626834297517872163783569 2720125723138404122837677)
            ·
              refine ⟨1020047146176901546064129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2720125723138404122837677 1020047146176901546064129)
              ·
                refine ⟨765035359632676159548097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020047146176901546064129 765035359632676159548097)
                ·
                  refine ⟨573776519724507119661073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765035359632676159548097 573776519724507119661073)
                  ·
                    refine ⟨430332389793380339745805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 573776519724507119661073 430332389793380339745805)
                    ·
                      refine ⟨161374646172517627404677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430332389793380339745805 161374646172517627404677)
                      ·
                        rfl

theorem cell23_314276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_314276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314276 prefixEnd_314276 := by exact prefixLift 314276
  have htrace : WordTrace (prefixWord ++ tailWord_314276) baseStart_314276 baseEnd_314276 := by
    simpa [prefixWord, tailWord_314276, baseEnd_314276] using wordTrace_append hprefix tailTrace_314276
  have hstable : (prefixWord ++ tailWord_314276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314276).length < 2 ^ (prefixWord ++ tailWord_314276).sum := by decide
  have hdescent : baseEnd_314276 < baseStart_314276 := by decide
  rcases family_descends (prefixWord ++ tailWord_314276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314296 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 6]
def baseStart_314296 : Nat := 118140960795 + 314296 * 2 ^ 59
def prefixEnd_314296 : Nat := 4983230072969 + 3 ^ 40 * 314296 * 2
def baseEnd_314296 : Nat := 17931657309511949906065

theorem tailTrace_314296 : CollatzResearch.WordTrace tailWord_314296 prefixEnd_314296 17931657309511949906065 := by
  unfold tailWord_314296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731658434683372164213371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7642211246244496218951161 5731658434683372164213371)
  ·
    refine ⟨8597487652025058246320057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5731658434683372164213371 8597487652025058246320057)
    ·
      refine ⟨6448115739018793684740043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8597487652025058246320057 6448115739018793684740043)
      ·
        refine ⟨9672173608528190527110065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448115739018793684740043 9672173608528190527110065)
        ·
          refine ⟨7254130206396142895332549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9672173608528190527110065 7254130206396142895332549)
          ·
            refine ⟨1360149413699276792874853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7254130206396142895332549 1360149413699276792874853)
            ·
              refine ⟨255028015068614398664035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1360149413699276792874853 255028015068614398664035)
              ·
                refine ⟨382542022602921597996053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255028015068614398664035 382542022602921597996053)
                ·
                  refine ⟨17931657309511949906065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 382542022602921597996053 17931657309511949906065)
                  ·
                    rfl

theorem cell23_314296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_314296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314296 prefixEnd_314296 := by exact prefixLift 314296
  have htrace : WordTrace (prefixWord ++ tailWord_314296) baseStart_314296 baseEnd_314296 := by
    simpa [prefixWord, tailWord_314296, baseEnd_314296] using wordTrace_append hprefix tailTrace_314296
  have hstable : (prefixWord ++ tailWord_314296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314296).length < 2 ^ (prefixWord ++ tailWord_314296).sum := by decide
  have hdescent : baseEnd_314296 < baseStart_314296 := by decide
  rcases family_descends (prefixWord ++ tailWord_314296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314339 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 6]
def baseStart_314339 : Nat := 118140960795 + 314339 * 2 ^ 59
def prefixEnd_314339 : Nat := 4983230072969 + 3 ^ 40 * 314339 * 2
def baseEnd_314339 : Nat := 53802331817916960305629

theorem tailTrace_314339 : CollatzResearch.WordTrace tailWord_314339 prefixEnd_314339 53802331817916960305629 := by
  unfold tailWord_314339
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464885208210962672242071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7643256805473975114828047 11464885208210962672242071)
  ·
    refine ⟨17197327812316444008363107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464885208210962672242071 17197327812316444008363107)
    ·
      refine ⟨25795991718474666012544661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197327812316444008363107 25795991718474666012544661)
      ·
        refine ⟨1209187111803499969338031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25795991718474666012544661 1209187111803499969338031)
        ·
          refine ⟨1813780667705249954007047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1209187111803499969338031 1813780667705249954007047)
          ·
            refine ⟨2720671001557874931010571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813780667705249954007047 2720671001557874931010571)
            ·
              refine ⟨4081006502336812396515857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720671001557874931010571 4081006502336812396515857)
              ·
                refine ⟨3060754876752609297386893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081006502336812396515857 3060754876752609297386893)
                ·
                  refine ⟨1147783078782228486520085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3060754876752609297386893 1147783078782228486520085)
                  ·
                    refine ⟨53802331817916960305629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1147783078782228486520085 53802331817916960305629)
                    ·
                      rfl

theorem cell23_314339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_314339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314339 prefixEnd_314339 := by exact prefixLift 314339
  have htrace : WordTrace (prefixWord ++ tailWord_314339) baseStart_314339 baseEnd_314339 := by
    simpa [prefixWord, tailWord_314339, baseEnd_314339] using wordTrace_append hprefix tailTrace_314339
  have hstable : (prefixWord ++ tailWord_314339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314339).length < 2 ^ (prefixWord ++ tailWord_314339).sum := by decide
  have hdescent : baseEnd_314339 < baseStart_314339 := by decide
  rcases family_descends (prefixWord ++ tailWord_314339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314346 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_314346 : Nat := 118140960795 + 314346 * 2 ^ 59
def prefixEnd_314346 : Nat := 4983230072969 + 3 ^ 40 * 314346 * 2
def baseEnd_314346 : Nat := 161410589818332353529355

theorem tailTrace_314346 : CollatzResearch.WordTrace tailWord_314346 prefixEnd_314346 161410589818332353529355 := by
  unfold tailWord_314346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866285129796400716936723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7643427012790401911831261 2866285129796400716936723)
  ·
    refine ⟨4299427694694601075405085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866285129796400716936723 4299427694694601075405085)
    ·
      refine ⟨1612285385510475403276907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4299427694694601075405085 1612285385510475403276907)
      ·
        refine ⟨2418428078265713104915361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612285385510475403276907 2418428078265713104915361)
        ·
          refine ⟨1813821058699284828686521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418428078265713104915361 1813821058699284828686521)
          ·
            refine ⟨1360365794024463621514891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813821058699284828686521 1360365794024463621514891)
            ·
              refine ⟨2040548691036695432272337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360365794024463621514891 2040548691036695432272337)
              ·
                refine ⟨1530411518277521574204253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040548691036695432272337 1530411518277521574204253)
                ·
                  refine ⟨573904319354070590326595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1530411518277521574204253 573904319354070590326595)
                  ·
                    refine ⟨860856479031105885489893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573904319354070590326595 860856479031105885489893)
                    ·
                      refine ⟨161410589818332353529355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 860856479031105885489893 161410589818332353529355)
                      ·
                        rfl

theorem cell23_314346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_314346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314346 prefixEnd_314346 := by exact prefixLift 314346
  have htrace : WordTrace (prefixWord ++ tailWord_314346) baseStart_314346 baseEnd_314346 := by
    simpa [prefixWord, tailWord_314346, baseEnd_314346] using wordTrace_append hprefix tailTrace_314346
  have hstable : (prefixWord ++ tailWord_314346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314346).length < 2 ^ (prefixWord ++ tailWord_314346).sum := by decide
  have hdescent : baseEnd_314346 < baseStart_314346 := by decide
  rcases family_descends (prefixWord ++ tailWord_314346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314357 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_314357 : Nat := 118140960795 + 314357 * 2 ^ 59
def prefixEnd_314357 : Nat := 4983230072969 + 3 ^ 40 * 314357 * 2
def baseEnd_314357 : Nat := 161416238105531810491805

theorem tailTrace_314357 : CollatzResearch.WordTrace tailWord_314357 prefixEnd_314357 161416238105531810491805 := by
  unfold tailWord_314357
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465541722145751746397325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7643694481430501164264883 11465541722145751746397325)
  ·
    refine ⟨4299578145804656904898997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11465541722145751746397325 4299578145804656904898997)
    ·
      refine ⟨403085451169186584834281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4299578145804656904898997 403085451169186584834281)
      ·
        refine ⟨302314088376889938625711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 403085451169186584834281 302314088376889938625711)
        ·
          refine ⟨453471132565334907938567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302314088376889938625711 453471132565334907938567)
          ·
            refine ⟨680206698848002361907851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453471132565334907938567 680206698848002361907851)
            ·
              refine ⟨1020310048272003542861777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680206698848002361907851 1020310048272003542861777)
              ·
                refine ⟨765232536204002657146333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020310048272003542861777 765232536204002657146333)
                ·
                  refine ⟨286962201076500996429875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765232536204002657146333 286962201076500996429875)
                  ·
                    refine ⟨430443301614751494644813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 286962201076500996429875 430443301614751494644813)
                    ·
                      refine ⟨161416238105531810491805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430443301614751494644813 161416238105531810491805)
                      ·
                        rfl

theorem cell23_314357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_314357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314357 prefixEnd_314357 := by exact prefixLift 314357
  have htrace : WordTrace (prefixWord ++ tailWord_314357) baseStart_314357 baseEnd_314357 := by
    simpa [prefixWord, tailWord_314357, baseEnd_314357] using wordTrace_append hprefix tailTrace_314357
  have hstable : (prefixWord ++ tailWord_314357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314357).length < 2 ^ (prefixWord ++ tailWord_314357).sum := by decide
  have hdescent : baseEnd_314357 < baseStart_314357 := by decide
  rcases family_descends (prefixWord ++ tailWord_314357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314376 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_314376 : Nat := 118140960795 + 314376 * 2 ^ 59
def prefixEnd_314376 : Nat := 4983230072969 + 3 ^ 40 * 314376 * 2
def baseEnd_314376 : Nat := 161425994237967236154217

theorem tailTrace_314376 : CollatzResearch.WordTrace tailWord_314376 prefixEnd_314376 161425994237967236154217 := by
  unfold tailWord_314376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733117354538458995669491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7644156472717945327559321 5733117354538458995669491)
  ·
    refine ⟨8599676031807688493504237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5733117354538458995669491 8599676031807688493504237)
    ·
      refine ⟨3224878511927883185064089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8599676031807688493504237 3224878511927883185064089)
      ·
        refine ⟨2418658883945912388798067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3224878511927883185064089 2418658883945912388798067)
        ·
          refine ⟨3627988325918868583197101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418658883945912388798067 3627988325918868583197101)
          ·
            refine ⟨1360495622219575718698913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3627988325918868583197101 1360495622219575718698913)
            ·
              refine ⟨1020371716664681789024185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1360495622219575718698913 1020371716664681789024185)
              ·
                refine ⟨765278787498511341768139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1020371716664681789024185 765278787498511341768139)
                ·
                  refine ⟨1147918181247767012652209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765278787498511341768139 1147918181247767012652209)
                  ·
                    refine ⟨860938635935825259489157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147918181247767012652209 860938635935825259489157)
                    ·
                      refine ⟨161425994237967236154217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 860938635935825259489157 161425994237967236154217)
                      ·
                        rfl

theorem cell23_314376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_314376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314376 prefixEnd_314376 := by exact prefixLift 314376
  have htrace : WordTrace (prefixWord ++ tailWord_314376) baseStart_314376 baseEnd_314376 := by
    simpa [prefixWord, tailWord_314376, baseEnd_314376] using wordTrace_append hprefix tailTrace_314376
  have hstable : (prefixWord ++ tailWord_314376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314376).length < 2 ^ (prefixWord ++ tailWord_314376).sum := by decide
  have hdescent : baseEnd_314376 < baseStart_314376 := by decide
  rcases family_descends (prefixWord ++ tailWord_314376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314380 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_314380 : Nat := 118140960795 + 314380 * 2 ^ 59
def prefixEnd_314380 : Nat := 4983230072969 + 3 ^ 40 * 314380 * 2
def baseEnd_314380 : Nat := 161428048160585220504199

theorem tailTrace_314380 : CollatzResearch.WordTrace tailWord_314380 prefixEnd_314380 161428048160585220504199 := by
  unfold tailWord_314380
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733190300531213337242297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7644253734041617782989729 5733190300531213337242297)
  ·
    refine ⟨4299892725398410002931723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5733190300531213337242297 4299892725398410002931723)
    ·
      refine ⟨6449839088097615004397585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4299892725398410002931723 6449839088097615004397585)
      ·
        refine ⟨4837379316073211253298189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6449839088097615004397585 4837379316073211253298189)
        ·
          refine ⟨1814017243527454219986821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4837379316073211253298189 1814017243527454219986821)
          ·
            refine ⟨340128233161397666247529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1814017243527454219986821 340128233161397666247529)
            ·
              refine ⟨255096174871048249685647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340128233161397666247529 255096174871048249685647)
              ·
                refine ⟨382644262306572374528471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255096174871048249685647 382644262306572374528471)
                ·
                  refine ⟨573966393459858561792707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382644262306572374528471 573966393459858561792707)
                  ·
                    refine ⟨860949590189787842689061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573966393459858561792707 860949590189787842689061)
                    ·
                      refine ⟨161428048160585220504199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 860949590189787842689061 161428048160585220504199)
                      ·
                        rfl

theorem cell23_314380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_314380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314380 prefixEnd_314380 := by exact prefixLift 314380
  have htrace : WordTrace (prefixWord ++ tailWord_314380) baseStart_314380 baseEnd_314380 := by
    simpa [prefixWord, tailWord_314380, baseEnd_314380] using wordTrace_append hprefix tailTrace_314380
  have hstable : (prefixWord ++ tailWord_314380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314380).length < 2 ^ (prefixWord ++ tailWord_314380).sum := by decide
  have hdescent : baseEnd_314380 < baseStart_314380 := by decide
  rcases family_descends (prefixWord ++ tailWord_314380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314397 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_314397 : Nat := 118140960795 + 314397 * 2 ^ 59
def prefixEnd_314397 : Nat := 4983230072969 + 3 ^ 40 * 314397 * 2
def baseEnd_314397 : Nat := 161436777331711653991621

theorem tailTrace_314397 : CollatzResearch.WordTrace tailWord_314397 prefixEnd_314397 161436777331711653991621 := by
  unfold tailWord_314397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467000642000838577853445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7644667094667225718568963 11467000642000838577853445)
  ·
    refine ⟨2150062620375157233347521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11467000642000838577853445 2150062620375157233347521)
    ·
      refine ⟨1612546965281367925010641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150062620375157233347521 1612546965281367925010641)
      ·
        refine ⟨1209410223961025943757981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612546965281367925010641 1209410223961025943757981)
        ·
          refine ⟨453528833985384728909243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1209410223961025943757981 453528833985384728909243)
          ·
            refine ⟨680293250978077093363865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453528833985384728909243 680293250978077093363865)
            ·
              refine ⟨510219938233557820022899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680293250978077093363865 510219938233557820022899)
              ·
                refine ⟨765329907350336730034349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510219938233557820022899 765329907350336730034349)
                ·
                  refine ⟨286998715256376273762881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765329907350336730034349 286998715256376273762881)
                  ·
                    refine ⟨215249036442282205322161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286998715256376273762881 215249036442282205322161)
                    ·
                      refine ⟨161436777331711653991621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215249036442282205322161 161436777331711653991621)
                      ·
                        rfl

theorem cell23_314397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_314397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314397 prefixEnd_314397 := by exact prefixLift 314397
  have htrace : WordTrace (prefixWord ++ tailWord_314397) baseStart_314397 baseEnd_314397 := by
    simpa [prefixWord, tailWord_314397, baseEnd_314397] using wordTrace_append hprefix tailTrace_314397
  have hstable : (prefixWord ++ tailWord_314397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314397).length < 2 ^ (prefixWord ++ tailWord_314397).sum := by decide
  have hdescent : baseEnd_314397 < baseStart_314397 := by decide
  rcases family_descends (prefixWord ++ tailWord_314397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314407 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 2, 4]
def baseStart_314407 : Nat := 118140960795 + 314407 * 2 ^ 59
def prefixEnd_314407 : Nat := 4983230072969 + 3 ^ 40 * 314407 * 2
def baseEnd_314407 : Nat := 53813970712752204955525

theorem tailTrace_314407 : CollatzResearch.WordTrace tailWord_314407 prefixEnd_314407 53813970712752204955525 := by
  unfold tailWord_314407
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467365371964610285717475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7644910247976406857144983 11467365371964610285717475)
  ·
    refine ⟨17201048057946915428576213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11467365371964610285717475 17201048057946915428576213)
    ·
      refine ⟨403149563858130830357255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17201048057946915428576213 403149563858130830357255)
      ·
        refine ⟨604724345787196245535883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403149563858130830357255 604724345787196245535883)
        ·
          refine ⟨907086518680794368303825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604724345787196245535883 907086518680794368303825)
          ·
            refine ⟨680314889010595776227869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907086518680794368303825 680314889010595776227869)
            ·
              refine ⟨255118083378973416085451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680314889010595776227869 255118083378973416085451)
              ·
                refine ⟨382677125068460124128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255118083378973416085451 382677125068460124128177)
                ·
                  refine ⟨287007843801345093096133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382677125068460124128177 287007843801345093096133)
                  ·
                    refine ⟨53813970712752204955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287007843801345093096133 53813970712752204955525)
                    ·
                      rfl

theorem cell23_314407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_314407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314407 prefixEnd_314407 := by exact prefixLift 314407
  have htrace : WordTrace (prefixWord ++ tailWord_314407) baseStart_314407 baseEnd_314407 := by
    simpa [prefixWord, tailWord_314407, baseEnd_314407] using wordTrace_append hprefix tailTrace_314407
  have hstable : (prefixWord ++ tailWord_314407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314407).length < 2 ^ (prefixWord ++ tailWord_314407).sum := by decide
  have hdescent : baseEnd_314407 < baseStart_314407 := by decide
  rcases family_descends (prefixWord ++ tailWord_314407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314410 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_314410 : Nat := 118140960795 + 314410 * 2 ^ 59
def prefixEnd_314410 : Nat := 4983230072969 + 3 ^ 40 * 314410 * 2
def baseEnd_314410 : Nat := 161443452580220103129061

theorem tailTrace_314410 : CollatzResearch.WordTrace tailWord_314410 prefixEnd_314410 161443452580220103129061 := by
  unfold tailWord_314410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866868697738435449519171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7644983193969161198717789 2866868697738435449519171)
  ·
    refine ⟨4300303046607653174278757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866868697738435449519171 4300303046607653174278757)
    ·
      refine ⟨806306821238934970177267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4300303046607653174278757 806306821238934970177267)
      ·
        refine ⟨1209460231858402455265901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 806306821238934970177267 1209460231858402455265901)
        ·
          refine ⟨453547586946900920724713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1209460231858402455265901 453547586946900920724713)
          ·
            refine ⟨340160690210175690543535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453547586946900920724713 340160690210175690543535)
            ·
              refine ⟨510241035315263535815303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340160690210175690543535 510241035315263535815303)
              ·
                refine ⟨765361552972895303722955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510241035315263535815303 765361552972895303722955)
                ·
                  refine ⟨1148042329459342955584433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 765361552972895303722955 1148042329459342955584433)
                  ·
                    refine ⟨861031747094507216688325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1148042329459342955584433 861031747094507216688325)
                    ·
                      refine ⟨161443452580220103129061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 861031747094507216688325 161443452580220103129061)
                      ·
                        rfl

theorem cell23_314410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_314410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314410 prefixEnd_314410 := by exact prefixLift 314410
  have htrace : WordTrace (prefixWord ++ tailWord_314410) baseStart_314410 baseEnd_314410 := by
    simpa [prefixWord, tailWord_314410, baseEnd_314410] using wordTrace_append hprefix tailTrace_314410
  have hstable : (prefixWord ++ tailWord_314410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314410).length < 2 ^ (prefixWord ++ tailWord_314410).sum := by decide
  have hdescent : baseEnd_314410 < baseStart_314410 := by decide
  rcases family_descends (prefixWord ++ tailWord_314410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314420 : List Nat := [2, 5, 1, 2, 1, 3, 2, 7]
def baseStart_314420 : Nat := 118140960795 + 314420 * 2 ^ 59
def prefixEnd_314420 : Nat := 4983230072969 + 3 ^ 40 * 314420 * 2
def baseEnd_314420 : Nat := 5979577310620928296445

theorem tailTrace_314420 : CollatzResearch.WordTrace tailWord_314420 prefixEnd_314420 5979577310620928296445 := by
  unfold tailWord_314420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733919760458756752970357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7645226347278342337293809 5733919760458756752970357)
  ·
    refine ⟨537554977543008445590971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5733919760458756752970357 537554977543008445590971)
    ·
      refine ⟨806332466314512668386457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537554977543008445590971 806332466314512668386457)
      ·
        refine ⟨604749349735884501289843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806332466314512668386457 604749349735884501289843)
        ·
          refine ⟨907124024603826751934765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604749349735884501289843 907124024603826751934765)
          ·
            refine ⟨340171509226435031975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 907124024603826751934765 340171509226435031975537)
            ·
              refine ⟨255128631919826273981653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340171509226435031975537 255128631919826273981653)
              ·
                refine ⟨5979577310620928296445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255128631919826273981653 5979577310620928296445)
                ·
                  rfl

theorem cell23_314420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 7].length) (baseStart_314420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314420 prefixEnd_314420 := by exact prefixLift 314420
  have htrace : WordTrace (prefixWord ++ tailWord_314420) baseStart_314420 baseEnd_314420 := by
    simpa [prefixWord, tailWord_314420, baseEnd_314420] using wordTrace_append hprefix tailTrace_314420
  have hstable : (prefixWord ++ tailWord_314420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314420).length < 2 ^ (prefixWord ++ tailWord_314420).sum := by decide
  have hdescent : baseEnd_314420 < baseStart_314420 := by decide
  rcases family_descends (prefixWord ++ tailWord_314420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314430 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_314430 : Nat := 118140960795 + 314430 * 2 ^ 59
def prefixEnd_314430 : Nat := 4983230072969 + 3 ^ 40 * 314430 * 2
def baseEnd_314430 : Nat := 161453722193310024878969

theorem tailTrace_314430 : CollatzResearch.WordTrace tailWord_314430 prefixEnd_314430 161453722193310024878969 := by
  unfold tailWord_314430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433525531360160651725593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7645469500587523475869829 1433525531360160651725593)
  ·
    refine ⟨1075144148520120488794195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1433525531360160651725593 1075144148520120488794195)
    ·
      refine ⟨1612716222780180733191293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075144148520120488794195 1612716222780180733191293)
      ·
        refine ⟨604768583542567774946735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1612716222780180733191293 604768583542567774946735)
        ·
          refine ⟨907152875313851662420103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604768583542567774946735 907152875313851662420103)
          ·
            refine ⟨1360729312970777493630155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907152875313851662420103 1360729312970777493630155)
            ·
              refine ⟨2041093969456166240445233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360729312970777493630155 2041093969456166240445233)
              ·
                refine ⟨1530820477092124680333925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041093969456166240445233 1530820477092124680333925)
                ·
                  refine ⟨287028839454773377562611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1530820477092124680333925 287028839454773377562611)
                  ·
                    refine ⟨430543259182160066343917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287028839454773377562611 430543259182160066343917)
                    ·
                      refine ⟨161453722193310024878969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430543259182160066343917 161453722193310024878969)
                      ·
                        rfl

theorem cell23_314430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_314430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314430 prefixEnd_314430 := by exact prefixLift 314430
  have htrace : WordTrace (prefixWord ++ tailWord_314430) baseStart_314430 baseEnd_314430 := by
    simpa [prefixWord, tailWord_314430, baseEnd_314430] using wordTrace_append hprefix tailTrace_314430
  have hstable : (prefixWord ++ tailWord_314430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314430).length < 2 ^ (prefixWord ++ tailWord_314430).sum := by decide
  have hdescent : baseEnd_314430 < baseStart_314430 := by decide
  rcases family_descends (prefixWord ++ tailWord_314430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314456 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_314456 : Nat := 118140960795 + 314456 * 2 ^ 59
def prefixEnd_314456 : Nat := 4983230072969 + 3 ^ 40 * 314456 * 2
def baseEnd_314456 : Nat := 161467072690326923153849

theorem tailTrace_314456 : CollatzResearch.WordTrace tailWord_314456 prefixEnd_314456 161467072690326923153849 := by
  unfold tailWord_314456
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734576274393545827125611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7646101699191394436167481 5734576274393545827125611)
  ·
    refine ⟨8601864411590318740688417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734576274393545827125611 8601864411590318740688417)
    ·
      refine ⟨6451398308692739055516313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8601864411590318740688417 6451398308692739055516313)
      ·
        refine ⟨4838548731519554291637235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6451398308692739055516313 4838548731519554291637235)
        ·
          refine ⟨7257823097279331437455853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838548731519554291637235 7257823097279331437455853)
          ·
            refine ⟨2721683661479749289045945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7257823097279331437455853 2721683661479749289045945)
            ·
              refine ⟨2041262746109811966784459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721683661479749289045945 2041262746109811966784459)
              ·
                refine ⟨3061894119164717950176689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041262746109811966784459 3061894119164717950176689)
                ·
                  refine ⟨2296420589373538462632517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061894119164717950176689 2296420589373538462632517)
                  ·
                    refine ⟨430578860507538461743597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296420589373538462632517 430578860507538461743597)
                    ·
                      refine ⟨161467072690326923153849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430578860507538461743597 161467072690326923153849)
                      ·
                        rfl

theorem cell23_314456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_314456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314456 prefixEnd_314456 := by exact prefixLift 314456
  have htrace : WordTrace (prefixWord ++ tailWord_314456) baseStart_314456 baseEnd_314456 := by
    simpa [prefixWord, tailWord_314456, baseEnd_314456] using wordTrace_append hprefix tailTrace_314456
  have hstable : (prefixWord ++ tailWord_314456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314456).length < 2 ^ (prefixWord ++ tailWord_314456).sum := by decide
  have hdescent : baseEnd_314456 < baseStart_314456 := by decide
  rcases family_descends (prefixWord ++ tailWord_314456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314493 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 5]
def baseStart_314493 : Nat := 118140960795 + 314493 * 2 ^ 59
def prefixEnd_314493 : Nat := 4983230072969 + 3 ^ 40 * 314493 * 2
def baseEnd_314493 : Nat := 17942896830504808710131

theorem tailTrace_314493 : CollatzResearch.WordTrace tailWord_314493 prefixEnd_314493 17942896830504808710131 := by
  unfold tailWord_314493
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470502049653046973348133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7647001366435364648898755 11470502049653046973348133)
  ·
    refine ⟨2150719134309946307502775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11470502049653046973348133 2150719134309946307502775)
    ·
      refine ⟨3226078701464919461254163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150719134309946307502775 3226078701464919461254163)
      ·
        refine ⟨4839118052197379191881245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226078701464919461254163 4839118052197379191881245)
        ·
          refine ⟨1814669269574017196955467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4839118052197379191881245 1814669269574017196955467)
          ·
            refine ⟨2722003904361025795433201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814669269574017196955467 2722003904361025795433201)
            ·
              refine ⟨2041502928270769346574901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722003904361025795433201 2041502928270769346574901)
              ·
                refine ⟨191390899525384626241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2041502928270769346574901 191390899525384626241397)
                ·
                  refine ⟨17942896830504808710131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191390899525384626241397 17942896830504808710131)
                  ·
                    rfl

theorem cell23_314493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_314493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314493 prefixEnd_314493 := by exact prefixLift 314493
  have htrace : WordTrace (prefixWord ++ tailWord_314493) baseStart_314493 baseEnd_314493 := by
    simpa [prefixWord, tailWord_314493, baseEnd_314493] using wordTrace_append hprefix tailTrace_314493
  have hstable : (prefixWord ++ tailWord_314493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314493).length < 2 ^ (prefixWord ++ tailWord_314493).sum := by decide
  have hdescent : baseEnd_314493 < baseStart_314493 := by decide
  rcases family_descends (prefixWord ++ tailWord_314493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314504 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_314504 : Nat := 118140960795 + 314504 * 2 ^ 59
def prefixEnd_314504 : Nat := 4983230072969 + 3 ^ 40 * 314504 * 2
def baseEnd_314504 : Nat := 161491719761742735353629

theorem tailTrace_314504 : CollatzResearch.WordTrace tailWord_314504 prefixEnd_314504 161491719761742735353629 := by
  unfold tailWord_314504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735451626306597925999283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7647268835075463901332377 5735451626306597925999283)
  ·
    refine ⟨8603177439459896888998925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5735451626306597925999283 8603177439459896888998925)
    ·
      refine ⟨3226191539797461333374597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8603177439459896888998925 3226191539797461333374597)
      ·
        refine ⟨604910913712024000007737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3226191539797461333374597 604910913712024000007737)
        ·
          refine ⟨453683185284018000005803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604910913712024000007737 453683185284018000005803)
          ·
            refine ⟨680524777926027000008705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453683185284018000005803 680524777926027000008705)
            ·
              refine ⟨510393583444520250006529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680524777926027000008705 510393583444520250006529)
              ·
                refine ⟨382795187583390187504897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510393583444520250006529 382795187583390187504897)
                ·
                  refine ⟨287096390687542640628673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382795187583390187504897 287096390687542640628673)
                  ·
                    refine ⟨215322293015656980471505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287096390687542640628673 215322293015656980471505)
                    ·
                      refine ⟨161491719761742735353629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215322293015656980471505 161491719761742735353629)
                      ·
                        rfl

theorem cell23_314504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_314504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314504 prefixEnd_314504 := by exact prefixLift 314504
  have htrace : WordTrace (prefixWord ++ tailWord_314504) baseStart_314504 baseEnd_314504 := by
    simpa [prefixWord, tailWord_314504, baseEnd_314504] using wordTrace_append hprefix tailTrace_314504
  have hstable : (prefixWord ++ tailWord_314504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314504).length < 2 ^ (prefixWord ++ tailWord_314504).sum := by decide
  have hdescent : baseEnd_314504 < baseStart_314504 := by decide
  rcases family_descends (prefixWord ++ tailWord_314504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314510 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_314510 : Nat := 118140960795 + 314510 * 2 ^ 59
def prefixEnd_314510 : Nat := 4983230072969 + 3 ^ 40 * 314510 * 2
def baseEnd_314510 : Nat := 17943866738407745764289

theorem tailTrace_314510 : CollatzResearch.WordTrace tailWord_314510 prefixEnd_314510 17943866738407745764289 := by
  unfold tailWord_314510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433890261323932359589623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7647414727060972584477989 1433890261323932359589623)
  ·
    refine ⟨2150835391985898539384435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433890261323932359589623 2150835391985898539384435)
    ·
      refine ⟨3226253087978847809076653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150835391985898539384435 3226253087978847809076653)
      ·
        refine ⟨1209844907992067928403745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3226253087978847809076653 1209844907992067928403745)
        ·
          refine ⟨907383680994050946302809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209844907992067928403745 907383680994050946302809)
          ·
            refine ⟨680537760745538209727107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907383680994050946302809 680537760745538209727107)
            ·
              refine ⟨1020806641118307314590661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680537760745538209727107 1020806641118307314590661)
              ·
                refine ⟨191401245209682621485749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1020806641118307314590661 191401245209682621485749)
                ·
                  refine ⟨17943866738407745764289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191401245209682621485749 17943866738407745764289)
                  ·
                    rfl

theorem cell23_314510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_314510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314510 prefixEnd_314510 := by exact prefixLift 314510
  have htrace : WordTrace (prefixWord ++ tailWord_314510) baseStart_314510 baseEnd_314510 := by
    simpa [prefixWord, tailWord_314510, baseEnd_314510] using wordTrace_append hprefix tailTrace_314510
  have hstable : (prefixWord ++ tailWord_314510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314510).length < 2 ^ (prefixWord ++ tailWord_314510).sum := by decide
  have hdescent : baseEnd_314510 < baseStart_314510 := by decide
  rcases family_descends (prefixWord ++ tailWord_314510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314543 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_314543 : Nat := 118140960795 + 314543 * 2 ^ 59
def prefixEnd_314543 : Nat := 4983230072969 + 3 ^ 40 * 314543 * 2
def baseEnd_314543 : Nat := 161511745507268082765949

theorem tailTrace_314543 : CollatzResearch.WordTrace tailWord_314543 prefixEnd_314543 161511745507268082765949 := by
  unfold tailWord_314543
  simp only [CollatzResearch.WordTrace]
  refine ⟨11472325699471905512668283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7648217132981270341778855 11472325699471905512668283)
  ·
    refine ⟨17208488549207858269002425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11472325699471905512668283 17208488549207858269002425)
    ·
      refine ⟨12906366411905893701751819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17208488549207858269002425 12906366411905893701751819)
      ·
        refine ⟨19359549617858840552627729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12906366411905893701751819 19359549617858840552627729)
        ·
          refine ⟨14519662213394130414470797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19359549617858840552627729 14519662213394130414470797)
          ·
            refine ⟨5444873330022798905426549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14519662213394130414470797 5444873330022798905426549)
            ·
              refine ⟨510456874689637397383739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5444873330022798905426549 510456874689637397383739)
              ·
                refine ⟨765685312034456096075609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510456874689637397383739 765685312034456096075609)
                ·
                  refine ⟨574263984025842072056707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765685312034456096075609 574263984025842072056707)
                  ·
                    refine ⟨861395976038763108085061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574263984025842072056707 861395976038763108085061)
                    ·
                      refine ⟨161511745507268082765949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 861395976038763108085061 161511745507268082765949)
                      ·
                        rfl

theorem cell23_314543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_314543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314543 prefixEnd_314543 := by exact prefixLift 314543
  have htrace : WordTrace (prefixWord ++ tailWord_314543) baseStart_314543 baseEnd_314543 := by
    simpa [prefixWord, tailWord_314543, baseEnd_314543] using wordTrace_append hprefix tailTrace_314543
  have hstable : (prefixWord ++ tailWord_314543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314543).length < 2 ^ (prefixWord ++ tailWord_314543).sum := by decide
  have hdescent : baseEnd_314543 < baseStart_314543 := by decide
  rcases family_descends (prefixWord ++ tailWord_314543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314570 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_314570 : Nat := 118140960795 + 314570 * 2 ^ 59
def prefixEnd_314570 : Nat := 4983230072969 + 3 ^ 40 * 314570 * 2
def baseEnd_314570 : Nat := 53841869828313159042775

theorem tailTrace_314570 : CollatzResearch.WordTrace tailWord_314570 prefixEnd_314570 53841869828313159042775 := by
  unfold tailWord_314570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868327617593522280975291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7648873646916059415934109 2868327617593522280975291)
  ·
    refine ⟨4302491426390283421462937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2868327617593522280975291 4302491426390283421462937)
    ·
      refine ⟨3226868569792712566097203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4302491426390283421462937 3226868569792712566097203)
      ·
        refine ⟨4840302854689068849145805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226868569792712566097203 4840302854689068849145805)
        ·
          refine ⟨1815113570508400818429677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4840302854689068849145805 1815113570508400818429677)
          ·
            refine ⟨680667588940650306911129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1815113570508400818429677 680667588940650306911129)
            ·
              refine ⟨510500691705487730183347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680667588940650306911129 510500691705487730183347)
              ·
                refine ⟨765751037558231595275021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510500691705487730183347 765751037558231595275021)
                ·
                  refine ⟨287156639084336848228133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765751037558231595275021 287156639084336848228133)
                  ·
                    refine ⟨53841869828313159042775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287156639084336848228133 53841869828313159042775)
                    ·
                      rfl

theorem cell23_314570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_314570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314570 prefixEnd_314570 := by exact prefixLift 314570
  have htrace : WordTrace (prefixWord ++ tailWord_314570) baseStart_314570 baseEnd_314570 := by
    simpa [prefixWord, tailWord_314570, baseEnd_314570] using wordTrace_append hprefix tailTrace_314570
  have hstable : (prefixWord ++ tailWord_314570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314570).length < 2 ^ (prefixWord ++ tailWord_314570).sum := by decide
  have hdescent : baseEnd_314570 < baseStart_314570 := by decide
  rcases family_descends (prefixWord ++ tailWord_314570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_314586 : Nat := 118140960795 + 314586 * 2 ^ 59
def prefixEnd_314586 : Nat := 4983230072969 + 3 ^ 40 * 314586 * 2
def baseEnd_314586 : Nat := 161533825175411414528251

theorem tailTrace_314586 : CollatzResearch.WordTrace tailWord_314586 prefixEnd_314586 161533825175411414528251 := by
  unfold tailWord_314586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2868473509579030964120903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7649262692210749237655741 2868473509579030964120903)
  ·
    refine ⟨4302710264368546446181355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2868473509579030964120903 4302710264368546446181355)
    ·
      refine ⟨6454065396552819669272033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302710264368546446181355 6454065396552819669272033)
      ·
        refine ⟨4840549047414614751954025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6454065396552819669272033 4840549047414614751954025)
        ·
          refine ⟨3630411785560961063965519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4840549047414614751954025 3630411785560961063965519)
          ·
            refine ⟨5445617678341441595948279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630411785560961063965519 5445617678341441595948279)
            ·
              refine ⟨8168426517512162393922419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445617678341441595948279 8168426517512162393922419)
              ·
                refine ⟨12252639776268243590883629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168426517512162393922419 12252639776268243590883629)
                ·
                  refine ⟨4594739916100591346581361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12252639776268243590883629 4594739916100591346581361)
                  ·
                    refine ⟨3446054937075443509936021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4594739916100591346581361 3446054937075443509936021)
                    ·
                      refine ⟨161533825175411414528251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3446054937075443509936021 161533825175411414528251)
                      ·
                        rfl

theorem cell23_314586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_314586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314586 prefixEnd_314586 := by exact prefixLift 314586
  have htrace : WordTrace (prefixWord ++ tailWord_314586) baseStart_314586 baseEnd_314586 := by
    simpa [prefixWord, tailWord_314586, baseEnd_314586] using wordTrace_append hprefix tailTrace_314586
  have hstable : (prefixWord ++ tailWord_314586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314586).length < 2 ^ (prefixWord ++ tailWord_314586).sum := by decide
  have hdescent : baseEnd_314586 < baseStart_314586 := by decide
  rcases family_descends (prefixWord ++ tailWord_314586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314627 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 3]
def baseStart_314627 : Nat := 118140960795 + 314627 * 2 ^ 59
def prefixEnd_314627 : Nat := 4983230072969 + 3 ^ 40 * 314627 * 2
def baseEnd_314627 : Nat := 161554877882245754115563

theorem tailTrace_314627 : CollatzResearch.WordTrace tailWord_314627 prefixEnd_314627 161554877882245754115563 := by
  unfold tailWord_314627
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475389431167587858726135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650259620778391905817423 11475389431167587858726135)
  ·
    refine ⟨17213084146751381788089203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475389431167587858726135 17213084146751381788089203)
    ·
      refine ⟨25819626220127072682133805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17213084146751381788089203 25819626220127072682133805)
      ·
        refine ⟨9682359832547652255800177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25819626220127072682133805 9682359832547652255800177)
        ·
          refine ⟨7261769874410739191850133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9682359832547652255800177 7261769874410739191850133)
          ·
            refine ⟨340395462863003399617975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7261769874410739191850133 340395462863003399617975)
            ·
              refine ⟨510593194294505099426963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340395462863003399617975 510593194294505099426963)
              ·
                refine ⟨765889791441757649140445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510593194294505099426963 765889791441757649140445)
                ·
                  refine ⟨287208671790659118427667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 765889791441757649140445 287208671790659118427667)
                  ·
                    refine ⟨430813007685988677641501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287208671790659118427667 430813007685988677641501)
                    ·
                      refine ⟨161554877882245754115563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430813007685988677641501 161554877882245754115563)
                      ·
                        rfl

theorem cell23_314627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_314627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314627 prefixEnd_314627 := by exact prefixLift 314627
  have htrace : WordTrace (prefixWord ++ tailWord_314627) baseStart_314627 baseEnd_314627 := by
    simpa [prefixWord, tailWord_314627, baseEnd_314627] using wordTrace_append hprefix tailTrace_314627
  have hstable : (prefixWord ++ tailWord_314627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314627).length < 2 ^ (prefixWord ++ tailWord_314627).sum := by decide
  have hdescent : baseEnd_314627 < baseStart_314627 := by decide
  rcases family_descends (prefixWord ++ tailWord_314627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314633 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_314633 : Nat := 118140960795 + 314633 * 2 ^ 59
def prefixEnd_314633 : Nat := 4983230072969 + 3 ^ 40 * 314633 * 2
def baseEnd_314633 : Nat := 161557958766172730640535

theorem tailTrace_314633 : CollatzResearch.WordTrace tailWord_314633 prefixEnd_314633 161557958766172730640535 := by
  unfold tailWord_314633
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475608269145850883444553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650405512763900588963035 11475608269145850883444553)
  ·
    refine ⟨8606706201859388162583415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11475608269145850883444553 8606706201859388162583415)
    ·
      refine ⟨12910059302789082243875123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606706201859388162583415 12910059302789082243875123)
      ·
        refine ⟨19365088954183623365812685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12910059302789082243875123 19365088954183623365812685)
        ·
          refine ⟨7261908357818858762179757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19365088954183623365812685 7261908357818858762179757)
          ·
            refine ⟨2723215634182072035817409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7261908357818858762179757 2723215634182072035817409)
            ·
              refine ⟨2042411725636554026863057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723215634182072035817409 2042411725636554026863057)
              ·
                refine ⟨1531808794227415520147293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042411725636554026863057 1531808794227415520147293)
                ·
                  refine ⟨574428297835280820055235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531808794227415520147293 574428297835280820055235)
                  ·
                    refine ⟨861642446752921230082853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574428297835280820055235 861642446752921230082853)
                    ·
                      refine ⟨161557958766172730640535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 861642446752921230082853 161557958766172730640535)
                      ·
                        rfl

theorem cell23_314633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_314633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314633 prefixEnd_314633 := by exact prefixLift 314633
  have htrace : WordTrace (prefixWord ++ tailWord_314633) baseStart_314633 baseEnd_314633 := by
    simpa [prefixWord, tailWord_314633, baseEnd_314633] using wordTrace_append hprefix tailTrace_314633
  have hstable : (prefixWord ++ tailWord_314633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314633).length < 2 ^ (prefixWord ++ tailWord_314633).sum := by decide
  have hdescent : baseEnd_314633 < baseStart_314633 := by decide
  rcases family_descends (prefixWord ++ tailWord_314633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314650 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_314650 : Nat := 118140960795 + 314650 * 2 ^ 59
def prefixEnd_314650 : Nat := 4983230072969 + 3 ^ 40 * 314650 * 2
def baseEnd_314650 : Nat := 161566687937299164127957

theorem tailTrace_314650 : CollatzResearch.WordTrace tailWord_314650 prefixEnd_314650 161566687937299164127957 := by
  unfold tailWord_314650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869057077521065696703351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7650818873389508524542269 2869057077521065696703351)
  ·
    refine ⟨4303585616281598545055027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2869057077521065696703351 4303585616281598545055027)
    ·
      refine ⟨6455378424422397817582541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303585616281598545055027 6455378424422397817582541)
      ·
        refine ⟨2420766909158399181593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6455378424422397817582541 2420766909158399181593453)
        ·
          refine ⟨907787590934399693097545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2420766909158399181593453 907787590934399693097545)
          ·
            refine ⟨680840693200799769823159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907787590934399693097545 680840693200799769823159)
            ·
              refine ⟨1021261039801199654734739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680840693200799769823159 1021261039801199654734739)
              ·
                refine ⟨1531891559701799482102109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021261039801199654734739 1531891559701799482102109)
                ·
                  refine ⟨574459334888174805788291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1531891559701799482102109 574459334888174805788291)
                  ·
                    refine ⟨861689002332262208682437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574459334888174805788291 861689002332262208682437)
                    ·
                      refine ⟨161566687937299164127957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 861689002332262208682437 161566687937299164127957)
                      ·
                        rfl

theorem cell23_314650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_314650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314650 prefixEnd_314650 := by exact prefixLift 314650
  have htrace : WordTrace (prefixWord ++ tailWord_314650) baseStart_314650 baseEnd_314650 := by
    simpa [prefixWord, tailWord_314650, baseEnd_314650] using wordTrace_append hprefix tailTrace_314650
  have hstable : (prefixWord ++ tailWord_314650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314650).length < 2 ^ (prefixWord ++ tailWord_314650).sum := by decide
  have hdescent : baseEnd_314650 < baseStart_314650 := by decide
  rcases family_descends (prefixWord ++ tailWord_314650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314677 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_314677 : Nat := 118140960795 + 314677 * 2 ^ 59
def prefixEnd_314677 : Nat := 4983230072969 + 3 ^ 40 * 314677 * 2
def baseEnd_314677 : Nat := 53860183971656852830111

theorem tailTrace_314677 : CollatzResearch.WordTrace tailWord_314677 prefixEnd_314677 53860183971656852830111 := by
  unfold tailWord_314677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477213080986446398046285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7651475387324297598697523 11477213080986446398046285)
  ·
    refine ⟨4303954905369917399267357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11477213080986446398046285 4303954905369917399267357)
    ·
      refine ⟨1613983089513719024725259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4303954905369917399267357 1613983089513719024725259)
      ·
        refine ⟨2420974634270578537087889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613983089513719024725259 2420974634270578537087889)
        ·
          refine ⟨1815730975702933902815917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2420974634270578537087889 1815730975702933902815917)
          ·
            refine ⟨680899115888600213555969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1815730975702933902815917 680899115888600213555969)
            ·
              refine ⟨510674336916450160166977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680899115888600213555969 510674336916450160166977)
              ·
                refine ⟨383005752687337620125233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 510674336916450160166977 383005752687337620125233)
                ·
                  refine ⟨287254314515503215093925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383005752687337620125233 287254314515503215093925)
                  ·
                    refine ⟨53860183971656852830111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287254314515503215093925 53860183971656852830111)
                    ·
                      rfl

theorem cell23_314677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_314677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314677 prefixEnd_314677 := by exact prefixLift 314677
  have htrace : WordTrace (prefixWord ++ tailWord_314677) baseStart_314677 baseEnd_314677 := by
    simpa [prefixWord, tailWord_314677, baseEnd_314677] using wordTrace_append hprefix tailTrace_314677
  have hstable : (prefixWord ++ tailWord_314677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314677).length < 2 ^ (prefixWord ++ tailWord_314677).sum := by decide
  have hdescent : baseEnd_314677 < baseStart_314677 := by decide
  rcases family_descends (prefixWord ++ tailWord_314677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314678 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_314678 : Nat := 118140960795 + 314678 * 2 ^ 59
def prefixEnd_314678 : Nat := 4983230072969 + 3 ^ 40 * 314678 * 2
def baseEnd_314678 : Nat := 161581065395625054577829

theorem tailTrace_314678 : CollatzResearch.WordTrace tailWord_314678 prefixEnd_314678 161581065395625054577829 := by
  unfold tailWord_314678
  simp only [CollatzResearch.WordTrace]
  refine ⟨717328097123926473052043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7651499702655215712555125 717328097123926473052043)
  ·
    refine ⟨1075992145685889709578065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717328097123926473052043 1075992145685889709578065)
    ·
      refine ⟨806994109264417282183549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075992145685889709578065 806994109264417282183549)
      ·
        refine ⟨302622790974156480818831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 806994109264417282183549 302622790974156480818831)
        ·
          refine ⟨453934186461234721228247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302622790974156480818831 453934186461234721228247)
          ·
            refine ⟨680901279691852081842371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453934186461234721228247 680901279691852081842371)
            ·
              refine ⟨1021351919537778122763557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680901279691852081842371 1021351919537778122763557)
              ·
                refine ⟨191503484913333398018167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1021351919537778122763557 191503484913333398018167)
                ·
                  refine ⟨287255227370000097027251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191503484913333398018167 287255227370000097027251)
                  ·
                    refine ⟨430882841055000145540877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287255227370000097027251 430882841055000145540877)
                    ·
                      refine ⟨161581065395625054577829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430882841055000145540877 161581065395625054577829)
                      ·
                        rfl

theorem cell23_314678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_314678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314678 prefixEnd_314678 := by exact prefixLift 314678
  have htrace : WordTrace (prefixWord ++ tailWord_314678) baseStart_314678 baseEnd_314678 := by
    simpa [prefixWord, tailWord_314678, baseEnd_314678] using wordTrace_append hprefix tailTrace_314678
  have hstable : (prefixWord ++ tailWord_314678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314678).length < 2 ^ (prefixWord ++ tailWord_314678).sum := by decide
  have hdescent : baseEnd_314678 < baseStart_314678 := by decide
  rcases family_descends (prefixWord ++ tailWord_314678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314700 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_314700 : Nat := 118140960795 + 314700 * 2 ^ 59
def prefixEnd_314700 : Nat := 4983230072969 + 3 ^ 40 * 314700 * 2
def baseEnd_314700 : Nat := 161592361970023968502727

theorem tailTrace_314700 : CollatzResearch.WordTrace tailWord_314700 prefixEnd_314700 161592361970023968502727 := by
  unfold tailWord_314700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739025979951560663066777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7652034639935414217422369 5739025979951560663066777)
  ·
    refine ⟨4304269484963670497300083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5739025979951560663066777 4304269484963670497300083)
    ·
      refine ⟨6456404227445505745950125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4304269484963670497300083 6456404227445505745950125)
      ·
        refine ⟨2421151585292064654731297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6456404227445505745950125 2421151585292064654731297)
        ·
          refine ⟨1815863688969048491048473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2421151585292064654731297 1815863688969048491048473)
          ·
            refine ⟨1361897766726786368286355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1815863688969048491048473 1361897766726786368286355)
            ·
              refine ⟨2042846650090179552429533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361897766726786368286355 2042846650090179552429533)
              ·
                refine ⟨766067493783817332161075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2042846650090179552429533 766067493783817332161075)
                ·
                  refine ⟨1149101240675725998241613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766067493783817332161075 1149101240675725998241613)
                  ·
                    refine ⟨430912965253397249340605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1149101240675725998241613 430912965253397249340605)
                    ·
                      refine ⟨161592361970023968502727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 430912965253397249340605 161592361970023968502727)
                      ·
                        rfl

theorem cell23_314700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_314700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314700 prefixEnd_314700 := by exact prefixLift 314700
  have htrace : WordTrace (prefixWord ++ tailWord_314700) baseStart_314700 baseEnd_314700 := by
    simpa [prefixWord, tailWord_314700, baseEnd_314700] using wordTrace_append hprefix tailTrace_314700
  have hstable : (prefixWord ++ tailWord_314700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314700).length < 2 ^ (prefixWord ++ tailWord_314700).sum := by decide
  have hdescent : baseEnd_314700 < baseStart_314700 := by decide
  rcases family_descends (prefixWord ++ tailWord_314700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314757 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 1, 4, 2]
def baseStart_314757 : Nat := 118140960795 + 314757 * 2 ^ 59
def prefixEnd_314757 : Nat := 4983230072969 + 3 ^ 40 * 314757 * 2
def baseEnd_314757 : Nat := 161621630367330245489965

theorem tailTrace_314757 : CollatzResearch.WordTrace tailWord_314757 prefixEnd_314757 161621630367330245489965 := by
  unfold tailWord_314757
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480130920696620060958525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7653420613797746707305683 11480130920696620060958525)
  ·
    refine ⟨4305049095261232522859447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11480130920696620060958525 4305049095261232522859447)
    ·
      refine ⟨6457573642891848784289171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305049095261232522859447 6457573642891848784289171)
      ·
        refine ⟨9686360464337773176433757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457573642891848784289171 9686360464337773176433757)
        ·
          refine ⟨3632385174126664941162659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9686360464337773176433757 3632385174126664941162659)
          ·
            refine ⟨5448577761189997411743989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632385174126664941162659 5448577761189997411743989)
            ·
              refine ⟨510804165111562257350999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5448577761189997411743989 510804165111562257350999)
              ·
                refine ⟨766206247667343386026499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510804165111562257350999 766206247667343386026499)
                ·
                  refine ⟨1149309371501015079039749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 766206247667343386026499 1149309371501015079039749)
                  ·
                    refine ⟨215495507156440327319953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149309371501015079039749 215495507156440327319953)
                    ·
                      refine ⟨161621630367330245489965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215495507156440327319953 161621630367330245489965)
                      ·
                        rfl

theorem cell23_314757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_314757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314757 prefixEnd_314757 := by exact prefixLift 314757
  have htrace : WordTrace (prefixWord ++ tailWord_314757) baseStart_314757 baseEnd_314757 := by
    simpa [prefixWord, tailWord_314757, baseEnd_314757] using wordTrace_append hprefix tailTrace_314757
  have hstable : (prefixWord ++ tailWord_314757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314757).length < 2 ^ (prefixWord ++ tailWord_314757).sum := by decide
  have hdescent : baseEnd_314757 < baseStart_314757 := by decide
  rcases family_descends (prefixWord ++ tailWord_314757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314763 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 7]
def baseStart_314763 : Nat := 118140960795 + 314763 * 2 ^ 59
def prefixEnd_314763 : Nat := 4983230072969 + 3 ^ 40 * 314763 * 2
def baseEnd_314763 : Nat := 17958301250139691334993

theorem tailTrace_314763 : CollatzResearch.WordTrace tailWord_314763 prefixEnd_314763 17958301250139691334993 := by
  unfold tailWord_314763
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480349758674883085676943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7653566505783255390451295 11480349758674883085676943)
  ·
    refine ⟨17220524638012324628515415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11480349758674883085676943 17220524638012324628515415)
    ·
      refine ⟨25830786957018486942773123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17220524638012324628515415 25830786957018486942773123)
      ·
        refine ⟨38746180435527730414159685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25830786957018486942773123 38746180435527730414159685)
        ·
          refine ⟨7264908831661449452654941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38746180435527730414159685 7264908831661449452654941)
          ·
            refine ⟨2724340811873043544745603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7264908831661449452654941 2724340811873043544745603)
            ·
              refine ⟨4086511217809565317118405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724340811873043544745603 4086511217809565317118405)
              ·
                refine ⟨766220853339293496959701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4086511217809565317118405 766220853339293496959701)
                ·
                  refine ⟨17958301250139691334993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 766220853339293496959701 17958301250139691334993)
                  ·
                    rfl

theorem cell23_314763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 7].length) (baseStart_314763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314763 prefixEnd_314763 := by exact prefixLift 314763
  have htrace : WordTrace (prefixWord ++ tailWord_314763) baseStart_314763 baseEnd_314763 := by
    simpa [prefixWord, tailWord_314763, baseEnd_314763] using wordTrace_append hprefix tailTrace_314763
  have hstable : (prefixWord ++ tailWord_314763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314763).length < 2 ^ (prefixWord ++ tailWord_314763).sum := by decide
  have hdescent : baseEnd_314763 < baseStart_314763 := by decide
  rcases family_descends (prefixWord ++ tailWord_314763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314797 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 7]
def baseStart_314797 : Nat := 118140960795 + 314797 * 2 ^ 59
def prefixEnd_314797 : Nat := 4983230072969 + 3 ^ 40 * 314797 * 2
def baseEnd_314797 : Nat := 17960241065945565443309

theorem tailTrace_314797 : CollatzResearch.WordTrace tailWord_314797 prefixEnd_314797 17960241065945565443309 := by
  unfold tailWord_314797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481589840551706892414645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7654393227034471261609763 11481589840551706892414645)
  ·
    refine ⟨1076399047551722521163873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11481589840551706892414645 1076399047551722521163873)
    ·
      refine ⟨807299285663791890872905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076399047551722521163873 807299285663791890872905)
      ·
        refine ⟨605474464247843918154679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 807299285663791890872905 605474464247843918154679)
        ·
          refine ⟨908211696371765877232019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605474464247843918154679 908211696371765877232019)
          ·
            refine ⟨1362317544557648815848029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908211696371765877232019 1362317544557648815848029)
            ·
              refine ⟨510869079209118305943011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362317544557648815848029 510869079209118305943011)
              ·
                refine ⟨766303618813677458914517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510869079209118305943011 766303618813677458914517)
                ·
                  refine ⟨17960241065945565443309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 766303618813677458914517 17960241065945565443309)
                  ·
                    rfl

theorem cell23_314797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_314797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314797 prefixEnd_314797 := by exact prefixLift 314797
  have htrace : WordTrace (prefixWord ++ tailWord_314797) baseStart_314797 baseEnd_314797 := by
    simpa [prefixWord, tailWord_314797, baseEnd_314797] using wordTrace_append hprefix tailTrace_314797
  have hstable : (prefixWord ++ tailWord_314797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314797).length < 2 ^ (prefixWord ++ tailWord_314797).sum := by decide
  have hdescent : baseEnd_314797 < baseStart_314797 := by decide
  rcases family_descends (prefixWord ++ tailWord_314797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314830 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_314830 : Nat := 118140960795 + 314830 * 2 ^ 59
def prefixEnd_314830 : Nat := 4983230072969 + 3 ^ 40 * 314830 * 2
def baseEnd_314830 : Nat := 161659114455108459877129

theorem tailTrace_314830 : CollatzResearch.WordTrace tailWord_314830 prefixEnd_314830 161659114455108459877129 := by
  unfold tailWord_314830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435349181179019191045743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7655195632954769018910629 1435349181179019191045743)
  ·
    refine ⟨2153023771768528786568615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435349181179019191045743 2153023771768528786568615)
    ·
      refine ⟨3229535657652793179852923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2153023771768528786568615 3229535657652793179852923)
      ·
        refine ⟨4844303486479189769779385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229535657652793179852923 4844303486479189769779385)
        ·
          refine ⟨3633227614859392327334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844303486479189769779385 3633227614859392327334539)
          ·
            refine ⟨5449841422289088491001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633227614859392327334539 5449841422289088491001809)
            ·
              refine ⟨4087381066716816368251357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449841422289088491001809 4087381066716816368251357)
              ·
                refine ⟨1532767900018806138094259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4087381066716816368251357 1532767900018806138094259)
                ·
                  refine ⟨2299151850028209207141389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1532767900018806138094259 2299151850028209207141389)
                  ·
                    refine ⟨862181943760578452678021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2299151850028209207141389 862181943760578452678021)
                    ·
                      refine ⟨161659114455108459877129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 862181943760578452678021 161659114455108459877129)
                      ·
                        rfl

theorem cell23_314830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_314830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314830 prefixEnd_314830 := by exact prefixLift 314830
  have htrace : WordTrace (prefixWord ++ tailWord_314830) baseStart_314830 baseEnd_314830 := by
    simpa [prefixWord, tailWord_314830, baseEnd_314830] using wordTrace_append hprefix tailTrace_314830
  have hstable : (prefixWord ++ tailWord_314830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314830).length < 2 ^ (prefixWord ++ tailWord_314830).sum := by decide
  have hdescent : baseEnd_314830 < baseStart_314830 := by decide
  rcases family_descends (prefixWord ++ tailWord_314830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314833 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_314833 : Nat := 118140960795 + 314833 * 2 ^ 59
def prefixEnd_314833 : Nat := 4983230072969 + 3 ^ 40 * 314833 * 2
def baseEnd_314833 : Nat := 161660654897071948139615

theorem tailTrace_314833 : CollatzResearch.WordTrace tailWord_314833 prefixEnd_314833 161660654897071948139615 := by
  unfold tailWord_314833
  simp only [CollatzResearch.WordTrace]
  refine ⟨11482902868421285040725153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655268578947523360483435 11482902868421285040725153)
  ·
    refine ⟨8612177151315963780543865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11482902868421285040725153 8612177151315963780543865)
    ·
      refine ⟨6459132863486972835407899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8612177151315963780543865 6459132863486972835407899)
      ·
        refine ⟨9688699295230459253111849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6459132863486972835407899 9688699295230459253111849)
        ·
          refine ⟨7266524471422844439833887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9688699295230459253111849 7266524471422844439833887)
          ·
            refine ⟨10899786707134266659750831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7266524471422844439833887 10899786707134266659750831)
            ·
              refine ⟨16349680060701399989626247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10899786707134266659750831 16349680060701399989626247)
              ·
                refine ⟨24524520091052099984439371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16349680060701399989626247 24524520091052099984439371)
                ·
                  refine ⟨36786780136578149976659057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24524520091052099984439371 36786780136578149976659057)
                  ·
                    refine ⟨27590085102433612482494293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36786780136578149976659057 27590085102433612482494293)
                    ·
                      refine ⟨161660654897071948139615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 27590085102433612482494293 161660654897071948139615)
                      ·
                        rfl

theorem cell23_314833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_314833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314833 prefixEnd_314833 := by exact prefixLift 314833
  have htrace : WordTrace (prefixWord ++ tailWord_314833) baseStart_314833 baseEnd_314833 := by
    simpa [prefixWord, tailWord_314833, baseEnd_314833] using wordTrace_append hprefix tailTrace_314833
  have hstable : (prefixWord ++ tailWord_314833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314833).length < 2 ^ (prefixWord ++ tailWord_314833).sum := by decide
  have hdescent : baseEnd_314833 < baseStart_314833 := by decide
  rcases family_descends (prefixWord ++ tailWord_314833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_314843 : Nat := 118140960795 + 314843 * 2 ^ 59
def prefixEnd_314843 : Nat := 4983230072969 + 3 ^ 40 * 314843 * 2
def baseEnd_314843 : Nat := 161665789703616909014569

theorem tailTrace_314843 : CollatzResearch.WordTrace tailWord_314843 prefixEnd_314843 161665789703616909014569 := by
  unfold tailWord_314843
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483267598385056748589183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655511732256704499059455 11483267598385056748589183)
  ·
    refine ⟨17224901397577585122883775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11483267598385056748589183 17224901397577585122883775)
    ·
      refine ⟨25837352096366377684325663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17224901397577585122883775 25837352096366377684325663)
      ·
        refine ⟨38756028144549566526488495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25837352096366377684325663 38756028144549566526488495)
        ·
          refine ⟨58134042216824349789732743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38756028144549566526488495 58134042216824349789732743)
          ·
            refine ⟨87201063325236524684599115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58134042216824349789732743 87201063325236524684599115)
            ·
              refine ⟨130801594987854787026898673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87201063325236524684599115 130801594987854787026898673)
              ·
                refine ⟨98101196240891090270174005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130801594987854787026898673 98101196240891090270174005)
                ·
                  refine ⟨9196987147583539712828813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98101196240891090270174005 9196987147583539712828813)
                  ·
                    refine ⟨3448870180343827392310805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9196987147583539712828813 3448870180343827392310805)
                    ·
                      refine ⟨161665789703616909014569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3448870180343827392310805 161665789703616909014569)
                      ·
                        rfl

theorem cell23_314843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_314843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314843 prefixEnd_314843 := by exact prefixLift 314843
  have htrace : WordTrace (prefixWord ++ tailWord_314843) baseStart_314843 baseEnd_314843 := by
    simpa [prefixWord, tailWord_314843, baseEnd_314843] using wordTrace_append hprefix tailTrace_314843
  have hstable : (prefixWord ++ tailWord_314843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314843).length < 2 ^ (prefixWord ++ tailWord_314843).sum := by decide
  have hdescent : baseEnd_314843 < baseStart_314843 := by decide
  rcases family_descends (prefixWord ++ tailWord_314843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314847 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 2, 4, 2]
def baseStart_314847 : Nat := 118140960795 + 314847 * 2 ^ 59
def prefixEnd_314847 : Nat := 4983230072969 + 3 ^ 40 * 314847 * 2
def baseEnd_314847 : Nat := 161667843626234893364551

theorem tailTrace_314847 : CollatzResearch.WordTrace tailWord_314847 prefixEnd_314847 161667843626234893364551 := by
  unfold tailWord_314847
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483413490370565431734795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655608993580376954489863 11483413490370565431734795)
  ·
    refine ⟨17225120235555848147602193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11483413490370565431734795 17225120235555848147602193)
    ·
      refine ⟨12918840176666886110701645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17225120235555848147602193 12918840176666886110701645)
      ·
        refine ⟨4844565066250082291513117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12918840176666886110701645 4844565066250082291513117)
        ·
          refine ⟨1816711899843780859317419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4844565066250082291513117 1816711899843780859317419)
          ·
            refine ⟨2725067849765671288976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816711899843780859317419 2725067849765671288976129)
            ·
              refine ⟨2043800887324253466732097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725067849765671288976129 2043800887324253466732097)
              ·
                refine ⟨1532850665493190100049073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2043800887324253466732097 1532850665493190100049073)
                ·
                  refine ⟨1149637999119892575036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1532850665493190100049073 1149637999119892575036805)
                  ·
                    refine ⟨215557124834979857819401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149637999119892575036805 215557124834979857819401)
                    ·
                      refine ⟨161667843626234893364551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215557124834979857819401 161667843626234893364551)
                      ·
                        rfl

theorem cell23_314847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_314847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314847 prefixEnd_314847 := by exact prefixLift 314847
  have htrace : WordTrace (prefixWord ++ tailWord_314847) baseStart_314847 baseEnd_314847 := by
    simpa [prefixWord, tailWord_314847, baseEnd_314847] using wordTrace_append hprefix tailTrace_314847
  have hstable : (prefixWord ++ tailWord_314847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314847).length < 2 ^ (prefixWord ++ tailWord_314847).sum := by decide
  have hdescent : baseEnd_314847 < baseStart_314847 := by decide
  rcases family_descends (prefixWord ++ tailWord_314847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314878 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_314878 : Nat := 118140960795 + 314878 * 2 ^ 59
def prefixEnd_314878 : Nat := 4983230072969 + 3 ^ 40 * 314878 * 2
def baseEnd_314878 : Nat := 53894587175508090692303

theorem tailTrace_314878 : CollatzResearch.WordTrace tailWord_314878 prefixEnd_314878 53894587175508090692303 := by
  unfold tailWord_314878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435568019157282215764161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7656362768838838484075525 1435568019157282215764161)
  ·
    refine ⟨1076676014367961661823121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1435568019157282215764161 1076676014367961661823121)
    ·
      refine ⟨807507010775971246367341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076676014367961661823121 807507010775971246367341)
      ·
        refine ⟨302815129040989217387753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 807507010775971246367341 302815129040989217387753)
        ·
          refine ⟨227111346780741913040815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302815129040989217387753 227111346780741913040815)
          ·
            refine ⟨340667020171112869561223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227111346780741913040815 340667020171112869561223)
            ·
              refine ⟨511000530256669304341835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340667020171112869561223 511000530256669304341835)
              ·
                refine ⟨766500795385003956512753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511000530256669304341835 766500795385003956512753)
                ·
                  refine ⟨574875596538752967384565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766500795385003956512753 574875596538752967384565)
                  ·
                    refine ⟨53894587175508090692303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 574875596538752967384565 53894587175508090692303)
                    ·
                      rfl

theorem cell23_314878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_314878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314878 prefixEnd_314878 := by exact prefixLift 314878
  have htrace : WordTrace (prefixWord ++ tailWord_314878) baseStart_314878 baseEnd_314878 := by
    simpa [prefixWord, tailWord_314878, baseEnd_314878] using wordTrace_append hprefix tailTrace_314878
  have hstable : (prefixWord ++ tailWord_314878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314878).length < 2 ^ (prefixWord ++ tailWord_314878).sum := by decide
  have hdescent : baseEnd_314878 < baseStart_314878 := by decide
  rcases family_descends (prefixWord ++ tailWord_314878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314881 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_314881 : Nat := 118140960795 + 314881 * 2 ^ 59
def prefixEnd_314881 : Nat := 4983230072969 + 3 ^ 40 * 314881 * 2
def baseEnd_314881 : Nat := 161685301968487760339395

theorem tailTrace_314881 : CollatzResearch.WordTrace tailWord_314881 prefixEnd_314881 161685301968487760339395 := by
  unfold tailWord_314881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11484653572247389238472497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7656435714831592825648331 11484653572247389238472497)
  ·
    refine ⟨8613490179185541928854373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11484653572247389238472497 8613490179185541928854373)
    ·
      refine ⟨1615029408597289111660195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8613490179185541928854373 1615029408597289111660195)
      ·
        refine ⟨2422544112895933667490293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615029408597289111660195 2422544112895933667490293)
        ·
          refine ⟨227113510583993781327215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2422544112895933667490293 227113510583993781327215)
          ·
            refine ⟨340670265875990671990823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227113510583993781327215 340670265875990671990823)
            ·
              refine ⟨511005398813986007986235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340670265875990671990823 511005398813986007986235)
              ·
                refine ⟨766508098220979011979353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511005398813986007986235 766508098220979011979353)
                ·
                  refine ⟨574881073665734258984515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 766508098220979011979353 574881073665734258984515)
                  ·
                    refine ⟨862321610498601388476773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 574881073665734258984515 862321610498601388476773)
                    ·
                      refine ⟨161685301968487760339395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 862321610498601388476773 161685301968487760339395)
                      ·
                        rfl

theorem cell23_314881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_314881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314881 prefixEnd_314881 := by exact prefixLift 314881
  have htrace : WordTrace (prefixWord ++ tailWord_314881) baseStart_314881 baseEnd_314881 := by
    simpa [prefixWord, tailWord_314881, baseEnd_314881] using wordTrace_append hprefix tailTrace_314881
  have hstable : (prefixWord ++ tailWord_314881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314881).length < 2 ^ (prefixWord ++ tailWord_314881).sum := by decide
  have hdescent : baseEnd_314881 < baseStart_314881 := by decide
  rcases family_descends (prefixWord ++ tailWord_314881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314884 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_314884 : Nat := 118140960795 + 314884 * 2 ^ 59
def prefixEnd_314884 : Nat := 4983230072969 + 3 ^ 40 * 314884 * 2
def baseEnd_314884 : Nat := 161686842410451248601881

theorem tailTrace_314884 : CollatzResearch.WordTrace tailWord_314884 prefixEnd_314884 161686842410451248601881 := by
  unfold tailWord_314884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742381495618260375415853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7656508660824347167221137 5742381495618260375415853)
  ·
    refine ⟨2153393060856847640780945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5742381495618260375415853 2153393060856847640780945)
    ·
      refine ⟨1615044795642635730585709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2153393060856847640780945 1615044795642635730585709)
      ·
        refine ⟨605641798365988398969641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1615044795642635730585709 605641798365988398969641)
        ·
          refine ⟨454231348774491299227231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605641798365988398969641 454231348774491299227231)
          ·
            refine ⟨681347023161736948840847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454231348774491299227231 681347023161736948840847)
            ·
              refine ⟨1022020534742605423261271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681347023161736948840847 1022020534742605423261271)
              ·
                refine ⟨1533030802113908134891907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022020534742605423261271 1533030802113908134891907)
                ·
                  refine ⟨2299546203170862202337861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1533030802113908134891907 2299546203170862202337861)
                  ·
                    refine ⟨431164913094536662938349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2299546203170862202337861 431164913094536662938349)
                    ·
                      refine ⟨161686842410451248601881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431164913094536662938349 161686842410451248601881)
                      ·
                        rfl

theorem cell23_314884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_314884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314884 prefixEnd_314884 := by exact prefixLift 314884
  have htrace : WordTrace (prefixWord ++ tailWord_314884) baseStart_314884 baseEnd_314884 := by
    simpa [prefixWord, tailWord_314884, baseEnd_314884] using wordTrace_append hprefix tailTrace_314884
  have hstable : (prefixWord ++ tailWord_314884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314884).length < 2 ^ (prefixWord ++ tailWord_314884).sum := by decide
  have hdescent : baseEnd_314884 < baseStart_314884 := by decide
  rcases family_descends (prefixWord ++ tailWord_314884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314891 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 1, 4]
def baseStart_314891 : Nat := 118140960795 + 314891 * 2 ^ 59
def prefixEnd_314891 : Nat := 4983230072969 + 3 ^ 40 * 314891 * 2
def baseEnd_314891 : Nat := 53896812258344240404783

theorem tailTrace_314891 : CollatzResearch.WordTrace tailWord_314891 prefixEnd_314891 53896812258344240404783 := by
  unfold tailWord_314891
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485018302211160946336527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7656678868140773964224351 11485018302211160946336527)
  ·
    refine ⟨17227527453316741419504791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11485018302211160946336527 17227527453316741419504791)
    ·
      refine ⟨25841291179975112129257187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17227527453316741419504791 25841291179975112129257187)
      ·
        refine ⟨38761936769962668193885781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25841291179975112129257187 38761936769962668193885781)
        ·
          refine ⟨454241446523000017897099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 38761936769962668193885781 454241446523000017897099)
          ·
            refine ⟨681362169784500026845649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454241446523000017897099 681362169784500026845649)
            ·
              refine ⟨511021627338375020134237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681362169784500026845649 511021627338375020134237)
              ·
                refine ⟨191633110251890632550339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511021627338375020134237 191633110251890632550339)
                ·
                  refine ⟨287449665377835948825509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191633110251890632550339 287449665377835948825509)
                  ·
                    refine ⟨53896812258344240404783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287449665377835948825509 53896812258344240404783)
                    ·
                      rfl

theorem cell23_314891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 4].length) (baseStart_314891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314891 prefixEnd_314891 := by exact prefixLift 314891
  have htrace : WordTrace (prefixWord ++ tailWord_314891) baseStart_314891 baseEnd_314891 := by
    simpa [prefixWord, tailWord_314891, baseEnd_314891] using wordTrace_append hprefix tailTrace_314891
  have hstable : (prefixWord ++ tailWord_314891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314891).length < 2 ^ (prefixWord ++ tailWord_314891).sum := by decide
  have hdescent : baseEnd_314891 < baseStart_314891 := by decide
  rcases family_descends (prefixWord ++ tailWord_314891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314897 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_314897 : Nat := 118140960795 + 314897 * 2 ^ 59
def prefixEnd_314897 : Nat := 4983230072969 + 3 ^ 40 * 314897 * 2
def baseEnd_314897 : Nat := 161693517658959697739321

theorem tailTrace_314897 : CollatzResearch.WordTrace tailWord_314897 prefixEnd_314897 161693517658959697739321 := by
  unfold tailWord_314897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11485237140189423971054945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7656824760126282647369963 11485237140189423971054945)
  ·
    refine ⟨8613927855142067978291209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11485237140189423971054945 8613927855142067978291209)
    ·
      refine ⟨6460445891356550983718407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8613927855142067978291209 6460445891356550983718407)
      ·
        refine ⟨9690668837034826475577611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6460445891356550983718407 9690668837034826475577611)
        ·
          refine ⟨14536003255552239713366417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9690668837034826475577611 14536003255552239713366417)
          ·
            refine ⟨10902002441664179785024813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14536003255552239713366417 10902002441664179785024813)
            ·
              refine ⟨4088250915624067419384305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10902002441664179785024813 4088250915624067419384305)
              ·
                refine ⟨3066188186718050564538229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4088250915624067419384305 3066188186718050564538229)
                ·
                  refine ⟨287455142504817240425459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3066188186718050564538229 287455142504817240425459)
                  ·
                    refine ⟨431182713757225860638189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287455142504817240425459 431182713757225860638189)
                    ·
                      refine ⟨161693517658959697739321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431182713757225860638189 161693517658959697739321)
                      ·
                        rfl

theorem cell23_314897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_314897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314897 prefixEnd_314897 := by exact prefixLift 314897
  have htrace : WordTrace (prefixWord ++ tailWord_314897) baseStart_314897 baseEnd_314897 := by
    simpa [prefixWord, tailWord_314897, baseEnd_314897] using wordTrace_append hprefix tailTrace_314897
  have hstable : (prefixWord ++ tailWord_314897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314897).length < 2 ^ (prefixWord ++ tailWord_314897).sum := by decide
  have hdescent : baseEnd_314897 < baseStart_314897 := by decide
  rcases family_descends (prefixWord ++ tailWord_314897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314904 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 6]
def baseStart_314904 : Nat := 118140960795 + 314904 * 2 ^ 59
def prefixEnd_314904 : Nat := 4983230072969 + 3 ^ 40 * 314904 * 2
def baseEnd_314904 : Nat := 17966345780393463372421

theorem tailTrace_314904 : CollatzResearch.WordTrace tailWord_314904 prefixEnd_314904 17966345780393463372421 := by
  unfold tailWord_314904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742746225582032083279883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7656994967442709444373177 5742746225582032083279883)
  ·
    refine ⟨8614119338373048124919825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742746225582032083279883 8614119338373048124919825)
    ·
      refine ⟨6460589503779786093689869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8614119338373048124919825 6460589503779786093689869)
      ·
        refine ⟨2422721063917419785133701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6460589503779786093689869 2422721063917419785133701)
        ·
          refine ⟨454260199484516209712569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2422721063917419785133701 454260199484516209712569)
          ·
            refine ⟨340695149613387157284427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454260199484516209712569 340695149613387157284427)
            ·
              refine ⟨511042724420080735926641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340695149613387157284427 511042724420080735926641)
              ·
                refine ⟨383282043315060551944981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511042724420080735926641 383282043315060551944981)
                ·
                  refine ⟨17966345780393463372421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383282043315060551944981 17966345780393463372421)
                  ·
                    rfl

theorem cell23_314904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_314904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314904 prefixEnd_314904 := by exact prefixLift 314904
  have htrace : WordTrace (prefixWord ++ tailWord_314904) baseStart_314904 baseEnd_314904 := by
    simpa [prefixWord, tailWord_314904, baseEnd_314904] using wordTrace_append hprefix tailTrace_314904
  have hstable : (prefixWord ++ tailWord_314904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314904).length < 2 ^ (prefixWord ++ tailWord_314904).sum := by decide
  have hdescent : baseEnd_314904 < baseStart_314904 := by decide
  rcases family_descends (prefixWord ++ tailWord_314904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314914 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_314914 : Nat := 118140960795 + 314914 * 2 ^ 59
def prefixEnd_314914 : Nat := 4983230072969 + 3 ^ 40 * 314914 * 2
def baseEnd_314914 : Nat := 161702246830086131226743

theorem tailTrace_314914 : CollatzResearch.WordTrace tailWord_314914 prefixEnd_314914 161702246830086131226743 := by
  unfold tailWord_314914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871464295281958968605949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7657238120751890582949197 2871464295281958968605949)
  ·
    refine ⟨1076799110730734613227231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2871464295281958968605949 1076799110730734613227231)
    ·
      refine ⟨1615198666096101919840847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076799110730734613227231 1615198666096101919840847)
      ·
        refine ⟨2422797999144152879761271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615198666096101919840847 2422797999144152879761271)
        ·
          refine ⟨3634196998716229319641907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422797999144152879761271 3634196998716229319641907)
          ·
            refine ⟨5451295498074343979462861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634196998716229319641907 5451295498074343979462861)
            ·
              refine ⟨2044235811777878992298573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5451295498074343979462861 2044235811777878992298573)
              ·
                refine ⟨766588429416704622111965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044235811777878992298573 766588429416704622111965)
                ·
                  refine ⟨287470661031264233291987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 766588429416704622111965 287470661031264233291987)
                  ·
                    refine ⟨431205991546896349937981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287470661031264233291987 431205991546896349937981)
                    ·
                      refine ⟨161702246830086131226743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431205991546896349937981 161702246830086131226743)
                      ·
                        rfl

theorem cell23_314914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_314914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314914 prefixEnd_314914 := by exact prefixLift 314914
  have htrace : WordTrace (prefixWord ++ tailWord_314914) baseStart_314914 baseEnd_314914 := by
    simpa [prefixWord, tailWord_314914, baseEnd_314914] using wordTrace_append hprefix tailTrace_314914
  have hstable : (prefixWord ++ tailWord_314914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314914).length < 2 ^ (prefixWord ++ tailWord_314914).sum := by decide
  have hdescent : baseEnd_314914 < baseStart_314914 := by decide
  rcases family_descends (prefixWord ++ tailWord_314914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314964 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_314964 : Nat := 118140960795 + 314964 * 2 ^ 59
def prefixEnd_314964 : Nat := 4983230072969 + 3 ^ 40 * 314964 * 2
def baseEnd_314964 : Nat := 53909306954270311867171

theorem tailTrace_314964 : CollatzResearch.WordTrace tailWord_314964 prefixEnd_314964 53909306954270311867171 := by
  unfold tailWord_314964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743840415473347206871973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7658453887297796275829297 5743840415473347206871973)
  ·
    refine ⟨1076970077901252601288495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5743840415473347206871973 1076970077901252601288495)
    ·
      refine ⟨1615455116851878901932743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076970077901252601288495 1615455116851878901932743)
      ·
        refine ⟨2423182675277818352899115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615455116851878901932743 2423182675277818352899115)
        ·
          refine ⟨3634774012916727529348673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423182675277818352899115 3634774012916727529348673)
          ·
            refine ⟨2726080509687545647011505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3634774012916727529348673 2726080509687545647011505)
            ·
              refine ⟨2044560382265659235258629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2726080509687545647011505 2044560382265659235258629)
              ·
                refine ⟨383355071674811106610993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2044560382265659235258629 383355071674811106610993)
                ·
                  refine ⟨287516303756108329958245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383355071674811106610993 287516303756108329958245)
                  ·
                    refine ⟨53909306954270311867171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287516303756108329958245 53909306954270311867171)
                    ·
                      rfl

theorem cell23_314964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_314964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314964 prefixEnd_314964 := by exact prefixLift 314964
  have htrace : WordTrace (prefixWord ++ tailWord_314964) baseStart_314964 baseEnd_314964 := by
    simpa [prefixWord, tailWord_314964, baseEnd_314964] using wordTrace_append hprefix tailTrace_314964
  have hstable : (prefixWord ++ tailWord_314964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314964).length < 2 ^ (prefixWord ++ tailWord_314964).sum := by decide
  have hdescent : baseEnd_314964 < baseStart_314964 := by decide
  rcases family_descends (prefixWord ++ tailWord_314964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314981 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_314981 : Nat := 118140960795 + 314981 * 2 ^ 59
def prefixEnd_314981 : Nat := 4983230072969 + 3 ^ 40 * 314981 * 2
def baseEnd_314981 : Nat := 53912216677979123029645

theorem tailTrace_314981 : CollatzResearch.WordTrace tailWord_314981 prefixEnd_314981 53912216677979123029645 := by
  unfold tailWord_314981
  simp only [CollatzResearch.WordTrace]
  refine ⟨11488300871885106317112797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7658867247923404211408531 11488300871885106317112797)
  ·
    refine ⟨4308112826956914868917299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11488300871885106317112797 4308112826956914868917299)
    ·
      refine ⟨6462169240435372303375949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4308112826956914868917299 6462169240435372303375949)
      ·
        refine ⟨2423313465163264613765981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6462169240435372303375949 2423313465163264613765981)
        ·
          refine ⟨908742549436224230162243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2423313465163264613765981 908742549436224230162243)
          ·
            refine ⟨1363113824154336345243365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 908742549436224230162243 1363113824154336345243365)
            ·
              refine ⟨255583842028938064733131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1363113824154336345243365 255583842028938064733131)
              ·
                refine ⟨383375763043407097099697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255583842028938064733131 383375763043407097099697)
                ·
                  refine ⟨287531822282555322824773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383375763043407097099697 287531822282555322824773)
                  ·
                    refine ⟨53912216677979123029645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287531822282555322824773 53912216677979123029645)
                    ·
                      rfl

theorem cell23_314981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_314981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_314981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_314981 prefixEnd_314981 := by exact prefixLift 314981
  have htrace : WordTrace (prefixWord ++ tailWord_314981) baseStart_314981 baseEnd_314981 := by
    simpa [prefixWord, tailWord_314981, baseEnd_314981] using wordTrace_append hprefix tailTrace_314981
  have hstable : (prefixWord ++ tailWord_314981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314981).length < 2 ^ (prefixWord ++ tailWord_314981).sum := by decide
  have hdescent : baseEnd_314981 < baseStart_314981 := by decide
  rcases family_descends (prefixWord ++ tailWord_314981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315022 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_315022 : Nat := 118140960795 + 315022 * 2 ^ 59
def prefixEnd_315022 : Nat := 4983230072969 + 3 ^ 40 * 315022 * 2
def baseEnd_315022 : Nat := 161757702740771708676247

theorem tailTrace_315022 : CollatzResearch.WordTrace tailWord_315022 prefixEnd_315022 161757702740771708676247 := by
  unfold tailWord_315022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436224533092071289919415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7659864176491046879570213 1436224533092071289919415)
  ·
    refine ⟨2154336799638106934879123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436224533092071289919415 2154336799638106934879123)
    ·
      refine ⟨3231505199457160402318685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154336799638106934879123 3231505199457160402318685)
      ·
        refine ⟨1211814449796435150869507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3231505199457160402318685 1211814449796435150869507)
        ·
          refine ⟨1817721674694652726304261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211814449796435150869507 1817721674694652726304261)
          ·
            refine ⟨340822814005247386182049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1817721674694652726304261 340822814005247386182049)
            ·
              refine ⟨255617110503935539636537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340822814005247386182049 255617110503935539636537)
              ·
                refine ⟨191712832877951654727403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255617110503935539636537 191712832877951654727403)
                ·
                  refine ⟨287569249316927482091105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191712832877951654727403 287569249316927482091105)
                  ·
                    refine ⟨215676936987695611568329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287569249316927482091105 215676936987695611568329)
                    ·
                      refine ⟨161757702740771708676247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215676936987695611568329 161757702740771708676247)
                      ·
                        rfl

theorem cell23_315022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_315022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315022 prefixEnd_315022 := by exact prefixLift 315022
  have htrace : WordTrace (prefixWord ++ tailWord_315022) baseStart_315022 baseEnd_315022 := by
    simpa [prefixWord, tailWord_315022, baseEnd_315022] using wordTrace_append hprefix tailTrace_315022
  have hstable : (prefixWord ++ tailWord_315022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315022).length < 2 ^ (prefixWord ++ tailWord_315022).sum := by decide
  have hdescent : baseEnd_315022 < baseStart_315022 := by decide
  rcases family_descends (prefixWord ++ tailWord_315022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315038 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_315038 : Nat := 118140960795 + 315038 * 2 ^ 59
def prefixEnd_315038 : Nat := 4983230072969 + 3 ^ 40 * 315038 * 2
def baseEnd_315038 : Nat := 161765918431243646076173

theorem tailTrace_315038 : CollatzResearch.WordTrace tailWord_315038 prefixEnd_315038 161765918431243646076173 := by
  unfold tailWord_315038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436297479084825631492221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7660253221785736701291845 1436297479084825631492221)
  ·
    refine ⟨538611554656809611809583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1436297479084825631492221 538611554656809611809583)
    ·
      refine ⟨807917331985214417714375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538611554656809611809583 807917331985214417714375)
      ·
        refine ⟨1211875997977821626571563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807917331985214417714375 1211875997977821626571563)
        ·
          refine ⟨1817813996966732439857345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211875997977821626571563 1817813996966732439857345)
          ·
            refine ⟨1363360497725049329893009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1817813996966732439857345 1363360497725049329893009)
            ·
              refine ⟨1022520373293786997419757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1363360497725049329893009 1022520373293786997419757)
              ·
                refine ⟨383445139985170124032409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022520373293786997419757 383445139985170124032409)
                ·
                  refine ⟨287583854988877593024307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383445139985170124032409 287583854988877593024307)
                  ·
                    refine ⟨431375782483316389536461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287583854988877593024307 431375782483316389536461)
                    ·
                      refine ⟨161765918431243646076173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431375782483316389536461 161765918431243646076173)
                      ·
                        rfl

theorem cell23_315038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_315038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315038 prefixEnd_315038 := by exact prefixLift 315038
  have htrace : WordTrace (prefixWord ++ tailWord_315038) baseStart_315038 baseEnd_315038 := by
    simpa [prefixWord, tailWord_315038, baseEnd_315038] using wordTrace_append hprefix tailTrace_315038
  have hstable : (prefixWord ++ tailWord_315038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315038).length < 2 ^ (prefixWord ++ tailWord_315038).sum := by decide
  have hdescent : baseEnd_315038 < baseStart_315038 := by decide
  rcases family_descends (prefixWord ++ tailWord_315038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315077 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_315077 : Nat := 118140960795 + 315077 * 2 ^ 59
def prefixEnd_315077 : Nat := 4983230072969 + 3 ^ 40 * 315077 * 2
def baseEnd_315077 : Nat := 161785944176768993488493

theorem tailTrace_315077 : CollatzResearch.WordTrace tailWord_315077 prefixEnd_315077 161785944176768993488493 := by
  unfold tailWord_315077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11491802279537314712607485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7661201519691543141738323 11491802279537314712607485)
  ·
    refine ⟨4309425854826493017227807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11491802279537314712607485 4309425854826493017227807)
    ·
      refine ⟨6464138782239739525841711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4309425854826493017227807 6464138782239739525841711)
      ·
        refine ⟨9696208173359609288762567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6464138782239739525841711 9696208173359609288762567)
        ·
          refine ⟨14544312260039413933143851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9696208173359609288762567 14544312260039413933143851)
          ·
            refine ⟨21816468390059120899715777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14544312260039413933143851 21816468390059120899715777)
            ·
              refine ⟨16362351292544340674786833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21816468390059120899715777 16362351292544340674786833)
              ·
                refine ⟨12271763469408255506090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16362351292544340674786833 12271763469408255506090125)
                ·
                  refine ⟨4601911301028095814783797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12271763469408255506090125 4601911301028095814783797)
                  ·
                    refine ⟨431429184471383982635981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4601911301028095814783797 431429184471383982635981)
                    ·
                      refine ⟨161785944176768993488493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431429184471383982635981 161785944176768993488493)
                      ·
                        rfl

theorem cell23_315077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_315077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315077 prefixEnd_315077 := by exact prefixLift 315077
  have htrace : WordTrace (prefixWord ++ tailWord_315077) baseStart_315077 baseEnd_315077 := by
    simpa [prefixWord, tailWord_315077, baseEnd_315077] using wordTrace_append hprefix tailTrace_315077
  have hstable : (prefixWord ++ tailWord_315077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315077).length < 2 ^ (prefixWord ++ tailWord_315077).sum := by decide
  have hdescent : baseEnd_315077 < baseStart_315077 := by decide
  rcases family_descends (prefixWord ++ tailWord_315077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315097 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_315097 : Nat := 118140960795 + 315097 * 2 ^ 59
def prefixEnd_315097 : Nat := 4983230072969 + 3 ^ 40 * 315097 * 2
def baseEnd_315097 : Nat := 53932071263286305079467

theorem tailTrace_315097 : CollatzResearch.WordTrace tailWord_315097 prefixEnd_315097 53932071263286305079467 := by
  unfold tailWord_315097
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492531739464858128335545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7661687826309905418890363 11492531739464858128335545)
  ·
    refine ⟨8619398804598643596251659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11492531739464858128335545 8619398804598643596251659)
    ·
      refine ⟨12929098206897965394377489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619398804598643596251659 12929098206897965394377489)
      ·
        refine ⟨9696823655173474045783117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12929098206897965394377489 9696823655173474045783117)
        ·
          refine ⟨3636308870690052767168669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9696823655173474045783117 3636308870690052767168669)
          ·
            refine ⟨1363615826508769787688251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3636308870690052767168669 1363615826508769787688251)
            ·
              refine ⟨2045423739763154681532377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363615826508769787688251 2045423739763154681532377)
              ·
                refine ⟨1534067804822366011149283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2045423739763154681532377 1534067804822366011149283)
                ·
                  refine ⟨2301101707233549016723925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534067804822366011149283 2301101707233549016723925)
                  ·
                    refine ⟨53932071263286305079467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2301101707233549016723925 53932071263286305079467)
                    ·
                      rfl

theorem cell23_315097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_315097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315097 prefixEnd_315097 := by exact prefixLift 315097
  have htrace : WordTrace (prefixWord ++ tailWord_315097) baseStart_315097 baseEnd_315097 := by
    simpa [prefixWord, tailWord_315097, baseEnd_315097] using wordTrace_append hprefix tailTrace_315097
  have hstable : (prefixWord ++ tailWord_315097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315097).length < 2 ^ (prefixWord ++ tailWord_315097).sum := by decide
  have hdescent : baseEnd_315097 < baseStart_315097 := by decide
  rcases family_descends (prefixWord ++ tailWord_315097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315104 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2]
def baseStart_315104 : Nat := 118140960795 + 315104 * 2 ^ 59
def prefixEnd_315104 : Nat := 4983230072969 + 3 ^ 40 * 315104 * 2
def baseEnd_315104 : Nat := 161799808154440387850869

theorem tailTrace_315104 : CollatzResearch.WordTrace tailWord_315104 prefixEnd_315104 161799808154440387850869 := by
  unfold tailWord_315104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746393525219749161920183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7661858033626332215893577 5746393525219749161920183)
  ·
    refine ⟨8619590287829623742880275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5746393525219749161920183 8619590287829623742880275)
    ·
      refine ⟨12929385431744435614320413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619590287829623742880275 12929385431744435614320413)
      ·
        refine ⟨4848519536904163355370155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12929385431744435614320413 4848519536904163355370155)
        ·
          refine ⟨7272779305356245033055233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4848519536904163355370155 7272779305356245033055233)
          ·
            refine ⟨5454584479017183774791425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7272779305356245033055233 5454584479017183774791425)
            ·
              refine ⟨4090938359262887831093569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5454584479017183774791425 4090938359262887831093569)
              ·
                refine ⟨3068203769447165873320177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4090938359262887831093569 3068203769447165873320177)
                ·
                  refine ⟨2301152827085374404990133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068203769447165873320177 2301152827085374404990133)
                  ·
                    refine ⟨215733077539253850467825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2301152827085374404990133 215733077539253850467825)
                    ·
                      refine ⟨161799808154440387850869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215733077539253850467825 161799808154440387850869)
                      ·
                        rfl

theorem cell23_315104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_315104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315104 prefixEnd_315104 := by exact prefixLift 315104
  have htrace : WordTrace (prefixWord ++ tailWord_315104) baseStart_315104 baseEnd_315104 := by
    simpa [prefixWord, tailWord_315104, baseEnd_315104] using wordTrace_append hprefix tailTrace_315104
  have hstable : (prefixWord ++ tailWord_315104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315104).length < 2 ^ (prefixWord ++ tailWord_315104).sum := by decide
  have hdescent : baseEnd_315104 < baseStart_315104 := by decide
  rcases family_descends (prefixWord ++ tailWord_315104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315147 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_315147 : Nat := 118140960795 + 315147 * 2 ^ 59
def prefixEnd_315147 : Nat := 4983230072969 + 3 ^ 40 * 315147 * 2
def baseEnd_315147 : Nat := 161821887822583719613171

theorem tailTrace_315147 : CollatzResearch.WordTrace tailWord_315147 prefixEnd_315147 161821887822583719613171 := by
  unfold tailWord_315147
  simp only [CollatzResearch.WordTrace]
  refine ⟨11494355389283716667655695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7662903592855811111770463 11494355389283716667655695)
  ·
    refine ⟨17241533083925575001483543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11494355389283716667655695 17241533083925575001483543)
    ·
      refine ⟨25862299625888362502225315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17241533083925575001483543 25862299625888362502225315)
      ·
        refine ⟨38793449438832543753337973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25862299625888362502225315 38793449438832543753337973)
        ·
          refine ⟨3636885884890550976875435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38793449438832543753337973 3636885884890550976875435)
          ·
            refine ⟨5455328827335826465313153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3636885884890550976875435 5455328827335826465313153)
            ·
              refine ⟨4091496620501869848984865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5455328827335826465313153 4091496620501869848984865)
              ·
                refine ⟨3068622465376402386738649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4091496620501869848984865 3068622465376402386738649)
                ·
                  refine ⟨2301466849032301790053987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068622465376402386738649 2301466849032301790053987)
                  ·
                    refine ⟨3452200273548452685080981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301466849032301790053987 3452200273548452685080981)
                    ·
                      refine ⟨161821887822583719613171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3452200273548452685080981 161821887822583719613171)
                      ·
                        rfl

theorem cell23_315147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_315147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315147 prefixEnd_315147 := by exact prefixLift 315147
  have htrace : WordTrace (prefixWord ++ tailWord_315147) baseStart_315147 baseEnd_315147 := by
    simpa [prefixWord, tailWord_315147, baseEnd_315147] using wordTrace_append hprefix tailTrace_315147
  have hstable : (prefixWord ++ tailWord_315147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315147).length < 2 ^ (prefixWord ++ tailWord_315147).sum := by decide
  have hdescent : baseEnd_315147 < baseStart_315147 := by decide
  rcases family_descends (prefixWord ++ tailWord_315147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315188 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_315188 : Nat := 118140960795 + 315188 * 2 ^ 59
def prefixEnd_315188 : Nat := 4983230072969 + 3 ^ 40 * 315188 * 2
def baseEnd_315188 : Nat := 161842940529418059200483

theorem tailTrace_315188 : CollatzResearch.WordTrace tailWord_315188 prefixEnd_315188 161842940529418059200483 := by
  unfold tailWord_315188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747925391067590334949109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7663900521423453779932145 5747925391067590334949109)
  ·
    refine ⟨538868005412586593901479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5747925391067590334949109 538868005412586593901479)
    ·
      refine ⟨808302008118879890852219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538868005412586593901479 808302008118879890852219)
      ·
        refine ⟨1212453012178319836278329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808302008118879890852219 1212453012178319836278329)
        ·
          refine ⟨909339759133739877208747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212453012178319836278329 909339759133739877208747)
          ·
            refine ⟨1364009638700609815813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909339759133739877208747 1364009638700609815813121)
            ·
              refine ⟨1023007229025457361859841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364009638700609815813121 1023007229025457361859841)
              ·
                refine ⟨767255421769093021394881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023007229025457361859841 767255421769093021394881)
                ·
                  refine ⟨575441566326819766046161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 767255421769093021394881 575441566326819766046161)
                  ·
                    refine ⟨431581174745114824534621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 575441566326819766046161 431581174745114824534621)
                    ·
                      refine ⟨161842940529418059200483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431581174745114824534621 161842940529418059200483)
                      ·
                        rfl

theorem cell23_315188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_315188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315188 prefixEnd_315188 := by exact prefixLift 315188
  have htrace : WordTrace (prefixWord ++ tailWord_315188) baseStart_315188 baseEnd_315188 := by
    simpa [prefixWord, tailWord_315188, baseEnd_315188] using wordTrace_append hprefix tailTrace_315188
  have hstable : (prefixWord ++ tailWord_315188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315188).length < 2 ^ (prefixWord ++ tailWord_315188).sum := by decide
  have hdescent : baseEnd_315188 < baseStart_315188 := by decide
  rcases family_descends (prefixWord ++ tailWord_315188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315218 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_315218 : Nat := 118140960795 + 315218 * 2 ^ 59
def prefixEnd_315218 : Nat := 4983230072969 + 3 ^ 40 * 315218 * 2
def baseEnd_315218 : Nat := 161858344949052941825345

theorem tailTrace_315218 : CollatzResearch.WordTrace tailWord_315218 prefixEnd_315218 161858344949052941825345 := by
  unfold tailWord_315218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874236243006623948372577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7664629981350997195660205 2874236243006623948372577)
  ·
    refine ⟨2155677182254967961279433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2874236243006623948372577 2155677182254967961279433)
    ·
      refine ⟨1616757886691225970959575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155677182254967961279433 1616757886691225970959575)
      ·
        refine ⟨2425136830036838956439363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616757886691225970959575 2425136830036838956439363)
        ·
          refine ⟨3637705245055258434659045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425136830036838956439363 3637705245055258434659045)
          ·
            refine ⟨682069733447860956498571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3637705245055258434659045 682069733447860956498571)
            ·
              refine ⟨1023104600171791434747857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682069733447860956498571 1023104600171791434747857)
              ·
                refine ⟨767328450128843576060893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023104600171791434747857 767328450128843576060893)
                ·
                  refine ⟨287748168798316341022835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767328450128843576060893 287748168798316341022835)
                  ·
                    refine ⟨431622253197474511534253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287748168798316341022835 431622253197474511534253)
                    ·
                      refine ⟨161858344949052941825345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431622253197474511534253 161858344949052941825345)
                      ·
                        rfl

theorem cell23_315218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_315218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315218 prefixEnd_315218 := by exact prefixLift 315218
  have htrace : WordTrace (prefixWord ++ tailWord_315218) baseStart_315218 baseEnd_315218 := by
    simpa [prefixWord, tailWord_315218, baseEnd_315218] using wordTrace_append hprefix tailTrace_315218
  have hstable : (prefixWord ++ tailWord_315218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315218).length < 2 ^ (prefixWord ++ tailWord_315218).sum := by decide
  have hdescent : baseEnd_315218 < baseStart_315218 := by decide
  rcases family_descends (prefixWord ++ tailWord_315218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315258 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_315258 : Nat := 118140960795 + 315258 * 2 ^ 59
def prefixEnd_315258 : Nat := 4983230072969 + 3 ^ 40 * 315258 * 2
def baseEnd_315258 : Nat := 161878884175232785325161

theorem tailTrace_315258 : CollatzResearch.WordTrace tailWord_315258 prefixEnd_315258 161878884175232785325161 := by
  unfold tailWord_315258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874600972970395656236607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7665602594587721749964285 2874600972970395656236607)
  ·
    refine ⟨4311901459455593484354911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874600972970395656236607 4311901459455593484354911)
    ·
      refine ⟨6467852189183390226532367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311901459455593484354911 6467852189183390226532367)
      ·
        refine ⟨9701778283775085339798551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6467852189183390226532367 9701778283775085339798551)
        ·
          refine ⟨14552667425662628009697827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9701778283775085339798551 14552667425662628009697827)
          ·
            refine ⟨21829001138493942014546741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14552667425662628009697827 21829001138493942014546741)
            ·
              refine ⟨2046468856733807063863757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21829001138493942014546741 2046468856733807063863757)
              ·
                refine ⟨767425821275177648948909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046468856733807063863757 767425821275177648948909)
                ·
                  refine ⟨287784682978191618355841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767425821275177648948909 287784682978191618355841)
                  ·
                    refine ⟨215838512233643713766881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287784682978191618355841 215838512233643713766881)
                    ·
                      refine ⟨161878884175232785325161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215838512233643713766881 161878884175232785325161)
                      ·
                        rfl

theorem cell23_315258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_315258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315258 prefixEnd_315258 := by exact prefixLift 315258
  have htrace : WordTrace (prefixWord ++ tailWord_315258) baseStart_315258 baseEnd_315258 := by
    simpa [prefixWord, tailWord_315258, baseEnd_315258] using wordTrace_append hprefix tailTrace_315258
  have hstable : (prefixWord ++ tailWord_315258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315258).length < 2 ^ (prefixWord ++ tailWord_315258).sum := by decide
  have hdescent : baseEnd_315258 < baseStart_315258 := by decide
  rcases family_descends (prefixWord ++ tailWord_315258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315271 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_315271 : Nat := 118140960795 + 315271 * 2 ^ 59
def prefixEnd_315271 : Nat := 4983230072969 + 3 ^ 40 * 315271 * 2
def baseEnd_315271 : Nat := 161885559423741234462601

theorem tailTrace_315271 : CollatzResearch.WordTrace tailWord_315271 prefixEnd_315271 161885559423741234462601 := by
  unfold tailWord_315271
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498878040834485845169667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7665918693889657230113111 11498878040834485845169667)
  ·
    refine ⟨17248317061251728767754501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11498878040834485845169667 17248317061251728767754501)
    ·
      refine ⟨3234059448984699143953969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17248317061251728767754501 3234059448984699143953969)
      ·
        refine ⟨2425544586738524357965477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3234059448984699143953969 2425544586738524357965477)
        ·
          refine ⟨454789610013473317118527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2425544586738524357965477 454789610013473317118527)
          ·
            refine ⟨682184415020209975677791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454789610013473317118527 682184415020209975677791)
            ·
              refine ⟨1023276622530314963516687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682184415020209975677791 1023276622530314963516687)
              ·
                refine ⟨1534914933795472445275031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023276622530314963516687 1534914933795472445275031)
                ·
                  refine ⟨2302372400693208667912547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534914933795472445275031 2302372400693208667912547)
                  ·
                    refine ⟨3453558601039813001868821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302372400693208667912547 3453558601039813001868821)
                    ·
                      refine ⟨161885559423741234462601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3453558601039813001868821 161885559423741234462601)
                      ·
                        rfl

theorem cell23_315271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_315271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315271 prefixEnd_315271 := by exact prefixLift 315271
  have htrace : WordTrace (prefixWord ++ tailWord_315271) baseStart_315271 baseEnd_315271 := by
    simpa [prefixWord, tailWord_315271, baseEnd_315271] using wordTrace_append hprefix tailTrace_315271
  have hstable : (prefixWord ++ tailWord_315271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315271).length < 2 ^ (prefixWord ++ tailWord_315271).sum := by decide
  have hdescent : baseEnd_315271 < baseStart_315271 := by decide
  rcases family_descends (prefixWord ++ tailWord_315271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315298 : List Nat := [3, 3, 1, 2, 4, 1, 9]
def baseStart_315298 : Nat := 118140960795 + 315298 * 2 ^ 59
def prefixEnd_315298 : Nat := 4983230072969 + 3 ^ 40 * 315298 * 2
def baseEnd_315298 : Nat := 1998758313597686775617

theorem tailTrace_315298 : CollatzResearch.WordTrace tailWord_315298 prefixEnd_315298 1998758313597686775617 := by
  unfold tailWord_315298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874965702934167364100637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7666575207824446304268365 2874965702934167364100637)
  ·
    refine ⟨1078112138600312761537739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2874965702934167364100637 1078112138600312761537739)
    ·
      refine ⟨1617168207900469142306609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078112138600312761537739 1617168207900469142306609)
      ·
        refine ⟨1212876155925351856729957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1617168207900469142306609 1212876155925351856729957)
        ·
          refine ⟨227414279236003473136867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1212876155925351856729957 227414279236003473136867)
          ·
            refine ⟨341121418854005209705301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227414279236003473136867 341121418854005209705301)
            ·
              refine ⟨1998758313597686775617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 341121418854005209705301 1998758313597686775617)
              ·
                rfl

theorem cell23_315298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 9].length) (baseStart_315298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315298 prefixEnd_315298 := by exact prefixLift 315298
  have htrace : WordTrace (prefixWord ++ tailWord_315298) baseStart_315298 baseEnd_315298 := by
    simpa [prefixWord, tailWord_315298, baseEnd_315298] using wordTrace_append hprefix tailTrace_315298
  have hstable : (prefixWord ++ tailWord_315298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315298).length < 2 ^ (prefixWord ++ tailWord_315298).sum := by decide
  have hdescent : baseEnd_315298 < baseStart_315298 := by decide
  rcases family_descends (prefixWord ++ tailWord_315298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315325 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_315325 : Nat := 118140960795 + 315325 * 2 ^ 59
def prefixEnd_315325 : Nat := 4983230072969 + 3 ^ 40 * 315325 * 2
def baseEnd_315325 : Nat := 161913287379084023187353

theorem tailTrace_315325 : CollatzResearch.WordTrace tailWord_315325 prefixEnd_315325 161913287379084023187353 := by
  unfold tailWord_315325
  simp only [CollatzResearch.WordTrace]
  refine ⟨11500847582638853067635429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7667231721759235378423619 11500847582638853067635429)
  ·
    refine ⟨2156408921744784950181643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11500847582638853067635429 2156408921744784950181643)
    ·
      refine ⟨3234613382617177425272465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156408921744784950181643 3234613382617177425272465)
      ·
        refine ⟨2425960036962883068954349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3234613382617177425272465 2425960036962883068954349)
        ·
          refine ⟨909735013861081150857881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2425960036962883068954349 909735013861081150857881)
          ·
            refine ⟨682301260395810863143411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909735013861081150857881 682301260395810863143411)
            ·
              refine ⟨1023451890593716294715117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682301260395810863143411 1023451890593716294715117)
              ·
                refine ⟨383794458972643610518169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023451890593716294715117 383794458972643610518169)
                ·
                  refine ⟨287845844229482707888627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383794458972643610518169 287845844229482707888627)
                  ·
                    refine ⟨431768766344224061832941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287845844229482707888627 431768766344224061832941)
                    ·
                      refine ⟨161913287379084023187353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431768766344224061832941 161913287379084023187353)
                      ·
                        rfl

theorem cell23_315325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_315325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315325 prefixEnd_315325 := by exact prefixLift 315325
  have htrace : WordTrace (prefixWord ++ tailWord_315325) baseStart_315325 baseEnd_315325 := by
    simpa [prefixWord, tailWord_315325, baseEnd_315325] using wordTrace_append hprefix tailTrace_315325
  have hstable : (prefixWord ++ tailWord_315325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315325).length < 2 ^ (prefixWord ++ tailWord_315325).sum := by decide
  have hdescent : baseEnd_315325 < baseStart_315325 := by decide
  rcases family_descends (prefixWord ++ tailWord_315325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315382 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_315382 : Nat := 118140960795 + 315382 * 2 ^ 59
def prefixEnd_315382 : Nat := 4983230072969 + 3 ^ 40 * 315382 * 2
def baseEnd_315382 : Nat := 161942555776390300174591

theorem tailTrace_315382 : CollatzResearch.WordTrace tailWord_315382 prefixEnd_315382 161942555776390300174591 := by
  unfold tailWord_315382
  simp only [CollatzResearch.WordTrace]
  refine ⟨718932908964521987653775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7668617695621567868306933 718932908964521987653775)
  ·
    refine ⟨1078399363446782981480663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 718932908964521987653775 1078399363446782981480663)
    ·
      refine ⟨1617599045170174472220995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078399363446782981480663 1617599045170174472220995)
      ·
        refine ⟨2426398567755261708331493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617599045170174472220995 2426398567755261708331493)
        ·
          refine ⟨454949731454111570312155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2426398567755261708331493 454949731454111570312155)
          ·
            refine ⟨682424597181167355468233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454949731454111570312155 682424597181167355468233)
            ·
              refine ⟨511818447885875516601175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682424597181167355468233 511818447885875516601175)
              ·
                refine ⟨767727671828813274901763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511818447885875516601175 767727671828813274901763)
                ·
                  refine ⟨1151591507743219912352645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767727671828813274901763 1151591507743219912352645)
                  ·
                    refine ⟨215923407701853733566121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1151591507743219912352645 215923407701853733566121)
                    ·
                      refine ⟨161942555776390300174591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 215923407701853733566121 161942555776390300174591)
                      ·
                        rfl

theorem cell23_315382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_315382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315382 prefixEnd_315382 := by exact prefixLift 315382
  have htrace : WordTrace (prefixWord ++ tailWord_315382) baseStart_315382 baseEnd_315382 := by
    simpa [prefixWord, tailWord_315382, baseEnd_315382] using wordTrace_append hprefix tailTrace_315382
  have hstable : (prefixWord ++ tailWord_315382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315382).length < 2 ^ (prefixWord ++ tailWord_315382).sum := by decide
  have hdescent : baseEnd_315382 < baseStart_315382 := by decide
  rcases family_descends (prefixWord ++ tailWord_315382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315438 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_315438 : Nat := 118140960795 + 315438 * 2 ^ 59
def prefixEnd_315438 : Nat := 4983230072969 + 3 ^ 40 * 315438 * 2
def baseEnd_315438 : Nat := 161971310693042081074333

theorem tailTrace_315438 : CollatzResearch.WordTrace tailWord_315438 prefixEnd_315438 161971310693042081074333 := by
  unfold tailWord_315438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438121128903684170812371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7669979354152982244332645 1438121128903684170812371)
  ·
    refine ⟨2157181693355526256218557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438121128903684170812371 2157181693355526256218557)
    ·
      refine ⟨808943135008322346081959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2157181693355526256218557 808943135008322346081959)
      ·
        refine ⟨1213414702512483519122939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808943135008322346081959 1213414702512483519122939)
        ·
          refine ⟨1820122053768725278684409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213414702512483519122939 1820122053768725278684409)
          ·
            refine ⟨1365091540326543959013307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820122053768725278684409 1365091540326543959013307)
            ·
              refine ⟨2047637310489815938519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365091540326543959013307 2047637310489815938519961)
              ·
                refine ⟨1535727982867361953889971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047637310489815938519961 1535727982867361953889971)
                ·
                  refine ⟨2303591974301042930834957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535727982867361953889971 2303591974301042930834957)
                  ·
                    refine ⟨863846990362891099063109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303591974301042930834957 863846990362891099063109)
                    ·
                      refine ⟨161971310693042081074333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 863846990362891099063109 161971310693042081074333)
                      ·
                        rfl

theorem cell23_315438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_315438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315438 prefixEnd_315438 := by exact prefixLift 315438
  have htrace : WordTrace (prefixWord ++ tailWord_315438) baseStart_315438 baseEnd_315438 := by
    simpa [prefixWord, tailWord_315438, baseEnd_315438] using wordTrace_append hprefix tailTrace_315438
  have hstable : (prefixWord ++ tailWord_315438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315438).length < 2 ^ (prefixWord ++ tailWord_315438).sum := by decide
  have hdescent : baseEnd_315438 < baseStart_315438 := by decide
  rcases family_descends (prefixWord ++ tailWord_315438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315471 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_315471 : Nat := 118140960795 + 315471 * 2 ^ 59
def prefixEnd_315471 : Nat := 4983230072969 + 3 ^ 40 * 315471 * 2
def baseEnd_315471 : Nat := 161988255554640451961681

theorem tailTrace_315471 : CollatzResearch.WordTrace tailWord_315471 prefixEnd_315471 161988255554640451961681 := by
  unfold tailWord_315471
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506172640109920002450267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7670781760073280001633511 11506172640109920002450267)
  ·
    refine ⟨17259258960164880003675401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11506172640109920002450267 17259258960164880003675401)
    ·
      refine ⟨12944444220123660002756551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17259258960164880003675401 12944444220123660002756551)
      ·
        refine ⟨19416666330185490004134827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12944444220123660002756551 19416666330185490004134827)
        ·
          refine ⟨29124999495278235006202241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19416666330185490004134827 29124999495278235006202241)
          ·
            refine ⟨21843749621458676254651681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29124999495278235006202241 21843749621458676254651681)
            ·
              refine ⟨16382812216094007190988761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21843749621458676254651681 16382812216094007190988761)
              ·
                refine ⟨12287109162070505393241571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16382812216094007190988761 12287109162070505393241571)
                ·
                  refine ⟨18430663743105758089862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12287109162070505393241571 18430663743105758089862357)
                  ·
                    refine ⟨431968681479041205231149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18430663743105758089862357 431968681479041205231149)
                    ·
                      refine ⟨161988255554640451961681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 431968681479041205231149 161988255554640451961681)
                      ·
                        rfl

theorem cell23_315471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_315471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315471 prefixEnd_315471 := by exact prefixLift 315471
  have htrace : WordTrace (prefixWord ++ tailWord_315471) baseStart_315471 baseEnd_315471 := by
    simpa [prefixWord, tailWord_315471, baseEnd_315471] using wordTrace_append hprefix tailTrace_315471
  have hstable : (prefixWord ++ tailWord_315471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315471).length < 2 ^ (prefixWord ++ tailWord_315471).sum := by decide
  have hdescent : baseEnd_315471 < baseStart_315471 := by decide
  rcases family_descends (prefixWord ++ tailWord_315471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315482 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_315482 : Nat := 118140960795 + 315482 * 2 ^ 59
def prefixEnd_315482 : Nat := 4983230072969 + 3 ^ 40 * 315482 * 2
def baseEnd_315482 : Nat := 53997967947279969641377

theorem tailTrace_315482 : CollatzResearch.WordTrace tailWord_315482 prefixEnd_315482 53997967947279969641377 := by
  unfold tailWord_315482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2876643460767517220275175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7671049228713379254067133 2876643460767517220275175)
  ·
    refine ⟨4314965191151275830412763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2876643460767517220275175 4314965191151275830412763)
    ·
      refine ⟨6472447786726913745619145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4314965191151275830412763 6472447786726913745619145)
      ·
        refine ⟨4854335840045185309214359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6472447786726913745619145 4854335840045185309214359)
        ·
          refine ⟨7281503760067777963821539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854335840045185309214359 7281503760067777963821539)
          ·
            refine ⟨10922255640101666945732309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281503760067777963821539 10922255640101666945732309)
            ·
              refine ⟨255990366564882819040601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10922255640101666945732309 255990366564882819040601)
              ·
                refine ⟨191992774923662114280451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255990366564882819040601 191992774923662114280451)
                ·
                  refine ⟨287989162385493171420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191992774923662114280451 287989162385493171420677)
                  ·
                    refine ⟨53997967947279969641377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287989162385493171420677 53997967947279969641377)
                    ·
                      rfl

theorem cell23_315482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_315482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315482 prefixEnd_315482 := by exact prefixLift 315482
  have htrace : WordTrace (prefixWord ++ tailWord_315482) baseStart_315482 baseEnd_315482 := by
    simpa [prefixWord, tailWord_315482, baseEnd_315482] using wordTrace_append hprefix tailTrace_315482
  have hstable : (prefixWord ++ tailWord_315482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315482).length < 2 ^ (prefixWord ++ tailWord_315482).sum := by decide
  have hdescent : baseEnd_315482 < baseStart_315482 := by decide
  rcases family_descends (prefixWord ++ tailWord_315482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315538 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_315538 : Nat := 118140960795 + 315538 * 2 ^ 59
def prefixEnd_315538 : Nat := 4983230072969 + 3 ^ 40 * 315538 * 2
def baseEnd_315538 : Nat := 54007552919497229941291

theorem tailTrace_315538 : CollatzResearch.WordTrace tailWord_315538 prefixEnd_315538 54007552919497229941291 := by
  unfold tailWord_315538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877154082716797611284817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7672410887244793630092845 2877154082716797611284817)
  ·
    refine ⟨2157865562037598208463613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2877154082716797611284817 2157865562037598208463613)
    ·
      refine ⟨809199585764099328173855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2157865562037598208463613 809199585764099328173855)
      ·
        refine ⟨1213799378646148992260783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809199585764099328173855 1213799378646148992260783)
        ·
          refine ⟨1820699067969223488391175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213799378646148992260783 1820699067969223488391175)
          ·
            refine ⟨2731048601953835232586763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820699067969223488391175 2731048601953835232586763)
            ·
              refine ⟨4096572902930752848880145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731048601953835232586763 4096572902930752848880145)
              ·
                refine ⟨3072429677198064636660109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096572902930752848880145 3072429677198064636660109)
                ·
                  refine ⟨1152161128949274238747541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3072429677198064636660109 1152161128949274238747541)
                  ·
                    refine ⟨54007552919497229941291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1152161128949274238747541 54007552919497229941291)
                    ·
                      rfl

theorem cell23_315538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_315538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315538 prefixEnd_315538 := by exact prefixLift 315538
  have htrace : WordTrace (prefixWord ++ tailWord_315538) baseStart_315538 baseEnd_315538 := by
    simpa [prefixWord, tailWord_315538, baseEnd_315538] using wordTrace_append hprefix tailTrace_315538
  have hstable : (prefixWord ++ tailWord_315538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315538).length < 2 ^ (prefixWord ++ tailWord_315538).sum := by decide
  have hdescent : baseEnd_315538 < baseStart_315538 := by decide
  rcases family_descends (prefixWord ++ tailWord_315538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315545 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 7, 2, 2]
def baseStart_315545 : Nat := 118140960795 + 315545 * 2 ^ 59
def prefixEnd_315545 : Nat := 4983230072969 + 3 ^ 40 * 315545 * 2
def baseEnd_315545 : Nat := 162026253123073162436341

theorem tailTrace_315545 : CollatzResearch.WordTrace tailWord_315545 prefixEnd_315545 162026253123073162436341 := by
  unfold tailWord_315545
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508871641841830640644089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7672581094561220427096059 11508871641841830640644089)
  ·
    refine ⟨8631653731381372980483067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11508871641841830640644089 8631653731381372980483067)
    ·
      refine ⟨12947480597072059470724601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631653731381372980483067 12947480597072059470724601)
      ·
        refine ⟨9710610447804044603043451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12947480597072059470724601 9710610447804044603043451)
        ·
          refine ⟨14565915671706066904565177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710610447804044603043451 14565915671706066904565177)
          ·
            refine ⟨10924436753779550178423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14565915671706066904565177 10924436753779550178423883)
            ·
              refine ⟨16386655130669325267635825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924436753779550178423883 16386655130669325267635825)
              ·
                refine ⟨12289991348001993950726869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16386655130669325267635825 12289991348001993950726869)
                ·
                  refine ⟨288046672218796733220161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12289991348001993950726869 288046672218796733220161)
                  ·
                    refine ⟨216035004164097549915121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288046672218796733220161 216035004164097549915121)
                    ·
                      refine ⟨162026253123073162436341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216035004164097549915121 162026253123073162436341)
                      ·
                        rfl

theorem cell23_315545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_315545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315545 prefixEnd_315545 := by exact prefixLift 315545
  have htrace : WordTrace (prefixWord ++ tailWord_315545) baseStart_315545 baseEnd_315545 := by
    simpa [prefixWord, tailWord_315545, baseEnd_315545] using wordTrace_append hprefix tailTrace_315545
  have hstable : (prefixWord ++ tailWord_315545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315545).length < 2 ^ (prefixWord ++ tailWord_315545).sum := by decide
  have hdescent : baseEnd_315545 < baseStart_315545 := by decide
  rcases family_descends (prefixWord ++ tailWord_315545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315548 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_315548 : Nat := 118140960795 + 315548 * 2 ^ 59
def prefixEnd_315548 : Nat := 4983230072969 + 3 ^ 40 * 315548 * 2
def baseEnd_315548 : Nat := 162027793565036650698827

theorem tailTrace_315548 : CollatzResearch.WordTrace tailWord_315548 prefixEnd_315548 162027793565036650698827 := by
  unfold tailWord_315548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754490530415481076501649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7672654040553974768668865 5754490530415481076501649)
  ·
    refine ⟨4315867897811610807376237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5754490530415481076501649 4315867897811610807376237)
    ·
      refine ⟨1618450461679354052766089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4315867897811610807376237 1618450461679354052766089)
      ·
        refine ⟨1213837846259515539574567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618450461679354052766089 1213837846259515539574567)
        ·
          refine ⟨1820756769389273309361851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213837846259515539574567 1820756769389273309361851)
          ·
            refine ⟨2731135154083909964042777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820756769389273309361851 2731135154083909964042777)
            ·
              refine ⟨2048351365562932473032083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731135154083909964042777 2048351365562932473032083)
              ·
                refine ⟨3072527048344398709548125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048351365562932473032083 3072527048344398709548125)
                ·
                  refine ⟨1152197643129149516080547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3072527048344398709548125 1152197643129149516080547)
                  ·
                    refine ⟨1728296464693724274120821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152197643129149516080547 1728296464693724274120821)
                    ·
                      refine ⟨162027793565036650698827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1728296464693724274120821 162027793565036650698827)
                      ·
                        rfl

theorem cell23_315548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_315548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315548 prefixEnd_315548 := by exact prefixLift 315548
  have htrace : WordTrace (prefixWord ++ tailWord_315548) baseStart_315548 baseEnd_315548 := by
    simpa [prefixWord, tailWord_315548, baseEnd_315548] using wordTrace_append hprefix tailTrace_315548
  have hstable : (prefixWord ++ tailWord_315548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315548).length < 2 ^ (prefixWord ++ tailWord_315548).sum := by decide
  have hdescent : baseEnd_315548 < baseStart_315548 := by decide
  rcases family_descends (prefixWord ++ tailWord_315548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315579 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 1, 2, 2]
def baseStart_315579 : Nat := 118140960795 + 315579 * 2 ^ 59
def prefixEnd_315579 : Nat := 4983230072969 + 3 ^ 40 * 315579 * 2
def baseEnd_315579 : Nat := 162043711465326029411185

theorem tailTrace_315579 : CollatzResearch.WordTrace tailWord_315579 prefixEnd_315579 162043711465326029411185 := by
  unfold tailWord_315579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510111723718654447381791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673407815812436298254527 11510111723718654447381791)
  ·
    refine ⟨17265167585577981671072687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11510111723718654447381791 17265167585577981671072687)
    ·
      refine ⟨25897751378366972506609031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17265167585577981671072687 25897751378366972506609031)
      ·
        refine ⟨38846627067550458759913547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897751378366972506609031 38846627067550458759913547)
        ·
          refine ⟨58269940601325688139870321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38846627067550458759913547 58269940601325688139870321)
          ·
            refine ⟨43702455450994266104902741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58269940601325688139870321 43702455450994266104902741)
            ·
              refine ⟨512138149816339055916829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 43702455450994266104902741 512138149816339055916829)
              ·
                refine ⟨192051806181127145968811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512138149816339055916829 192051806181127145968811)
                ·
                  refine ⟨288077709271690718953217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192051806181127145968811 288077709271690718953217)
                  ·
                    refine ⟨216058281953768039214913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288077709271690718953217 216058281953768039214913)
                    ·
                      refine ⟨162043711465326029411185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216058281953768039214913 162043711465326029411185)
                      ·
                        rfl

theorem cell23_315579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 1, 2, 2].length) (baseStart_315579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315579 prefixEnd_315579 := by exact prefixLift 315579
  have htrace : WordTrace (prefixWord ++ tailWord_315579) baseStart_315579 baseEnd_315579 := by
    simpa [prefixWord, tailWord_315579, baseEnd_315579] using wordTrace_append hprefix tailTrace_315579
  have hstable : (prefixWord ++ tailWord_315579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315579).length < 2 ^ (prefixWord ++ tailWord_315579).sum := by decide
  have hdescent : baseEnd_315579 < baseStart_315579 := by decide
  rcases family_descends (prefixWord ++ tailWord_315579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315585 : List Nat := [1, 2, 6, 1, 2, 1, 10]
def baseStart_315585 : Nat := 118140960795 + 315585 * 2 ^ 59
def prefixEnd_315585 : Nat := 4983230072969 + 3 ^ 40 * 315585 * 2
def baseEnd_315585 : Nat := 2000577683324111184397

theorem tailTrace_315585 : CollatzResearch.WordTrace tailWord_315585 prefixEnd_315585 2000577683324111184397 := by
  unfold tailWord_315585
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510330561696917472100209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673553707797944981400139 11510330561696917472100209)
  ·
    refine ⟨8632747921272688104075157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11510330561696917472100209 8632747921272688104075157)
    ·
      refine ⟨404660058809657254878523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8632747921272688104075157 404660058809657254878523)
      ·
        refine ⟨606990088214485882317785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404660058809657254878523 606990088214485882317785)
        ·
          refine ⟨455242566160864411738339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606990088214485882317785 455242566160864411738339)
          ·
            refine ⟨682863849241296617607509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455242566160864411738339 682863849241296617607509)
            ·
              refine ⟨2000577683324111184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 682863849241296617607509 2000577683324111184397)
              ·
                rfl

theorem cell23_315585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 10].length) (baseStart_315585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315585 prefixEnd_315585 := by exact prefixLift 315585
  have htrace : WordTrace (prefixWord ++ tailWord_315585) baseStart_315585 baseEnd_315585 := by
    simpa [prefixWord, tailWord_315585, baseEnd_315585] using wordTrace_append hprefix tailTrace_315585
  have hstable : (prefixWord ++ tailWord_315585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315585).length < 2 ^ (prefixWord ++ tailWord_315585).sum := by decide
  have hdescent : baseEnd_315585 < baseStart_315585 := by decide
  rcases family_descends (prefixWord ++ tailWord_315585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315595 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 3]
def baseStart_315595 : Nat := 118140960795 + 315595 * 2 ^ 59
def prefixEnd_315595 : Nat := 4983230072969 + 3 ^ 40 * 315595 * 2
def baseEnd_315595 : Nat := 162051927155797966811111

theorem tailTrace_315595 : CollatzResearch.WordTrace tailWord_315595 prefixEnd_315595 162051927155797966811111 := by
  unfold tailWord_315595
  simp only [CollatzResearch.WordTrace]
  refine ⟨11510695291660689179964239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673796861107126119976159 11510695291660689179964239)
  ·
    refine ⟨17266042937491033769946359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11510695291660689179964239 17266042937491033769946359)
    ·
      refine ⟨25899064406236550654919539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17266042937491033769946359 25899064406236550654919539)
      ·
        refine ⟨38848596609354825982379309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25899064406236550654919539 38848596609354825982379309)
        ·
          refine ⟨14568223728508059743392241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38848596609354825982379309 14568223728508059743392241)
          ·
            refine ⟨10926167796381044807544181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14568223728508059743392241 10926167796381044807544181)
            ·
              refine ⟨1024328230910722950707267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10926167796381044807544181 1024328230910722950707267)
              ·
                refine ⟨1536492346366084426060901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024328230910722950707267 1536492346366084426060901)
                ·
                  refine ⟨288092314943640829886419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536492346366084426060901 288092314943640829886419)
                  ·
                    refine ⟨432138472415461244829629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288092314943640829886419 432138472415461244829629)
                    ·
                      refine ⟨162051927155797966811111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432138472415461244829629 162051927155797966811111)
                      ·
                        rfl

theorem cell23_315595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 3].length) (baseStart_315595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315595 prefixEnd_315595 := by exact prefixLift 315595
  have htrace : WordTrace (prefixWord ++ tailWord_315595) baseStart_315595 baseEnd_315595 := by
    simpa [prefixWord, tailWord_315595, baseEnd_315595] using wordTrace_append hprefix tailTrace_315595
  have hstable : (prefixWord ++ tailWord_315595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315595).length < 2 ^ (prefixWord ++ tailWord_315595).sum := by decide
  have hdescent : baseEnd_315595 < baseStart_315595 := by decide
  rcases family_descends (prefixWord ++ tailWord_315595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315596 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_315596 : Nat := 118140960795 + 315596 * 2 ^ 59
def prefixEnd_315596 : Nat := 4983230072969 + 3 ^ 40 * 315596 * 2
def baseEnd_315596 : Nat := 162052440636452462898607

theorem tailTrace_315596 : CollatzResearch.WordTrace tailWord_315596 prefixEnd_315596 162052440636452462898607 := by
  unfold tailWord_315596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755365882328533175375321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7673821176438044233833761 5755365882328533175375321)
  ·
    refine ⟨4316524411746399881531491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5755365882328533175375321 4316524411746399881531491)
    ·
      refine ⟨6474786617619599822297237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316524411746399881531491 6474786617619599822297237)
      ·
        refine ⟨303505622700918741670183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6474786617619599822297237 303505622700918741670183)
        ·
          refine ⟨455258434051378112505275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303505622700918741670183 455258434051378112505275)
          ·
            refine ⟨682887651077067168757913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455258434051378112505275 682887651077067168757913)
            ·
              refine ⟨512165738307800376568435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682887651077067168757913 512165738307800376568435)
              ·
                refine ⟨768248607461700564852653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512165738307800376568435 768248607461700564852653)
                ·
                  refine ⟨288093227798137711819745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768248607461700564852653 288093227798137711819745)
                  ·
                    refine ⟨216069920848603283864809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288093227798137711819745 216069920848603283864809)
                    ·
                      refine ⟨162052440636452462898607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216069920848603283864809 162052440636452462898607)
                      ·
                        rfl

theorem cell23_315596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_315596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315596 prefixEnd_315596 := by exact prefixLift 315596
  have htrace : WordTrace (prefixWord ++ tailWord_315596) baseStart_315596 baseEnd_315596 := by
    simpa [prefixWord, tailWord_315596, baseEnd_315596] using wordTrace_append hprefix tailTrace_315596
  have hstable : (prefixWord ++ tailWord_315596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315596).length < 2 ^ (prefixWord ++ tailWord_315596).sum := by decide
  have hdescent : baseEnd_315596 < baseStart_315596 := by decide
  rcases family_descends (prefixWord ++ tailWord_315596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315606 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_315606 : Nat := 118140960795 + 315606 * 2 ^ 59
def prefixEnd_315606 : Nat := 4983230072969 + 3 ^ 40 * 315606 * 2
def baseEnd_315606 : Nat := 54019191814332474591187

theorem tailTrace_315606 : CollatzResearch.WordTrace tailWord_315606 prefixEnd_315606 54019191814332474591187 := by
  unfold tailWord_315606
  simp only [CollatzResearch.WordTrace]
  refine ⟨719443530913802378663417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7674064329747225372409781 719443530913802378663417)
  ·
    refine ⟨539582648185351783997563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 719443530913802378663417 539582648185351783997563)
    ·
      refine ⟨809373972278027675996345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 539582648185351783997563 809373972278027675996345)
      ·
        refine ⟨607030479208520756997259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809373972278027675996345 607030479208520756997259)
        ·
          refine ⟨910545718812781135495889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607030479208520756997259 910545718812781135495889)
          ·
            refine ⟨682909289109585851621917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910545718812781135495889 682909289109585851621917)
            ·
              refine ⟨256090983416094694358219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682909289109585851621917 256090983416094694358219)
              ·
                refine ⟨384136475124142041537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256090983416094694358219 384136475124142041537329)
                ·
                  refine ⟨288102356343106531152997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384136475124142041537329 288102356343106531152997)
                  ·
                    refine ⟨54019191814332474591187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288102356343106531152997 54019191814332474591187)
                    ·
                      rfl

theorem cell23_315606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_315606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315606 prefixEnd_315606 := by exact prefixLift 315606
  have htrace : WordTrace (prefixWord ++ tailWord_315606) baseStart_315606 baseEnd_315606 := by
    simpa [prefixWord, tailWord_315606, baseEnd_315606] using wordTrace_append hprefix tailTrace_315606
  have hstable : (prefixWord ++ tailWord_315606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315606).length < 2 ^ (prefixWord ++ tailWord_315606).sum := by decide
  have hdescent : baseEnd_315606 < baseStart_315606 := by decide
  rcases family_descends (prefixWord ++ tailWord_315606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315619 : List Nat := [1, 1, 1, 8, 2, 1, 2, 7]
def baseStart_315619 : Nat := 118140960795 + 315619 * 2 ^ 59
def prefixEnd_315619 : Nat := 4983230072969 + 3 ^ 40 * 315619 * 2
def baseEnd_315619 : Nat := 6002379655240958255963

theorem tailTrace_315619 : CollatzResearch.WordTrace tailWord_315619 prefixEnd_315619 6002379655240958255963 := by
  unfold tailWord_315619
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511570643573741278837911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7674380429049160852558607 11511570643573741278837911)
  ·
    refine ⟨17267355965360611918256867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11511570643573741278837911 17267355965360611918256867)
    ·
      refine ⟨25901033948040917877385301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17267355965360611918256867 25901033948040917877385301)
      ·
        refine ⟨303527741578604506375609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 25901033948040917877385301 303527741578604506375609)
        ·
          refine ⟨227645806183953379781707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303527741578604506375609 227645806183953379781707)
          ·
            refine ⟨341468709275930069672561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227645806183953379781707 341468709275930069672561)
            ·
              refine ⟨256101531956947552254421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341468709275930069672561 256101531956947552254421)
              ·
                refine ⟨6002379655240958255963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 256101531956947552254421 6002379655240958255963)
                ·
                  rfl

theorem cell23_315619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 7].length) (baseStart_315619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315619 prefixEnd_315619 := by exact prefixLift 315619
  have htrace : WordTrace (prefixWord ++ tailWord_315619) baseStart_315619 baseEnd_315619 := by
    simpa [prefixWord, tailWord_315619, baseEnd_315619] using wordTrace_append hprefix tailTrace_315619
  have hstable : (prefixWord ++ tailWord_315619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315619).length < 2 ^ (prefixWord ++ tailWord_315619).sum := by decide
  have hdescent : baseEnd_315619 < baseStart_315619 := by decide
  rcases family_descends (prefixWord ++ tailWord_315619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315635 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 3, 4, 2]
def baseStart_315635 : Nat := 118140960795 + 315635 * 2 ^ 59
def prefixEnd_315635 : Nat := 4983230072969 + 3 ^ 40 * 315635 * 2
def baseEnd_315635 : Nat := 162072466381977810310927

theorem tailTrace_315635 : CollatzResearch.WordTrace tailWord_315635 prefixEnd_315635 162072466381977810310927 := by
  unfold tailWord_315635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512154211515776011420359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7674769474343850674280239 11512154211515776011420359)
  ·
    refine ⟨17268231317273664017130539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11512154211515776011420359 17268231317273664017130539)
    ·
      refine ⟨25902346975910496025695809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17268231317273664017130539 25902346975910496025695809)
      ·
        refine ⟨19426760231932872019271857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25902346975910496025695809 19426760231932872019271857)
        ·
          refine ⟨14570070173949654014453893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19426760231932872019271857 14570070173949654014453893)
          ·
            refine ⟨2731888157615560127710105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14570070173949654014453893 2731888157615560127710105)
            ·
              refine ⟨2048916118211670095782579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731888157615560127710105 2048916118211670095782579)
              ·
                refine ⟨3073374177317505143673869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048916118211670095782579 3073374177317505143673869)
                ·
                  refine ⟨1152515316494064428877701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3073374177317505143673869 1152515316494064428877701)
                  ·
                    refine ⟨216096621842637080414569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152515316494064428877701 216096621842637080414569)
                    ·
                      refine ⟨162072466381977810310927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216096621842637080414569 162072466381977810310927)
                      ·
                        rfl

theorem cell23_315635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4, 2].length) (baseStart_315635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315635 prefixEnd_315635 := by exact prefixLift 315635
  have htrace : WordTrace (prefixWord ++ tailWord_315635) baseStart_315635 baseEnd_315635 := by
    simpa [prefixWord, tailWord_315635, baseEnd_315635] using wordTrace_append hprefix tailTrace_315635
  have hstable : (prefixWord ++ tailWord_315635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315635).length < 2 ^ (prefixWord ++ tailWord_315635).sum := by decide
  have hdescent : baseEnd_315635 < baseStart_315635 := by decide
  rcases family_descends (prefixWord ++ tailWord_315635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315648 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_315648 : Nat := 118140960795 + 315648 * 2 ^ 59
def prefixEnd_315648 : Nat := 4983230072969 + 3 ^ 40 * 315648 * 2
def baseEnd_315648 : Nat := 162079141630486259448367

theorem tailTrace_315648 : CollatzResearch.WordTrace tailWord_315648 prefixEnd_315648 162079141630486259448367 := by
  unfold tailWord_315648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756314180234339615821799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7675085573645786154429065 5756314180234339615821799)
  ·
    refine ⟨8634471270351509423732699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5756314180234339615821799 8634471270351509423732699)
    ·
      refine ⟨12951706905527264135599049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8634471270351509423732699 12951706905527264135599049)
      ·
        refine ⟨9713780179145448101699287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12951706905527264135599049 9713780179145448101699287)
        ·
          refine ⟨14570670268718172152548931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9713780179145448101699287 14570670268718172152548931)
          ·
            refine ⟨21856005403077258228823397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14570670268718172152548931 21856005403077258228823397)
            ·
              refine ⟨4098001013076985917904387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21856005403077258228823397 4098001013076985917904387)
              ·
                refine ⟨6147001519615478876856581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098001013076985917904387 6147001519615478876856581)
                ·
                  refine ⟨1152562784927902289410609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6147001519615478876856581 1152562784927902289410609)
                  ·
                    refine ⟨864422088695926717057957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1152562784927902289410609 864422088695926717057957)
                    ·
                      refine ⟨162079141630486259448367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 864422088695926717057957 162079141630486259448367)
                      ·
                        rfl

theorem cell23_315648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_315648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315648 prefixEnd_315648 := by exact prefixLift 315648
  have htrace : WordTrace (prefixWord ++ tailWord_315648) baseStart_315648 baseEnd_315648 := by
    simpa [prefixWord, tailWord_315648, baseEnd_315648] using wordTrace_append hprefix tailTrace_315648
  have hstable : (prefixWord ++ tailWord_315648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315648).length < 2 ^ (prefixWord ++ tailWord_315648).sum := by decide
  have hdescent : baseEnd_315648 < baseStart_315648 := by decide
  rcases family_descends (prefixWord ++ tailWord_315648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315812 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_315812 : Nat := 118140960795 + 315812 * 2 ^ 59
def prefixEnd_315812 : Nat := 4983230072969 + 3 ^ 40 * 315812 * 2
def baseEnd_315812 : Nat := 54054450819274539265871

theorem tailTrace_315812 : CollatzResearch.WordTrace tailWord_315812 prefixEnd_315812 54054450819274539265871 := by
  unfold tailWord_315812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759304965937267620306845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7679073287916356827075793 5759304965937267620306845)
  ·
    refine ⟨2159739362226475357615067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5759304965937267620306845 2159739362226475357615067)
    ·
      refine ⟨3239609043339713036422601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2159739362226475357615067 3239609043339713036422601)
      ·
        refine ⟨2429706782504784777316951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239609043339713036422601 2429706782504784777316951)
        ·
          refine ⟨3644560173757177165975427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429706782504784777316951 3644560173757177165975427)
          ·
            refine ⟨5466840260635765748963141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644560173757177165975427 5466840260635765748963141)
            ·
              refine ⟨1025032548869206077930589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5466840260635765748963141 1025032548869206077930589)
              ·
                refine ⟨384387205825952279223971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1025032548869206077930589 384387205825952279223971)
                ·
                  refine ⟨576580808738928418835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384387205825952279223971 576580808738928418835957)
                  ·
                    refine ⟨54054450819274539265871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 576580808738928418835957 54054450819274539265871)
                    ·
                      rfl

theorem cell23_315812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_315812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315812 prefixEnd_315812 := by exact prefixLift 315812
  have htrace : WordTrace (prefixWord ++ tailWord_315812) baseStart_315812 baseEnd_315812 := by
    simpa [prefixWord, tailWord_315812, baseEnd_315812] using wordTrace_append hprefix tailTrace_315812
  have hstable : (prefixWord ++ tailWord_315812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315812).length < 2 ^ (prefixWord ++ tailWord_315812).sum := by decide
  have hdescent : baseEnd_315812 < baseStart_315812 := by decide
  rcases family_descends (prefixWord ++ tailWord_315812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315845 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_315845 : Nat := 118140960795 + 315845 * 2 ^ 59
def prefixEnd_315845 : Nat := 4983230072969 + 3 ^ 40 * 315845 * 2
def baseEnd_315845 : Nat := 162180297319421988684961

theorem tailTrace_315845 : CollatzResearch.WordTrace tailWord_315845 prefixEnd_315845 162180297319421988684961 := by
  unfold tailWord_315845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519813540754981876564989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7679875693836654584376659 11519813540754981876564989)
  ·
    refine ⟨4319930077783118203711871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11519813540754981876564989 4319930077783118203711871)
    ·
      refine ⟨6479895116674677305567807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4319930077783118203711871 6479895116674677305567807)
      ·
        refine ⟨9719842675012015958351711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6479895116674677305567807 9719842675012015958351711)
        ·
          refine ⟨14579764012518023937527567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9719842675012015958351711 14579764012518023937527567)
          ·
            refine ⟨21869646018777035906291351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14579764012518023937527567 21869646018777035906291351)
            ·
              refine ⟨32804469028165553859437027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21869646018777035906291351 32804469028165553859437027)
              ·
                refine ⟨49206703542248330789155541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32804469028165553859437027 49206703542248330789155541)
                ·
                  refine ⟨1153282114271445252870833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49206703542248330789155541 1153282114271445252870833)
                  ·
                    refine ⟨864961585703583939653125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153282114271445252870833 864961585703583939653125)
                    ·
                      refine ⟨162180297319421988684961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 864961585703583939653125 162180297319421988684961)
                      ·
                        rfl

theorem cell23_315845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_315845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315845 prefixEnd_315845 := by exact prefixLift 315845
  have htrace : WordTrace (prefixWord ++ tailWord_315845) baseStart_315845 baseEnd_315845 := by
    simpa [prefixWord, tailWord_315845, baseEnd_315845] using wordTrace_append hprefix tailTrace_315845
  have hstable : (prefixWord ++ tailWord_315845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315845).length < 2 ^ (prefixWord ++ tailWord_315845).sum := by decide
  have hdescent : baseEnd_315845 < baseStart_315845 := by decide
  rcases family_descends (prefixWord ++ tailWord_315845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315849 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 3, 2, 2]
def baseStart_315849 : Nat := 118140960795 + 315849 * 2 ^ 59
def prefixEnd_315849 : Nat := 4983230072969 + 3 ^ 40 * 315849 * 2
def baseEnd_315849 : Nat := 162182351242039973034943

theorem tailTrace_315849 : CollatzResearch.WordTrace tailWord_315849 prefixEnd_315849 162182351242039973034943 := by
  unfold tailWord_315849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11519959432740490559710601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7679972955160327039807067 11519959432740490559710601)
  ·
    refine ⟨8639969574555367919782951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11519959432740490559710601 8639969574555367919782951)
    ·
      refine ⟨12959954361833051879674427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639969574555367919782951 12959954361833051879674427)
      ·
        refine ⟨19439931542749577819511641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959954361833051879674427 19439931542749577819511641)
        ·
          refine ⟨14579948657062183364633731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19439931542749577819511641 14579948657062183364633731)
          ·
            refine ⟨21869922985593275046950597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14579948657062183364633731 21869922985593275046950597)
            ·
              refine ⟨4100610559798739071303237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21869922985593275046950597 4100610559798739071303237)
              ·
                refine ⟨768864479962263575869357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4100610559798739071303237 768864479962263575869357)
                ·
                  refine ⟨288324179985848840951009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 768864479962263575869357 288324179985848840951009)
                  ·
                    refine ⟨216243134989386630713257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288324179985848840951009 216243134989386630713257)
                    ·
                      refine ⟨162182351242039973034943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216243134989386630713257 162182351242039973034943)
                      ·
                        rfl

theorem cell23_315849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2, 2].length) (baseStart_315849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315849 prefixEnd_315849 := by exact prefixLift 315849
  have htrace : WordTrace (prefixWord ++ tailWord_315849) baseStart_315849 baseEnd_315849 := by
    simpa [prefixWord, tailWord_315849, baseEnd_315849] using wordTrace_append hprefix tailTrace_315849
  have hstable : (prefixWord ++ tailWord_315849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315849).length < 2 ^ (prefixWord ++ tailWord_315849).sum := by decide
  have hdescent : baseEnd_315849 < baseStart_315849 := by decide
  rcases family_descends (prefixWord ++ tailWord_315849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315877 : List Nat := [1, 3, 1, 5, 3, 1, 2, 2, 1, 1, 3]
def baseStart_315877 : Nat := 118140960795 + 315877 * 2 ^ 59
def prefixEnd_315877 : Nat := 4983230072969 + 3 ^ 40 * 315877 * 2
def baseEnd_315877 : Nat := 162196728700365863484815

theorem tailTrace_315877 : CollatzResearch.WordTrace tailWord_315877 prefixEnd_315877 162196728700365863484815 := by
  unfold tailWord_315877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11520980676639051341729885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7680653784426034227819923 11520980676639051341729885)
  ·
    refine ⟨4320367753739644253148707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11520980676639051341729885 4320367753739644253148707)
    ·
      refine ⟨6480551630609466379723061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320367753739644253148707 6480551630609466379723061)
      ·
        refine ⟨607551715369637473099037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6480551630609466379723061 607551715369637473099037)
        ·
          refine ⟨227831893263614052412139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 607551715369637473099037 227831893263614052412139)
          ·
            refine ⟨341747839895421078618209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227831893263614052412139 341747839895421078618209)
            ·
              refine ⟨256310879921565808963657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341747839895421078618209 256310879921565808963657)
              ·
                refine ⟨192233159941174356722743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256310879921565808963657 192233159941174356722743)
                ·
                  refine ⟨288349739911761535084115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192233159941174356722743 288349739911761535084115)
                  ·
                    refine ⟨432524609867642302626173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288349739911761535084115 432524609867642302626173)
                    ·
                      refine ⟨162196728700365863484815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432524609867642302626173 162196728700365863484815)
                      ·
                        rfl

theorem cell23_315877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_315877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315877 prefixEnd_315877 := by exact prefixLift 315877
  have htrace : WordTrace (prefixWord ++ tailWord_315877) baseStart_315877 baseEnd_315877 := by
    simpa [prefixWord, tailWord_315877, baseEnd_315877] using wordTrace_append hprefix tailTrace_315877
  have hstable : (prefixWord ++ tailWord_315877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315877).length < 2 ^ (prefixWord ++ tailWord_315877).sum := by decide
  have hdescent : baseEnd_315877 < baseStart_315877 := by decide
  rcases family_descends (prefixWord ++ tailWord_315877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315906 : List Nat := [3, 4, 1, 2, 2, 1, 3, 7]
def baseStart_315906 : Nat := 118140960795 + 315906 * 2 ^ 59
def prefixEnd_315906 : Nat := 4983230072969 + 3 ^ 40 * 315906 * 2
def baseEnd_315906 : Nat := 6007837764420231482303

theorem tailTrace_315906 : CollatzResearch.WordTrace tailWord_315906 prefixEnd_315906 6007837764420231482303 := by
  unfold tailWord_315906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880509598383497323633893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7681358929022659529690381 2880509598383497323633893)
  ·
    refine ⟨540095549696905748181355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2880509598383497323633893 540095549696905748181355)
    ·
      refine ⟨810143324545358622272033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540095549696905748181355 810143324545358622272033)
      ·
        refine ⟨607607493409018966704025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 810143324545358622272033 607607493409018966704025)
        ·
          refine ⟨455705620056764225028019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607607493409018966704025 455705620056764225028019)
          ·
            refine ⟨683558430085146337542029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455705620056764225028019 683558430085146337542029)
            ·
              refine ⟨256334411281929876578261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683558430085146337542029 256334411281929876578261)
              ·
                refine ⟨6007837764420231482303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 256334411281929876578261 6007837764420231482303)
                ·
                  rfl

theorem cell23_315906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_315906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315906 prefixEnd_315906 := by exact prefixLift 315906
  have htrace : WordTrace (prefixWord ++ tailWord_315906) baseStart_315906 baseEnd_315906 := by
    simpa [prefixWord, tailWord_315906, baseEnd_315906] using wordTrace_append hprefix tailTrace_315906
  have hstable : (prefixWord ++ tailWord_315906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315906).length < 2 ^ (prefixWord ++ tailWord_315906).sum := by decide
  have hdescent : baseEnd_315906 < baseStart_315906 := by decide
  rcases family_descends (prefixWord ++ tailWord_315906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315909 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 3, 3, 2]
def baseStart_315909 : Nat := 118140960795 + 315909 * 2 ^ 59
def prefixEnd_315909 : Nat := 4983230072969 + 3 ^ 40 * 315909 * 2
def baseEnd_315909 : Nat := 162213160081309738284667

theorem tailTrace_315909 : CollatzResearch.WordTrace tailWord_315909 prefixEnd_315909 162213160081309738284667 := by
  unfold tailWord_315909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522147812523120806894781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7681431875015413871263187 11522147812523120806894781)
  ·
    refine ⟨4320805429696170302585543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11522147812523120806894781 4320805429696170302585543)
    ·
      refine ⟨6481208144544255453878315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4320805429696170302585543 6481208144544255453878315)
      ·
        refine ⟨9721812216816383180817473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481208144544255453878315 9721812216816383180817473)
        ·
          refine ⟨7291359162612287385613105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9721812216816383180817473 7291359162612287385613105)
          ·
            refine ⟨5468519371959215539209829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7291359162612287385613105 5468519371959215539209829)
            ·
              refine ⟨1025347382242352913601843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5468519371959215539209829 1025347382242352913601843)
              ·
                refine ⟨1538021073363529370402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025347382242352913601843 1538021073363529370402765)
                ·
                  refine ⟨576757902511323513901037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1538021073363529370402765 576757902511323513901037)
                  ·
                    refine ⟨216284213441746317712889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576757902511323513901037 216284213441746317712889)
                    ·
                      refine ⟨162213160081309738284667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216284213441746317712889 162213160081309738284667)
                      ·
                        rfl

theorem cell23_315909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_315909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315909 prefixEnd_315909 := by exact prefixLift 315909
  have htrace : WordTrace (prefixWord ++ tailWord_315909) baseStart_315909 baseEnd_315909 := by
    simpa [prefixWord, tailWord_315909, baseEnd_315909] using wordTrace_append hprefix tailTrace_315909
  have hstable : (prefixWord ++ tailWord_315909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315909).length < 2 ^ (prefixWord ++ tailWord_315909).sum := by decide
  have hdescent : baseEnd_315909 < baseStart_315909 := by decide
  rcases family_descends (prefixWord ++ tailWord_315909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315917 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_315917 : Nat := 118140960795 + 315917 * 2 ^ 59
def prefixEnd_315917 : Nat := 4983230072969 + 3 ^ 40 * 315917 * 2
def baseEnd_315917 : Nat := 162217267926545706984631

theorem tailTrace_315917 : CollatzResearch.WordTrace tailWord_315917 prefixEnd_315917 162217267926545706984631 := by
  unfold tailWord_315917
  simp only [CollatzResearch.WordTrace]
  refine ⟨11522439596494138173186005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7681626397662758782124003 11522439596494138173186005)
  ·
    refine ⟨270057178042831363434047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11522439596494138173186005 270057178042831363434047)
    ·
      refine ⟨405085767064247045151071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270057178042831363434047 405085767064247045151071)
      ·
        refine ⟨607628650596370567726607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405085767064247045151071 607628650596370567726607)
        ·
          refine ⟨911442975894555851589911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607628650596370567726607 911442975894555851589911)
          ·
            refine ⟨1367164463841833777384867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911442975894555851589911 1367164463841833777384867)
            ·
              refine ⟨2050746695762750666077301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367164463841833777384867 2050746695762750666077301)
              ·
                refine ⟨192257502727757874944747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2050746695762750666077301 192257502727757874944747)
                ·
                  refine ⟨288386254091636812417121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192257502727757874944747 288386254091636812417121)
                  ·
                    refine ⟨216289690568727609312841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288386254091636812417121 216289690568727609312841)
                    ·
                      refine ⟨162217267926545706984631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216289690568727609312841 162217267926545706984631)
                      ·
                        rfl

theorem cell23_315917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_315917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315917 prefixEnd_315917 := by exact prefixLift 315917
  have htrace : WordTrace (prefixWord ++ tailWord_315917) baseStart_315917 baseEnd_315917 := by
    simpa [prefixWord, tailWord_315917, baseEnd_315917] using wordTrace_append hprefix tailTrace_315917
  have hstable : (prefixWord ++ tailWord_315917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315917).length < 2 ^ (prefixWord ++ tailWord_315917).sum := by decide
  have hdescent : baseEnd_315917 < baseStart_315917 := by decide
  rcases family_descends (prefixWord ++ tailWord_315917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315932 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_315932 : Nat := 118140960795 + 315932 * 2 ^ 59
def prefixEnd_315932 : Nat := 4983230072969 + 3 ^ 40 * 315932 * 2
def baseEnd_315932 : Nat := 54074990045454382765687

theorem tailTrace_315932 : CollatzResearch.WordTrace tailWord_315932 prefixEnd_315932 54074990045454382765687 := by
  unfold tailWord_315932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761493345719897867491025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7681991127626530489988033 5761493345719897867491025)
  ·
    refine ⟨4321120009289923400618269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5761493345719897867491025 4321120009289923400618269)
    ·
      refine ⟨1620420003483721275231851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4321120009289923400618269 1620420003483721275231851)
      ·
        refine ⟨2430630005225581912847777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620420003483721275231851 2430630005225581912847777)
        ·
          refine ⟨1822972503919186434635833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430630005225581912847777 1822972503919186434635833)
          ·
            refine ⟨1367229377939389825976875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822972503919186434635833 1367229377939389825976875)
            ·
              refine ⟨2050844066909084738965313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367229377939389825976875 2050844066909084738965313)
              ·
                refine ⟨1538133050181813554223985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050844066909084738965313 1538133050181813554223985)
                ·
                  refine ⟨1153599787636360165667989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538133050181813554223985 1153599787636360165667989)
                  ·
                    refine ⟨54074990045454382765687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1153599787636360165667989 54074990045454382765687)
                    ·
                      rfl

theorem cell23_315932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_315932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315932 prefixEnd_315932 := by exact prefixLift 315932
  have htrace : WordTrace (prefixWord ++ tailWord_315932) baseStart_315932 baseEnd_315932 := by
    simpa [prefixWord, tailWord_315932, baseEnd_315932] using wordTrace_append hprefix tailTrace_315932
  have hstable : (prefixWord ++ tailWord_315932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315932).length < 2 ^ (prefixWord ++ tailWord_315932).sum := by decide
  have hdescent : baseEnd_315932 < baseStart_315932 := by decide
  rcases family_descends (prefixWord ++ tailWord_315932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315933 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_315933 : Nat := 118140960795 + 315933 * 2 ^ 59
def prefixEnd_315933 : Nat := 4983230072969 + 3 ^ 40 * 315933 * 2
def baseEnd_315933 : Nat := 162225483617017644384557

theorem tailTrace_315933 : CollatzResearch.WordTrace tailWord_315933 prefixEnd_315933 162225483617017644384557 := by
  unfold tailWord_315933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11523023164436172905768453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7682015442957448603845635 11523023164436172905768453)
  ·
    refine ⟨2160566843331782419831585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11523023164436172905768453 2160566843331782419831585)
    ·
      refine ⟨1620425132498836814873689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2160566843331782419831585 1620425132498836814873689)
      ·
        refine ⟨1215318849374127611155267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620425132498836814873689 1215318849374127611155267)
        ·
          refine ⟨1822978274061191416732901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215318849374127611155267 1822978274061191416732901)
          ·
            refine ⟨341808426386473390637419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1822978274061191416732901 341808426386473390637419)
            ·
              refine ⟨512712639579710085956129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341808426386473390637419 512712639579710085956129)
              ·
                refine ⟨384534479684782564467097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512712639579710085956129 384534479684782564467097)
                ·
                  refine ⟨288400859763586923350323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384534479684782564467097 288400859763586923350323)
                  ·
                    refine ⟨432601289645380385025485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288400859763586923350323 432601289645380385025485)
                    ·
                      refine ⟨162225483617017644384557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432601289645380385025485 162225483617017644384557)
                      ·
                        rfl

theorem cell23_315933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_315933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315933 prefixEnd_315933 := by exact prefixLift 315933
  have htrace : WordTrace (prefixWord ++ tailWord_315933) baseStart_315933 baseEnd_315933 := by
    simpa [prefixWord, tailWord_315933, baseEnd_315933] using wordTrace_append hprefix tailTrace_315933
  have hstable : (prefixWord ++ tailWord_315933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315933).length < 2 ^ (prefixWord ++ tailWord_315933).sum := by decide
  have hdescent : baseEnd_315933 < baseStart_315933 := by decide
  rcases family_descends (prefixWord ++ tailWord_315933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315950 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_315950 : Nat := 118140960795 + 315950 * 2 ^ 59
def prefixEnd_315950 : Nat := 4983230072969 + 3 ^ 40 * 315950 * 2
def baseEnd_315950 : Nat := 162234212788144077871979

theorem tailTrace_315950 : CollatzResearch.WordTrace tailWord_315950 prefixEnd_315950 162234212788144077871979 := by
  unfold tailWord_315950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440455400671823101142163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7682428803583056539424869 1440455400671823101142163)
  ·
    refine ⟨2160683101007734651713245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440455400671823101142163 2160683101007734651713245)
    ·
      refine ⟨810256162877900494392467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2160683101007734651713245 810256162877900494392467)
      ·
        refine ⟨1215384244316850741588701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810256162877900494392467 1215384244316850741588701)
        ·
          refine ⟨455769091618819028095763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215384244316850741588701 455769091618819028095763)
          ·
            refine ⟨683653637428228542143645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455769091618819028095763 683653637428228542143645)
            ·
              refine ⟨256370114035585703303867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683653637428228542143645 256370114035585703303867)
              ·
                refine ⟨384555171053378554955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256370114035585703303867 384555171053378554955801)
                ·
                  refine ⟨288416378290033916216851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384555171053378554955801 288416378290033916216851)
                  ·
                    refine ⟨432624567435050874325277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288416378290033916216851 432624567435050874325277)
                    ·
                      refine ⟨162234212788144077871979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432624567435050874325277 162234212788144077871979)
                      ·
                        rfl

theorem cell23_315950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_315950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315950 prefixEnd_315950 := by exact prefixLift 315950
  have htrace : WordTrace (prefixWord ++ tailWord_315950) baseStart_315950 baseEnd_315950 := by
    simpa [prefixWord, tailWord_315950, baseEnd_315950] using wordTrace_append hprefix tailTrace_315950
  have hstable : (prefixWord ++ tailWord_315950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315950).length < 2 ^ (prefixWord ++ tailWord_315950).sum := by decide
  have hdescent : baseEnd_315950 < baseStart_315950 := by decide
  rcases family_descends (prefixWord ++ tailWord_315950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315952 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_315952 : Nat := 118140960795 + 315952 * 2 ^ 59
def prefixEnd_315952 : Nat := 4983230072969 + 3 ^ 40 * 315952 * 2
def baseEnd_315952 : Nat := 162235239749453070046969

theorem tailTrace_315952 : CollatzResearch.WordTrace tailWord_315952 prefixEnd_315952 162235239749453070046969 := by
  unfold tailWord_315952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761858075683669575355055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7682477434244892767140073 5761858075683669575355055)
  ·
    refine ⟨8642787113525504363032583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5761858075683669575355055 8642787113525504363032583)
    ·
      refine ⟨12964180670288256544548875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8642787113525504363032583 12964180670288256544548875)
      ·
        refine ⟨19446271005432384816823313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12964180670288256544548875 19446271005432384816823313)
        ·
          refine ⟨14584703254074288612617485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19446271005432384816823313 14584703254074288612617485)
          ·
            refine ⟨5469263720277858229731557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14584703254074288612617485 5469263720277858229731557)
            ·
              refine ⟨1025486947552098418074667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5469263720277858229731557 1025486947552098418074667)
              ·
                refine ⟨1538230421328147627112001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025486947552098418074667 1538230421328147627112001)
                ·
                  refine ⟨1153672815996110720334001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538230421328147627112001 1153672815996110720334001)
                  ·
                    refine ⟨865254611997083040250501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153672815996110720334001 865254611997083040250501)
                    ·
                      refine ⟨162235239749453070046969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 865254611997083040250501 162235239749453070046969)
                      ·
                        rfl

theorem cell23_315952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_315952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315952 prefixEnd_315952 := by exact prefixLift 315952
  have htrace : WordTrace (prefixWord ++ tailWord_315952) baseStart_315952 baseEnd_315952 := by
    simpa [prefixWord, tailWord_315952, baseEnd_315952] using wordTrace_append hprefix tailTrace_315952
  have hstable : (prefixWord ++ tailWord_315952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315952).length < 2 ^ (prefixWord ++ tailWord_315952).sum := by decide
  have hdescent : baseEnd_315952 < baseStart_315952 := by decide
  rcases family_descends (prefixWord ++ tailWord_315952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315962 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_315962 : Nat := 118140960795 + 315962 * 2 ^ 59
def prefixEnd_315962 : Nat := 4983230072969 + 3 ^ 40 * 315962 * 2
def baseEnd_315962 : Nat := 18026708283999781213547

theorem tailTrace_315962 : CollatzResearch.WordTrace tailWord_315962 prefixEnd_315962 18026708283999781213547 := by
  unfold tailWord_315962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881020220332777714643535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7682720587554073905716093 2881020220332777714643535)
  ·
    refine ⟨4321530330499166571965303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2881020220332777714643535 4321530330499166571965303)
    ·
      refine ⟨6482295495748749857947955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321530330499166571965303 6482295495748749857947955)
      ·
        refine ⟨9723443243623124786921933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482295495748749857947955 9723443243623124786921933)
        ·
          refine ⟨3646291216358671795095725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9723443243623124786921933 3646291216358671795095725)
          ·
            refine ⟨1367359206134501923160897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3646291216358671795095725 1367359206134501923160897)
            ·
              refine ⟨1025519404600876442370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367359206134501923160897 1025519404600876442370673)
              ·
                refine ⟨769139553450657331778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025519404600876442370673 769139553450657331778005)
                ·
                  refine ⟨18026708283999781213547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 769139553450657331778005 18026708283999781213547)
                  ·
                    rfl

theorem cell23_315962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_315962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315962 prefixEnd_315962 := by exact prefixLift 315962
  have htrace : WordTrace (prefixWord ++ tailWord_315962) baseStart_315962 baseEnd_315962 := by
    simpa [prefixWord, tailWord_315962, baseEnd_315962] using wordTrace_append hprefix tailTrace_315962
  have hstable : (prefixWord ++ tailWord_315962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315962).length < 2 ^ (prefixWord ++ tailWord_315962).sum := by decide
  have hdescent : baseEnd_315962 < baseStart_315962 := by decide
  rcases family_descends (prefixWord ++ tailWord_315962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315979 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 5]
def baseStart_315979 : Nat := 118140960795 + 315979 * 2 ^ 59
def prefixEnd_315979 : Nat := 4983230072969 + 3 ^ 40 * 315979 * 2
def baseEnd_315979 : Nat := 18027678191902718267705

theorem tailTrace_315979 : CollatzResearch.WordTrace tailWord_315979 prefixEnd_315979 18027678191902718267705 := by
  unfold tailWord_315979
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524700922269522761942991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7683133948179681841295327 11524700922269522761942991)
  ·
    refine ⟨17287051383404284142914487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524700922269522761942991 17287051383404284142914487)
    ·
      refine ⟨25930577075106426214371731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17287051383404284142914487 25930577075106426214371731)
      ·
        refine ⟨38895865612659639321557597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25930577075106426214371731 38895865612659639321557597)
        ·
          refine ⟨14585949604747364745584099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38895865612659639321557597 14585949604747364745584099)
          ·
            refine ⟨21878924407121047118376149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585949604747364745584099 21878924407121047118376149)
            ·
              refine ⟨512787290791899541836941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21878924407121047118376149 512787290791899541836941)
              ·
                refine ⟨192295234046962328188853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512787290791899541836941 192295234046962328188853)
                ·
                  refine ⟨18027678191902718267705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192295234046962328188853 18027678191902718267705)
                  ·
                    rfl

theorem cell23_315979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 5].length) (baseStart_315979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315979 prefixEnd_315979 := by exact prefixLift 315979
  have htrace : WordTrace (prefixWord ++ tailWord_315979) baseStart_315979 baseEnd_315979 := by
    simpa [prefixWord, tailWord_315979, baseEnd_315979] using wordTrace_append hprefix tailTrace_315979
  have hstable : (prefixWord ++ tailWord_315979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315979).length < 2 ^ (prefixWord ++ tailWord_315979).sum := by decide
  have hdescent : baseEnd_315979 < baseStart_315979 := by decide
  rcases family_descends (prefixWord ++ tailWord_315979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315992 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_315992 : Nat := 118140960795 + 315992 * 2 ^ 59
def prefixEnd_315992 : Nat := 4983230072969 + 3 ^ 40 * 315992 * 2
def baseEnd_315992 : Nat := 54085259658544304515595

theorem tailTrace_315992 : CollatzResearch.WordTrace tailWord_315992 prefixEnd_315992 54085259658544304515595 := by
  unfold tailWord_315992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762587535611212991083115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683450047481617321444153 5762587535611212991083115)
  ·
    refine ⟨8643881303416819486624673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762587535611212991083115 8643881303416819486624673)
    ·
      refine ⟨6482910977562614614968505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643881303416819486624673 6482910977562614614968505)
      ·
        refine ⟨4862183233171960961226379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6482910977562614614968505 4862183233171960961226379)
        ·
          refine ⟨7293274849757941441839569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862183233171960961226379 7293274849757941441839569)
          ·
            refine ⟨5469956137318456081379677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293274849757941441839569 5469956137318456081379677)
            ·
              refine ⟨2051233551494421030517379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5469956137318456081379677 2051233551494421030517379)
              ·
                refine ⟨3076850327241631545776069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051233551494421030517379 3076850327241631545776069)
                ·
                  refine ⟨576909436357805914833013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3076850327241631545776069 576909436357805914833013)
                  ·
                    refine ⟨54085259658544304515595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 576909436357805914833013 54085259658544304515595)
                    ·
                      rfl

theorem cell23_315992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_315992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315992 prefixEnd_315992 := by exact prefixLift 315992
  have htrace : WordTrace (prefixWord ++ tailWord_315992) baseStart_315992 baseEnd_315992 := by
    simpa [prefixWord, tailWord_315992, baseEnd_315992] using wordTrace_append hprefix tailTrace_315992
  have hstable : (prefixWord ++ tailWord_315992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315992).length < 2 ^ (prefixWord ++ tailWord_315992).sum := by decide
  have hdescent : baseEnd_315992 < baseStart_315992 := by decide
  rcases family_descends (prefixWord ++ tailWord_315992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315996 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 7]
def baseStart_315996 : Nat := 118140960795 + 315996 * 2 ^ 59
def prefixEnd_315996 : Nat := 4983230072969 + 3 ^ 40 * 315996 * 2
def baseEnd_315996 : Nat := 18028648099805655321863

theorem tailTrace_315996 : CollatzResearch.WordTrace tailWord_315996 prefixEnd_315996 18028648099805655321863 := by
  unfold tailWord_315996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762660481603967332655921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683547308805289776874561 5762660481603967332655921)
  ·
    refine ⟨4321995361202975499491941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762660481603967332655921 4321995361202975499491941)
    ·
      refine ⟨810374130225557906154739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4321995361202975499491941 810374130225557906154739)
      ·
        refine ⟨1215561195338336859232109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810374130225557906154739 1215561195338336859232109)
        ·
          refine ⟨455835448251876322212041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215561195338336859232109 455835448251876322212041)
          ·
            refine ⟨341876586188907241659031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455835448251876322212041 341876586188907241659031)
            ·
              refine ⟨512814879283360862488547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341876586188907241659031 512814879283360862488547)
              ·
                refine ⟨769222318925041293732821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512814879283360862488547 769222318925041293732821)
                ·
                  refine ⟨18028648099805655321863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 769222318925041293732821 18028648099805655321863)
                  ·
                    rfl

theorem cell23_315996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_315996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_315996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_315996 prefixEnd_315996 := by exact prefixLift 315996
  have htrace : WordTrace (prefixWord ++ tailWord_315996) baseStart_315996 baseEnd_315996 := by
    simpa [prefixWord, tailWord_315996, baseEnd_315996] using wordTrace_append hprefix tailTrace_315996
  have hstable : (prefixWord ++ tailWord_315996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315996).length < 2 ^ (prefixWord ++ tailWord_315996).sum := by decide
  have hdescent : baseEnd_315996 < baseStart_315996 := by decide
  rcases family_descends (prefixWord ++ tailWord_315996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316012 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_316012 : Nat := 118140960795 + 316012 * 2 ^ 59
def prefixEnd_316012 : Nat := 4983230072969 + 3 ^ 40 * 316012 * 2
def baseEnd_316012 : Nat := 162266048588722835296693

theorem tailTrace_316012 : CollatzResearch.WordTrace tailWord_316012 prefixEnd_316012 162266048588722835296693 := by
  unfold tailWord_316012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762952265574984698947145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7683936354099979598596193 5762952265574984698947145)
  ·
    refine ⟨4322214199181238524210359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5762952265574984698947145 4322214199181238524210359)
    ·
      refine ⟨6483321298771857786315539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4322214199181238524210359 6483321298771857786315539)
      ·
        refine ⟨9724981948157786679473309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6483321298771857786315539 9724981948157786679473309)
        ·
          refine ⟨3646868230559170004802491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9724981948157786679473309 3646868230559170004802491)
          ·
            refine ⟨5470302345838755007203737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646868230559170004802491 5470302345838755007203737)
            ·
              refine ⟨4102726759379066255402803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5470302345838755007203737 4102726759379066255402803)
              ·
                refine ⟨6154090139068599383104205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102726759379066255402803 6154090139068599383104205)
                ·
                  refine ⟨2307783802150724768664077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154090139068599383104205 2307783802150724768664077)
                  ·
                    refine ⟨865418925806521788249029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307783802150724768664077 865418925806521788249029)
                    ·
                      refine ⟨162266048588722835296693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 865418925806521788249029 162266048588722835296693)
                      ·
                        rfl

theorem cell23_316012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_316012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316012 prefixEnd_316012 := by exact prefixLift 316012
  have htrace : WordTrace (prefixWord ++ tailWord_316012) baseStart_316012 baseEnd_316012 := by
    simpa [prefixWord, tailWord_316012, baseEnd_316012] using wordTrace_append hprefix tailTrace_316012
  have hstable : (prefixWord ++ tailWord_316012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316012).length < 2 ^ (prefixWord ++ tailWord_316012).sum := by decide
  have hdescent : baseEnd_316012 < baseStart_316012 := by decide
  rcases family_descends (prefixWord ++ tailWord_316012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316046 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_316046 : Nat := 118140960795 + 316046 * 2 ^ 59
def prefixEnd_316046 : Nat := 4983230072969 + 3 ^ 40 * 316046 * 2
def baseEnd_316046 : Nat := 162283506930975702271537

theorem tailTrace_316046 : CollatzResearch.WordTrace tailWord_316046 prefixEnd_316046 162283506930975702271537 := by
  unfold tailWord_316046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440893076628349150578999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7684763075351195469754661 1440893076628349150578999)
  ·
    refine ⟨2161339614942523725868499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1440893076628349150578999 2161339614942523725868499)
    ·
      refine ⟨3242009422413785588802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161339614942523725868499 3242009422413785588802749)
      ·
        refine ⟨1215753533405169595801031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3242009422413785588802749 1215753533405169595801031)
        ·
          refine ⟨1823630300107754393701547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215753533405169595801031 1823630300107754393701547)
          ·
            refine ⟨2735445450161631590552321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823630300107754393701547 2735445450161631590552321)
            ·
              refine ⟨2051584087621223692914241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735445450161631590552321 2051584087621223692914241)
              ·
                refine ⟨1538688065715917769685681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051584087621223692914241 1538688065715917769685681)
                ·
                  refine ⟨1154016049286938327264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538688065715917769685681 1154016049286938327264261)
                  ·
                    refine ⟨216378009241300936362049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154016049286938327264261 216378009241300936362049)
                    ·
                      refine ⟨162283506930975702271537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216378009241300936362049 162283506930975702271537)
                      ·
                        rfl

theorem cell23_316046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_316046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316046 prefixEnd_316046 := by exact prefixLift 316046
  have htrace : WordTrace (prefixWord ++ tailWord_316046) baseStart_316046 baseEnd_316046 := by
    simpa [prefixWord, tailWord_316046, baseEnd_316046] using wordTrace_append hprefix tailTrace_316046
  have hstable : (prefixWord ++ tailWord_316046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316046).length < 2 ^ (prefixWord ++ tailWord_316046).sum := by decide
  have hdescent : baseEnd_316046 < baseStart_316046 := by decide
  rcases family_descends (prefixWord ++ tailWord_316046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316113 : List Nat := [1, 2, 2, 1, 2, 3, 1, 6, 1, 1, 3]
def baseStart_316113 : Nat := 118140960795 + 316113 * 2 ^ 59
def prefixEnd_316113 : Nat := 4983230072969 + 3 ^ 40 * 316113 * 2
def baseEnd_316113 : Nat := 162317910134826940133729

theorem tailTrace_316113 : CollatzResearch.WordTrace tailWord_316113 prefixEnd_316113 162317910134826940133729 := by
  unfold tailWord_316113
  simp only [CollatzResearch.WordTrace]
  refine ⟨11529588303784063647320993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7686392202522709098213995 11529588303784063647320993)
  ·
    refine ⟨8647191227838047735490745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11529588303784063647320993 8647191227838047735490745)
    ·
      refine ⟨6485393420878535801618059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8647191227838047735490745 6485393420878535801618059)
      ·
        refine ⟨9728090131317803702427089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485393420878535801618059 9728090131317803702427089)
        ·
          refine ⟨7296067598488352776820317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9728090131317803702427089 7296067598488352776820317)
          ·
            refine ⟨2736025349433132291307619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7296067598488352776820317 2736025349433132291307619)
            ·
              refine ⟨4104038024149698436961429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736025349433132291307619 4104038024149698436961429)
              ·
                refine ⟨192376782382017114232567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4104038024149698436961429 192376782382017114232567)
                ·
                  refine ⟨288565173573025671348851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192376782382017114232567 288565173573025671348851)
                  ·
                    refine ⟨432847760359538507023277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288565173573025671348851 432847760359538507023277)
                    ·
                      refine ⟨162317910134826940133729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432847760359538507023277 162317910134826940133729)
                      ·
                        rfl

theorem cell23_316113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 1, 1, 3].length) (baseStart_316113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316113 prefixEnd_316113 := by exact prefixLift 316113
  have htrace : WordTrace (prefixWord ++ tailWord_316113) baseStart_316113 baseEnd_316113 := by
    simpa [prefixWord, tailWord_316113, baseEnd_316113] using wordTrace_append hprefix tailTrace_316113
  have hstable : (prefixWord ++ tailWord_316113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316113).length < 2 ^ (prefixWord ++ tailWord_316113).sum := by decide
  have hdescent : baseEnd_316113 < baseStart_316113 := by decide
  rcases family_descends (prefixWord ++ tailWord_316113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316146 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_316146 : Nat := 118140960795 + 316146 * 2 ^ 59
def prefixEnd_316146 : Nat := 4983230072969 + 3 ^ 40 * 316146 * 2
def baseEnd_316146 : Nat := 54111618332141770340359

theorem tailTrace_316146 : CollatzResearch.WordTrace tailWord_316146 prefixEnd_316146 54111618332141770340359 := by
  unfold tailWord_316146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882697978166127570818073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7687194608443006855514861 2882697978166127570818073)
  ·
    refine ⟨2162023483624595678113555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2882697978166127570818073 2162023483624595678113555)
    ·
      refine ⟨3243035225436893517170333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162023483624595678113555 3243035225436893517170333)
      ·
        refine ⟨1216138209538835068938875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3243035225436893517170333 1216138209538835068938875)
        ·
          refine ⟨1824207314308252603408313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216138209538835068938875 1824207314308252603408313)
          ·
            refine ⟨1368155485731189452556235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824207314308252603408313 1368155485731189452556235)
            ·
              refine ⟨2052233228596784178834353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368155485731189452556235 2052233228596784178834353)
              ·
                refine ⟨1539174921447588134125765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052233228596784178834353 1539174921447588134125765)
                ·
                  refine ⟨288595297771422775148581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539174921447588134125765 288595297771422775148581)
                  ·
                    refine ⟨54111618332141770340359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288595297771422775148581 54111618332141770340359)
                    ·
                      rfl

theorem cell23_316146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_316146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316146 prefixEnd_316146 := by exact prefixLift 316146
  have htrace : WordTrace (prefixWord ++ tailWord_316146) baseStart_316146 baseEnd_316146 := by
    simpa [prefixWord, tailWord_316146, baseEnd_316146] using wordTrace_append hprefix tailTrace_316146
  have hstable : (prefixWord ++ tailWord_316146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316146).length < 2 ^ (prefixWord ++ tailWord_316146).sum := by decide
  have hdescent : baseEnd_316146 < baseStart_316146 := by decide
  rcases family_descends (prefixWord ++ tailWord_316146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316156 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_316156 : Nat := 118140960795 + 316156 * 2 ^ 59
def prefixEnd_316156 : Nat := 4983230072969 + 3 ^ 40 * 316156 * 2
def baseEnd_316156 : Nat := 162339989802970271896031

theorem tailTrace_316156 : CollatzResearch.WordTrace tailWord_316156 prefixEnd_316156 162339989802970271896031 := by
  unfold tailWord_316156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765578321314140995568161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7687437761752187994090881 5765578321314140995568161)
  ·
    refine ⟨4324183740985605746676121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5765578321314140995568161 4324183740985605746676121)
    ·
      refine ⟨3243137805739204310007091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4324183740985605746676121 3243137805739204310007091)
      ·
        refine ⟨4864706708608806465010637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243137805739204310007091 4864706708608806465010637)
        ·
          refine ⟨1824265015728302424378989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4864706708608806465010637 1824265015728302424378989)
          ·
            refine ⟨684099380898113409142121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1824265015728302424378989 684099380898113409142121)
            ·
              refine ⟨513074535673585056856591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684099380898113409142121 513074535673585056856591)
              ·
                refine ⟨769611803510377585284887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513074535673585056856591 769611803510377585284887)
                ·
                  refine ⟨1154417705265566377927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769611803510377585284887 1154417705265566377927331)
                  ·
                    refine ⟨1731626557898349566890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154417705265566377927331 1731626557898349566890997)
                    ·
                      refine ⟨162339989802970271896031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1731626557898349566890997 162339989802970271896031)
                      ·
                        rfl

theorem cell23_316156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_316156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316156 prefixEnd_316156 := by exact prefixLift 316156
  have htrace : WordTrace (prefixWord ++ tailWord_316156) baseStart_316156 baseEnd_316156 := by
    simpa [prefixWord, tailWord_316156, baseEnd_316156] using wordTrace_append hprefix tailTrace_316156
  have hstable : (prefixWord ++ tailWord_316156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316156).length < 2 ^ (prefixWord ++ tailWord_316156).sum := by decide
  have hdescent : baseEnd_316156 < baseStart_316156 := by decide
  rcases family_descends (prefixWord ++ tailWord_316156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316186 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_316186 : Nat := 118140960795 + 316186 * 2 ^ 59
def prefixEnd_316186 : Nat := 4983230072969 + 3 ^ 40 * 316186 * 2
def baseEnd_316186 : Nat := 162355394222605154520893

theorem tailTrace_316186 : CollatzResearch.WordTrace tailWord_316186 prefixEnd_316186 162355394222605154520893 := by
  unfold tailWord_316186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883062708129899278682103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7688167221679731409818941 2883062708129899278682103)
  ·
    refine ⟨4324594062194848918023155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2883062708129899278682103 4324594062194848918023155)
    ·
      refine ⟨6486891093292273377034733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324594062194848918023155 6486891093292273377034733)
      ·
        refine ⟨2432584159984602516388025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6486891093292273377034733 2432584159984602516388025)
        ·
          refine ⟨1824438119988451887291019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432584159984602516388025 1824438119988451887291019)
          ·
            refine ⟨2736657179982677830936529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824438119988451887291019 2736657179982677830936529)
            ·
              refine ⟨2052492884987008373202397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736657179982677830936529 2052492884987008373202397)
              ·
                refine ⟨769684831870128139950899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052492884987008373202397 769684831870128139950899)
                ·
                  refine ⟨1154527247805192209926349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769684831870128139950899 1154527247805192209926349)
                  ·
                    refine ⟨432947717926947078722381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1154527247805192209926349 432947717926947078722381)
                    ·
                      refine ⟨162355394222605154520893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 432947717926947078722381 162355394222605154520893)
                      ·
                        rfl

theorem cell23_316186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_316186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316186 prefixEnd_316186 := by exact prefixLift 316186
  have htrace : WordTrace (prefixWord ++ tailWord_316186) baseStart_316186 baseEnd_316186 := by
    simpa [prefixWord, tailWord_316186, baseEnd_316186] using wordTrace_append hprefix tailTrace_316186
  have hstable : (prefixWord ++ tailWord_316186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316186).length < 2 ^ (prefixWord ++ tailWord_316186).sum := by decide
  have hdescent : baseEnd_316186 < baseStart_316186 := by decide
  rcases family_descends (prefixWord ++ tailWord_316186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316221 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_316221 : Nat := 118140960795 + 316221 * 2 ^ 59
def prefixEnd_316221 : Nat := 4983230072969 + 3 ^ 40 * 316221 * 2
def baseEnd_316221 : Nat := 162373366045512517583233

theorem tailTrace_316221 : CollatzResearch.WordTrace tailWord_316221 prefixEnd_316221 162373366045512517583233 := by
  unfold tailWord_316221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533527387392798092252517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7689018258261865394835011 11533527387392798092252517)
  ·
    refine ⟨2162536385136149642297347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11533527387392798092252517 2162536385136149642297347)
    ·
      refine ⟨3243804577704224463446021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162536385136149642297347 3243804577704224463446021)
      ·
        refine ⟨608213358319542086896129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3243804577704224463446021 608213358319542086896129)
        ·
          refine ⟨456160018739656565172097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608213358319542086896129 456160018739656565172097)
          ·
            refine ⟨342120014054742423879073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456160018739656565172097 342120014054742423879073)
            ·
              refine ⟨256590010541056817909305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342120014054742423879073 256590010541056817909305)
              ·
                refine ⟨192442507905792613431979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256590010541056817909305 192442507905792613431979)
                ·
                  refine ⟨288663761858688920147969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192442507905792613431979 288663761858688920147969)
                  ·
                    refine ⟨216497821394016690110977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288663761858688920147969 216497821394016690110977)
                    ·
                      refine ⟨162373366045512517583233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216497821394016690110977 162373366045512517583233)
                      ·
                        rfl

theorem cell23_316221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_316221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316221 prefixEnd_316221 := by exact prefixLift 316221
  have htrace : WordTrace (prefixWord ++ tailWord_316221) baseStart_316221 baseEnd_316221 := by
    simpa [prefixWord, tailWord_316221, baseEnd_316221] using wordTrace_append hprefix tailTrace_316221
  have hstable : (prefixWord ++ tailWord_316221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316221).length < 2 ^ (prefixWord ++ tailWord_316221).sum := by decide
  have hdescent : baseEnd_316221 < baseStart_316221 := by decide
  rcases family_descends (prefixWord ++ tailWord_316221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316229 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_316229 : Nat := 118140960795 + 316229 * 2 ^ 59
def prefixEnd_316229 : Nat := 4983230072969 + 3 ^ 40 * 316229 * 2
def baseEnd_316229 : Nat := 162377473890748486283195

theorem tailTrace_316229 : CollatzResearch.WordTrace tailWord_316229 prefixEnd_316229 162377473890748486283195 := by
  unfold tailWord_316229
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533819171363815458543741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7689212780909210305695827 11533819171363815458543741)
  ·
    refine ⟨4325182189261430796953903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11533819171363815458543741 4325182189261430796953903)
    ·
      refine ⟨6487773283892146195430855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325182189261430796953903 6487773283892146195430855)
      ·
        refine ⟨9731659925838219293146283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487773283892146195430855 9731659925838219293146283)
        ·
          refine ⟨14597489888757328939719425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731659925838219293146283 14597489888757328939719425)
          ·
            refine ⟨10948117416567996704789569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14597489888757328939719425 10948117416567996704789569)
            ·
              refine ⟨8211088062425997528592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10948117416567996704789569 8211088062425997528592177)
              ·
                refine ⟨6158316046819498146444133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8211088062425997528592177 6158316046819498146444133)
                ·
                  refine ⟨1154684258778655902458275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6158316046819498146444133 1154684258778655902458275)
                  ·
                    refine ⟨1732026388167983853687413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154684258778655902458275 1732026388167983853687413)
                    ·
                      refine ⟨162377473890748486283195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1732026388167983853687413 162377473890748486283195)
                      ·
                        rfl

theorem cell23_316229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_316229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316229 prefixEnd_316229 := by exact prefixLift 316229
  have htrace : WordTrace (prefixWord ++ tailWord_316229) baseStart_316229 baseEnd_316229 := by
    simpa [prefixWord, tailWord_316229, baseEnd_316229] using wordTrace_append hprefix tailTrace_316229
  have hstable : (prefixWord ++ tailWord_316229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316229).length < 2 ^ (prefixWord ++ tailWord_316229).sum := by decide
  have hdescent : baseEnd_316229 < baseStart_316229 := by decide
  rcases family_descends (prefixWord ++ tailWord_316229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316236 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_316236 : Nat := 118140960795 + 316236 * 2 ^ 59
def prefixEnd_316236 : Nat := 4983230072969 + 3 ^ 40 * 316236 * 2
def baseEnd_316236 : Nat := 54127022751776652965221

theorem tailTrace_316236 : CollatzResearch.WordTrace tailWord_316236 prefixEnd_316236 54127022751776652965221 := by
  unfold tailWord_316236
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767037241169227827024281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7689382988225637102699041 5767037241169227827024281)
  ·
    refine ⟨4325277930876920870268211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5767037241169227827024281 4325277930876920870268211)
    ·
      refine ⟨6487916896315381305402317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325277930876920870268211 6487916896315381305402317)
      ·
        refine ⟨2432968836118267989525869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6487916896315381305402317 2432968836118267989525869)
        ·
          refine ⟨912363313544350496072201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2432968836118267989525869 912363313544350496072201)
          ·
            refine ⟨684272485158262872054151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912363313544350496072201 684272485158262872054151)
            ·
              refine ⟨1026408727737394308081227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684272485158262872054151 1026408727737394308081227)
              ·
                refine ⟨1539613091606091462121841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026408727737394308081227 1539613091606091462121841)
                ·
                  refine ⟨1154709818704568596591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1539613091606091462121841 1154709818704568596591381)
                  ·
                    refine ⟨54127022751776652965221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1154709818704568596591381 54127022751776652965221)
                    ·
                      rfl

theorem cell23_316236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_316236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316236 prefixEnd_316236 := by exact prefixLift 316236
  have htrace : WordTrace (prefixWord ++ tailWord_316236) baseStart_316236 baseEnd_316236 := by
    simpa [prefixWord, tailWord_316236, baseEnd_316236] using wordTrace_append hprefix tailTrace_316236
  have hstable : (prefixWord ++ tailWord_316236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316236).length < 2 ^ (prefixWord ++ tailWord_316236).sum := by decide
  have hdescent : baseEnd_316236 < baseStart_316236 := by decide
  rcases family_descends (prefixWord ++ tailWord_316236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316249 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 9]
def baseStart_316249 : Nat := 118140960795 + 316249 * 2 ^ 59
def prefixEnd_316249 : Nat := 4983230072969 + 3 ^ 40 * 316249 * 2
def baseEnd_316249 : Nat := 18043082611537600892567

theorem tailTrace_316249 : CollatzResearch.WordTrace tailWord_316249 prefixEnd_316249 18043082611537600892567 := by
  unfold tailWord_316249
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534548631291358874271801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7689699087527572582847867 11534548631291358874271801)
  ·
    refine ⟨8650911473468519155703851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11534548631291358874271801 8650911473468519155703851)
    ·
      refine ⟨12976367210202778733555777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8650911473468519155703851 12976367210202778733555777)
      ·
        refine ⟨9732275407652084050166833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12976367210202778733555777 9732275407652084050166833)
        ·
          refine ⟨7299206555739063037625125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9732275407652084050166833 7299206555739063037625125)
          ·
            refine ⟨1368601229201074319554711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7299206555739063037625125 1368601229201074319554711)
            ·
              refine ⟨2052901843801611479332067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368601229201074319554711 2052901843801611479332067)
              ·
                refine ⟨3079352765702417218998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052901843801611479332067 3079352765702417218998101)
                ·
                  refine ⟨18043082611537600892567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3079352765702417218998101 18043082611537600892567)
                  ·
                    rfl

theorem cell23_316249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_316249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316249 prefixEnd_316249 := by exact prefixLift 316249
  have htrace : WordTrace (prefixWord ++ tailWord_316249) baseStart_316249 baseEnd_316249 := by
    simpa [prefixWord, tailWord_316249, baseEnd_316249] using wordTrace_append hprefix tailTrace_316249
  have hstable : (prefixWord ++ tailWord_316249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316249).length < 2 ^ (prefixWord ++ tailWord_316249).sum := by decide
  have hdescent : baseEnd_316249 < baseStart_316249 := by decide
  rcases family_descends (prefixWord ++ tailWord_316249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316277 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_316277 : Nat := 118140960795 + 316277 * 2 ^ 59
def prefixEnd_316277 : Nat := 4983230072969 + 3 ^ 40 * 316277 * 2
def baseEnd_316277 : Nat := 162402120962164298482975

theorem tailTrace_316277 : CollatzResearch.WordTrace tailWord_316277 prefixEnd_316277 162402120962164298482975 := by
  unfold tailWord_316277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535569875189919656291085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7690379916793279770860723 11535569875189919656291085)
  ·
    refine ⟨4325838703196219871109157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11535569875189919656291085 4325838703196219871109157)
    ·
      refine ⟨811094756849291225832967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4325838703196219871109157 811094756849291225832967)
      ·
        refine ⟨1216642135273936838749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811094756849291225832967 1216642135273936838749451)
        ·
          refine ⟨1824963202910905258124177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216642135273936838749451 1824963202910905258124177)
          ·
            refine ⟨1368722402183178943593133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824963202910905258124177 1368722402183178943593133)
            ·
              refine ⟨513270900818692103847425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1368722402183178943593133 513270900818692103847425)
              ·
                refine ⟨384953175614019077885569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513270900818692103847425 384953175614019077885569)
                ·
                  refine ⟨288714881710514308414177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 384953175614019077885569 288714881710514308414177)
                  ·
                    refine ⟨216536161282885731310633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 288714881710514308414177 216536161282885731310633)
                    ·
                      refine ⟨162402120962164298482975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216536161282885731310633 162402120962164298482975)
                      ·
                        rfl

theorem cell23_316277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_316277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316277 prefixEnd_316277 := by exact prefixLift 316277
  have htrace : WordTrace (prefixWord ++ tailWord_316277) baseStart_316277 baseEnd_316277 := by
    simpa [prefixWord, tailWord_316277, baseEnd_316277] using wordTrace_append hprefix tailTrace_316277
  have hstable : (prefixWord ++ tailWord_316277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316277).length < 2 ^ (prefixWord ++ tailWord_316277).sum := by decide
  have hdescent : baseEnd_316277 < baseStart_316277 := by decide
  rcases family_descends (prefixWord ++ tailWord_316277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316296 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_316296 : Nat := 118140960795 + 316296 * 2 ^ 59
def prefixEnd_316296 : Nat := 4983230072969 + 3 ^ 40 * 316296 * 2
def baseEnd_316296 : Nat := 54137292364866574715129

theorem tailTrace_316296 : CollatzResearch.WordTrace tailWord_316296 prefixEnd_316296 54137292364866574715129 := by
  unfold tailWord_316296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768131431060542950616371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7690841908080723934155161 5768131431060542950616371)
  ·
    refine ⟨8652197146590814425924557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5768131431060542950616371 8652197146590814425924557)
    ·
      refine ⟨3244573929971555409721709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8652197146590814425924557 3244573929971555409721709)
      ·
        refine ⟨1216715223739333278645641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3244573929971555409721709 1216715223739333278645641)
        ·
          refine ⟨912536417804499958984231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216715223739333278645641 912536417804499958984231)
          ·
            refine ⟨1368804626706749938476347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912536417804499958984231 1368804626706749938476347)
            ·
              refine ⟨2053206940060124907714521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368804626706749938476347 2053206940060124907714521)
              ·
                refine ⟨1539905205045093680785891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053206940060124907714521 1539905205045093680785891)
                ·
                  refine ⟨2309857807567640521178837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539905205045093680785891 2309857807567640521178837)
                  ·
                    refine ⟨54137292364866574715129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2309857807567640521178837 54137292364866574715129)
                    ·
                      rfl

theorem cell23_316296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_316296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316296 prefixEnd_316296 := by exact prefixLift 316296
  have htrace : WordTrace (prefixWord ++ tailWord_316296) baseStart_316296 baseEnd_316296 := by
    simpa [prefixWord, tailWord_316296, baseEnd_316296] using wordTrace_append hprefix tailTrace_316296
  have hstable : (prefixWord ++ tailWord_316296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316296).length < 2 ^ (prefixWord ++ tailWord_316296).sum := by decide
  have hdescent : baseEnd_316296 < baseStart_316296 := by decide
  rcases family_descends (prefixWord ++ tailWord_316296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316340 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_316340 : Nat := 118140960795 + 316340 * 2 ^ 59
def prefixEnd_316340 : Nat := 4983230072969 + 3 ^ 40 * 316340 * 2
def baseEnd_316340 : Nat := 162434470243397551995185

theorem tailTrace_316340 : CollatzResearch.WordTrace tailWord_316340 prefixEnd_316340 162434470243397551995185 := by
  unfold tailWord_316340
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768933836980840707917237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7691911782641120943889649 5768933836980840707917237)
  ·
    refine ⟨540837547216953816367241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5768933836980840707917237 540837547216953816367241)
    ·
      refine ⟨405628160412715362275431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540837547216953816367241 405628160412715362275431)
      ·
        refine ⟨608442240619073043413147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405628160412715362275431 608442240619073043413147)
        ·
          refine ⟨912663360928609565119721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608442240619073043413147 912663360928609565119721)
          ·
            refine ⟨684497520696457173839791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912663360928609565119721 684497520696457173839791)
            ·
              refine ⟨1026746281044685760759687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684497520696457173839791 1026746281044685760759687)
              ·
                refine ⟨1540119421567028641139531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026746281044685760759687 1540119421567028641139531)
                ·
                  refine ⟨2310179132350542961709297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540119421567028641139531 2310179132350542961709297)
                  ·
                    refine ⟨1732634349262907221281973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310179132350542961709297 1732634349262907221281973)
                    ·
                      refine ⟨162434470243397551995185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1732634349262907221281973 162434470243397551995185)
                      ·
                        rfl

theorem cell23_316340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_316340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316340 prefixEnd_316340 := by exact prefixLift 316340
  have htrace : WordTrace (prefixWord ++ tailWord_316340) baseStart_316340 baseEnd_316340 := by
    simpa [prefixWord, tailWord_316340, baseEnd_316340] using wordTrace_append hprefix tailTrace_316340
  have hstable : (prefixWord ++ tailWord_316340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316340).length < 2 ^ (prefixWord ++ tailWord_316340).sum := by decide
  have hdescent : baseEnd_316340 < baseStart_316340 := by decide
  rcases family_descends (prefixWord ++ tailWord_316340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316343 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 3, 4]
def baseStart_316343 : Nat := 118140960795 + 316343 * 2 ^ 59
def prefixEnd_316343 : Nat := 4983230072969 + 3 ^ 40 * 316343 * 2
def baseEnd_316343 : Nat := 54145336895120346752557

theorem tailTrace_316343 : CollatzResearch.WordTrace tailWord_316343 prefixEnd_316343 54145336895120346752557 := by
  unfold tailWord_316343
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537977092950812928193683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7691984728633875285462455 11537977092950812928193683)
  ·
    refine ⟨17306965639426219392290525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537977092950812928193683 17306965639426219392290525)
    ·
      refine ⟨6490112114784832272108947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17306965639426219392290525 6490112114784832272108947)
      ·
        refine ⟨9735168172177248408163421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6490112114784832272108947 9735168172177248408163421)
        ·
          refine ⟨3650688064566468153061283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9735168172177248408163421 3650688064566468153061283)
          ·
            refine ⟨5476032096849702229591925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650688064566468153061283 5476032096849702229591925)
            ·
              refine ⟨513378009079659584024243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5476032096849702229591925 513378009079659584024243)
              ·
                refine ⟨770067013619489376036365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513378009079659584024243 770067013619489376036365)
                ·
                  refine ⟨288775130107308516013637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 770067013619489376036365 288775130107308516013637)
                  ·
                    refine ⟨54145336895120346752557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288775130107308516013637 54145336895120346752557)
                    ·
                      rfl

theorem cell23_316343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_316343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316343 prefixEnd_316343 := by exact prefixLift 316343
  have htrace : WordTrace (prefixWord ++ tailWord_316343) baseStart_316343 baseEnd_316343 := by
    simpa [prefixWord, tailWord_316343, baseEnd_316343] using wordTrace_append hprefix tailTrace_316343
  have hstable : (prefixWord ++ tailWord_316343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316343).length < 2 ^ (prefixWord ++ tailWord_316343).sum := by decide
  have hdescent : baseEnd_316343 < baseStart_316343 := by decide
  rcases family_descends (prefixWord ++ tailWord_316343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316370 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_316370 : Nat := 118140960795 + 316370 * 2 ^ 59
def prefixEnd_316370 : Nat := 4983230072969 + 3 ^ 40 * 316370 * 2
def baseEnd_316370 : Nat := 162449874663032434620047

theorem tailTrace_316370 : CollatzResearch.WordTrace tailWord_316370 prefixEnd_316370 162449874663032434620047 := by
  unfold tailWord_316370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884740465963249134856641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7692641242568664359617709 2884740465963249134856641)
  ·
    refine ⟨2163555349472436851142481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2884740465963249134856641 2163555349472436851142481)
    ·
      refine ⟨1622666512104327638356861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163555349472436851142481 1622666512104327638356861)
      ·
        refine ⟨608499942039122864383823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1622666512104327638356861 608499942039122864383823)
        ·
          refine ⟨912749913058684296575735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608499942039122864383823 912749913058684296575735)
          ·
            refine ⟨1369124869588026444863603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912749913058684296575735 1369124869588026444863603)
            ·
              refine ⟨2053687304382039667295405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369124869588026444863603 2053687304382039667295405)
              ·
                refine ⟨770132739143264875235777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053687304382039667295405 770132739143264875235777)
                ·
                  refine ⟨577599554357448656426833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770132739143264875235777 577599554357448656426833)
                  ·
                    refine ⟨433199665768086492320125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577599554357448656426833 433199665768086492320125)
                    ·
                      refine ⟨162449874663032434620047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433199665768086492320125 162449874663032434620047)
                      ·
                        rfl

theorem cell23_316370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_316370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316370 prefixEnd_316370 := by exact prefixLift 316370
  have htrace : WordTrace (prefixWord ++ tailWord_316370) baseStart_316370 baseEnd_316370 := by
    simpa [prefixWord, tailWord_316370, baseEnd_316370] using wordTrace_append hprefix tailTrace_316370
  have hstable : (prefixWord ++ tailWord_316370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316370).length < 2 ^ (prefixWord ++ tailWord_316370).sum := by decide
  have hdescent : baseEnd_316370 < baseStart_316370 := by decide
  rcases family_descends (prefixWord ++ tailWord_316370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316394 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_316394 : Nat := 118140960795 + 316394 * 2 ^ 59
def prefixEnd_316394 : Nat := 4983230072969 + 3 ^ 40 * 316394 * 2
def baseEnd_316394 : Nat := 54154066066246780239979

theorem tailTrace_316394 : CollatzResearch.WordTrace tailWord_316394 prefixEnd_316394 54154066066246780239979 := by
  unfold tailWord_316394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884959303941512159575059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7693224810510699092200157 2884959303941512159575059)
  ·
    refine ⟨4327438955912268239362589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884959303941512159575059 4327438955912268239362589)
    ·
      refine ⟨1622789608467100589760971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4327438955912268239362589 1622789608467100589760971)
      ·
        refine ⟨2434184412700650884641457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622789608467100589760971 2434184412700650884641457)
        ·
          refine ⟨1825638309525488163481093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434184412700650884641457 1825638309525488163481093)
          ·
            refine ⟨342307183036029030652705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1825638309525488163481093 342307183036029030652705)
            ·
              refine ⟨256730387277021772989529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342307183036029030652705 256730387277021772989529)
              ·
                refine ⟨192547790457766329742147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256730387277021772989529 192547790457766329742147)
                ·
                  refine ⟨288821685686649494613221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192547790457766329742147 288821685686649494613221)
                  ·
                    refine ⟨54154066066246780239979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288821685686649494613221 54154066066246780239979)
                    ·
                      rfl

theorem cell23_316394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_316394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316394 prefixEnd_316394 := by exact prefixLift 316394
  have htrace : WordTrace (prefixWord ++ tailWord_316394) baseStart_316394 baseEnd_316394 := by
    simpa [prefixWord, tailWord_316394, baseEnd_316394] using wordTrace_append hprefix tailTrace_316394
  have hstable : (prefixWord ++ tailWord_316394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316394).length < 2 ^ (prefixWord ++ tailWord_316394).sum := by decide
  have hdescent : baseEnd_316394 < baseStart_316394 := by decide
  rcases family_descends (prefixWord ++ tailWord_316394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316423 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_316423 : Nat := 118140960795 + 316423 * 2 ^ 59
def prefixEnd_316423 : Nat := 4983230072969 + 3 ^ 40 * 316423 * 2
def baseEnd_316423 : Nat := 162477089137720727257303

theorem tailTrace_316423 : CollatzResearch.WordTrace tailWord_316423 prefixEnd_316423 162477089137720727257303 := by
  unfold tailWord_316423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11540894932660986591105923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7693929955107324394070615 11540894932660986591105923)
  ·
    refine ⟨17311342398991479886658885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11540894932660986591105923 17311342398991479886658885)
    ·
      refine ⟨3245876699810902478748541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17311342398991479886658885 3245876699810902478748541)
      ·
        refine ⟨1217203762429088429530703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3245876699810902478748541 1217203762429088429530703)
        ·
          refine ⟨1825805643643632644296055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217203762429088429530703 1825805643643632644296055)
          ·
            refine ⟨2738708465465448966444083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825805643643632644296055 2738708465465448966444083)
            ·
              refine ⟨4108062698198173449666125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738708465465448966444083 4108062698198173449666125)
              ·
                refine ⟨1540523511824315043624797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108062698198173449666125 1540523511824315043624797)
                ·
                  refine ⟨577696316934118141359299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1540523511824315043624797 577696316934118141359299)
                  ·
                    refine ⟨866544475401177212038949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577696316934118141359299 866544475401177212038949)
                    ·
                      refine ⟨162477089137720727257303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 866544475401177212038949 162477089137720727257303)
                      ·
                        rfl

theorem cell23_316423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_316423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316423 prefixEnd_316423 := by exact prefixLift 316423
  have htrace : WordTrace (prefixWord ++ tailWord_316423) baseStart_316423 baseEnd_316423 := by
    simpa [prefixWord, tailWord_316423, baseEnd_316423] using wordTrace_append hprefix tailTrace_316423
  have hstable : (prefixWord ++ tailWord_316423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316423).length < 2 ^ (prefixWord ++ tailWord_316423).sum := by decide
  have hdescent : baseEnd_316423 < baseStart_316423 := by decide
  rcases family_descends (prefixWord ++ tailWord_316423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316427 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 2, 3, 2]
def baseStart_316427 : Nat := 118140960795 + 316427 * 2 ^ 59
def prefixEnd_316427 : Nat := 4983230072969 + 3 ^ 40 * 316427 * 2
def baseEnd_316427 : Nat := 162479143060338711607285

theorem tailTrace_316427 : CollatzResearch.WordTrace tailWord_316427 prefixEnd_316427 162479143060338711607285 := by
  unfold tailWord_316427
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541040824646495274251535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694027216430996849501023 11541040824646495274251535)
  ·
    refine ⟨17311561236969742911377303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11541040824646495274251535 17311561236969742911377303)
    ·
      refine ⟨25967341855454614367065955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17311561236969742911377303 25967341855454614367065955)
      ·
        refine ⟨38951012783181921550598933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25967341855454614367065955 38951012783181921550598933)
        ·
          refine ⟨1825828724211652572684325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38951012783181921550598933 1825828724211652572684325)
          ·
            refine ⟨342342885789684857378311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1825828724211652572684325 342342885789684857378311)
            ·
              refine ⟨513514328684527286067467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342342885789684857378311 513514328684527286067467)
              ·
                refine ⟨770271493026790929101201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513514328684527286067467 770271493026790929101201)
                ·
                  refine ⟨577703619770093196825901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770271493026790929101201 577703619770093196825901)
                  ·
                    refine ⟨216638857413784948809713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 577703619770093196825901 216638857413784948809713)
                    ·
                      refine ⟨162479143060338711607285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216638857413784948809713 162479143060338711607285)
                      ·
                        rfl

theorem cell23_316427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3, 2].length) (baseStart_316427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316427 prefixEnd_316427 := by exact prefixLift 316427
  have htrace : WordTrace (prefixWord ++ tailWord_316427) baseStart_316427 baseEnd_316427 := by
    simpa [prefixWord, tailWord_316427, baseEnd_316427] using wordTrace_append hprefix tailTrace_316427
  have hstable : (prefixWord ++ tailWord_316427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316427).length < 2 ^ (prefixWord ++ tailWord_316427).sum := by decide
  have hdescent : baseEnd_316427 < baseStart_316427 := by decide
  rcases family_descends (prefixWord ++ tailWord_316427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316437 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_316437 : Nat := 118140960795 + 316437 * 2 ^ 59
def prefixEnd_316437 : Nat := 4983230072969 + 3 ^ 40 * 316437 * 2
def baseEnd_316437 : Nat := 54161425955627890827413

theorem tailTrace_316437 : CollatzResearch.WordTrace tailWord_316437 prefixEnd_316437 54161425955627890827413 := by
  unfold tailWord_316437
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541405554610266982115565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7694270369740177988077043 11541405554610266982115565)
  ·
    refine ⟨4328027082978850118293337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11541405554610266982115565 4328027082978850118293337)
    ·
      refine ⟨3246020312234137588720003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4328027082978850118293337 3246020312234137588720003)
      ·
        refine ⟨4869030468351206383080005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246020312234137588720003 4869030468351206383080005)
        ·
          refine ⟨912943212815851196827501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4869030468351206383080005 912943212815851196827501)
          ·
            refine ⟨342353704805944198810313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 912943212815851196827501 342353704805944198810313)
            ·
              refine ⟨256765278604458149107735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342353704805944198810313 256765278604458149107735)
              ·
                refine ⟨385147917906687223661603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256765278604458149107735 385147917906687223661603)
                ·
                  refine ⟨577721876860030835492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385147917906687223661603 577721876860030835492405)
                  ·
                    refine ⟨54161425955627890827413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 577721876860030835492405 54161425955627890827413)
                    ·
                      rfl

theorem cell23_316437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_316437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316437 prefixEnd_316437 := by exact prefixLift 316437
  have htrace : WordTrace (prefixWord ++ tailWord_316437) baseStart_316437 baseEnd_316437 := by
    simpa [prefixWord, tailWord_316437, baseEnd_316437] using wordTrace_append hprefix tailTrace_316437
  have hstable : (prefixWord ++ tailWord_316437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316437).length < 2 ^ (prefixWord ++ tailWord_316437).sum := by decide
  have hdescent : baseEnd_316437 < baseStart_316437 := by decide
  rcases family_descends (prefixWord ++ tailWord_316437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316440 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_316440 : Nat := 118140960795 + 316440 * 2 ^ 59
def prefixEnd_316440 : Nat := 4983230072969 + 3 ^ 40 * 316440 * 2
def baseEnd_316440 : Nat := 162485818308847160744725

theorem tailTrace_316440 : CollatzResearch.WordTrace tailWord_316440 prefixEnd_316440 162485818308847160744725 := by
  unfold tailWord_316440
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770757486799699247237387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7694343315732932329649849 5770757486799699247237387)
  ·
    refine ⟨8656136230199548870856081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770757486799699247237387 8656136230199548870856081)
    ·
      refine ⟨6492102172649661653142061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8656136230199548870856081 6492102172649661653142061)
      ·
        refine ⟨2434538314743623119928273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6492102172649661653142061 2434538314743623119928273)
        ·
          refine ⟨1825903736057717339946205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434538314743623119928273 1825903736057717339946205)
          ·
            refine ⟨684713901021644002479827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1825903736057717339946205 684713901021644002479827)
            ·
              refine ⟨1027070851532466003719741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684713901021644002479827 1027070851532466003719741)
              ·
                refine ⟨385151569324674751394903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027070851532466003719741 385151569324674751394903)
                ·
                  refine ⟨577727353987012127092355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385151569324674751394903 577727353987012127092355)
                  ·
                    refine ⟨866591030980518190638533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577727353987012127092355 866591030980518190638533)
                    ·
                      refine ⟨162485818308847160744725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 866591030980518190638533 162485818308847160744725)
                      ·
                        rfl

theorem cell23_316440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_316440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316440 prefixEnd_316440 := by exact prefixLift 316440
  have htrace : WordTrace (prefixWord ++ tailWord_316440) baseStart_316440 baseEnd_316440 := by
    simpa [prefixWord, tailWord_316440, baseEnd_316440] using wordTrace_append hprefix tailTrace_316440
  have hstable : (prefixWord ++ tailWord_316440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316440).length < 2 ^ (prefixWord ++ tailWord_316440).sum := by decide
  have hdescent : baseEnd_316440 < baseStart_316440 := by decide
  rcases family_descends (prefixWord ++ tailWord_316440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316450 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_316450 : Nat := 118140960795 + 316450 * 2 ^ 59
def prefixEnd_316450 : Nat := 4983230072969 + 3 ^ 40 * 316450 * 2
def baseEnd_316450 : Nat := 54163651038464040539893

theorem tailTrace_316450 : CollatzResearch.WordTrace tailWord_316450 prefixEnd_316450 54163651038464040539893 := by
  unfold tailWord_316450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885469925890792550584701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7694586469042113468225869 2885469925890792550584701)
  ·
    refine ⟨1082051222209047206469263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2885469925890792550584701 1082051222209047206469263)
    ·
      refine ⟨1623076833313570809703895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082051222209047206469263 1623076833313570809703895)
      ·
        refine ⟨2434615249970356214555843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623076833313570809703895 2434615249970356214555843)
        ·
          refine ⟨3651922874955534321833765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434615249970356214555843 3651922874955534321833765)
          ·
            refine ⟨684735539054162685343831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3651922874955534321833765 684735539054162685343831)
            ·
              refine ⟨1027103308581244028015747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684735539054162685343831 1027103308581244028015747)
              ·
                refine ⟨1540654962871866042023621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027103308581244028015747 1540654962871866042023621)
                ·
                  refine ⟨288872805538474882879429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540654962871866042023621 288872805538474882879429)
                  ·
                    refine ⟨54163651038464040539893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288872805538474882879429 54163651038464040539893)
                    ·
                      rfl

theorem cell23_316450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_316450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316450 prefixEnd_316450 := by exact prefixLift 316450
  have htrace : WordTrace (prefixWord ++ tailWord_316450) baseStart_316450 baseEnd_316450 := by
    simpa [prefixWord, tailWord_316450, baseEnd_316450] using wordTrace_append hprefix tailTrace_316450
  have hstable : (prefixWord ++ tailWord_316450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316450).length < 2 ^ (prefixWord ++ tailWord_316450).sum := by decide
  have hdescent : baseEnd_316450 < baseStart_316450 := by decide
  rcases family_descends (prefixWord ++ tailWord_316450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316470 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_316470 : Nat := 118140960795 + 316470 * 2 ^ 59
def prefixEnd_316470 : Nat := 4983230072969 + 3 ^ 40 * 316470 * 2
def baseEnd_316470 : Nat := 162501222728482043369587

theorem tailTrace_316470 : CollatzResearch.WordTrace tailWord_316470 prefixEnd_316470 162501222728482043369587 := by
  unfold tailWord_316470
  simp only [CollatzResearch.WordTrace]
  refine ⟨721413072718169601129179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7695072775660475745377909 721413072718169601129179)
  ·
    refine ⟨1082119609077254401693769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721413072718169601129179 1082119609077254401693769)
    ·
      refine ⟨811589706807940801270327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1082119609077254401693769 811589706807940801270327)
      ·
        refine ⟨1217384560211911201905491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811589706807940801270327 1217384560211911201905491)
        ·
          refine ⟨1826076840317866802858237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217384560211911201905491 1826076840317866802858237)
          ·
            refine ⟨684778815119200051071839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1826076840317866802858237 684778815119200051071839)
            ·
              refine ⟨1027168222678800076607759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684778815119200051071839 1027168222678800076607759)
              ·
                refine ⟨1540752334018200114911639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027168222678800076607759 1540752334018200114911639)
                ·
                  refine ⟨2311128501027300172367459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540752334018200114911639 2311128501027300172367459)
                  ·
                    refine ⟨3466692751540950258551189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311128501027300172367459 3466692751540950258551189)
                    ·
                      refine ⟨162501222728482043369587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3466692751540950258551189 162501222728482043369587)
                      ·
                        rfl

theorem cell23_316470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_316470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316470 prefixEnd_316470 := by exact prefixLift 316470
  have htrace : WordTrace (prefixWord ++ tailWord_316470) baseStart_316470 baseEnd_316470 := by
    simpa [prefixWord, tailWord_316470, baseEnd_316470] using wordTrace_append hprefix tailTrace_316470
  have hstable : (prefixWord ++ tailWord_316470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316470).length < 2 ^ (prefixWord ++ tailWord_316470).sum := by decide
  have hdescent : baseEnd_316470 < baseStart_316470 := by decide
  rcases family_descends (prefixWord ++ tailWord_316470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316477 : List Nat := [1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_316477 : Nat := 118140960795 + 316477 * 2 ^ 59
def prefixEnd_316477 : Nat := 4983230072969 + 3 ^ 40 * 316477 * 2
def baseEnd_316477 : Nat := 162504817093063515982055

theorem tailTrace_316477 : CollatzResearch.WordTrace tailWord_316477 prefixEnd_316477 162504817093063515982055 := by
  unfold tailWord_316477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542864474465353813571685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7695242982976902542381123 11542864474465353813571685)
  ·
    refine ⟨2164287088962253840044691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11542864474465353813571685 2164287088962253840044691)
    ·
      refine ⟨3246430633443380760067037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164287088962253840044691 3246430633443380760067037)
      ·
        refine ⟨1217411487541267785025139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3246430633443380760067037 1217411487541267785025139)
        ·
          refine ⟨1826117231311901677537709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217411487541267785025139 1826117231311901677537709)
          ·
            refine ⟨684793961741963129076641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1826117231311901677537709 684793961741963129076641)
            ·
              refine ⟨513595471306472346807481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684793961741963129076641 513595471306472346807481)
              ·
                refine ⟨385196603479854260105611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513595471306472346807481 385196603479854260105611)
                ·
                  refine ⟨577794905219781390158417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385196603479854260105611 577794905219781390158417)
                  ·
                    refine ⟨433346178914836042618813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577794905219781390158417 433346178914836042618813)
                    ·
                      refine ⟨162504817093063515982055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433346178914836042618813 162504817093063515982055)
                      ·
                        rfl

theorem cell23_316477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_316477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316477 prefixEnd_316477 := by exact prefixLift 316477
  have htrace : WordTrace (prefixWord ++ tailWord_316477) baseStart_316477 baseEnd_316477 := by
    simpa [prefixWord, tailWord_316477, baseEnd_316477] using wordTrace_append hprefix tailTrace_316477
  have hstable : (prefixWord ++ tailWord_316477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316477).length < 2 ^ (prefixWord ++ tailWord_316477).sum := by decide
  have hdescent : baseEnd_316477 < baseStart_316477 := by decide
  rcases family_descends (prefixWord ++ tailWord_316477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316490 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_316490 : Nat := 118140960795 + 316490 * 2 ^ 59
def prefixEnd_316490 : Nat := 4983230072969 + 3 ^ 40 * 316490 * 2
def baseEnd_316490 : Nat := 162511492341571965119495

theorem tailTrace_316490 : CollatzResearch.WordTrace tailWord_316490 prefixEnd_316490 162511492341571965119495 := by
  unfold tailWord_316490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885834655854564258448731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7695559082278838022529949 2885834655854564258448731)
  ·
    refine ⟨4328751983781846387673097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885834655854564258448731 4328751983781846387673097)
    ·
      refine ⟨3246563987836384790754823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4328751983781846387673097 3246563987836384790754823)
      ·
        refine ⟨4869845981754577186132235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246563987836384790754823 4869845981754577186132235)
        ·
          refine ⟨7304768972631865779198353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869845981754577186132235 7304768972631865779198353)
          ·
            refine ⟨5478576729473899334398765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7304768972631865779198353 5478576729473899334398765)
            ·
              refine ⟨2054466273552712250399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5478576729473899334398765 2054466273552712250399537)
              ·
                refine ⟨1540849705164534187799653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054466273552712250399537 1540849705164534187799653)
                ·
                  refine ⟨288909319718350160212435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540849705164534187799653 288909319718350160212435)
                  ·
                    refine ⟨433363979577525240318653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288909319718350160212435 433363979577525240318653)
                    ·
                      refine ⟨162511492341571965119495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433363979577525240318653 162511492341571965119495)
                      ·
                        rfl

theorem cell23_316490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_316490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316490 prefixEnd_316490 := by exact prefixLift 316490
  have htrace : WordTrace (prefixWord ++ tailWord_316490) baseStart_316490 baseEnd_316490 := by
    simpa [prefixWord, tailWord_316490, baseEnd_316490] using wordTrace_append hprefix tailTrace_316490
  have hstable : (prefixWord ++ tailWord_316490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316490).length < 2 ^ (prefixWord ++ tailWord_316490).sum := by decide
  have hdescent : baseEnd_316490 < baseStart_316490 := by decide
  rcases family_descends (prefixWord ++ tailWord_316490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316496 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_316496 : Nat := 118140960795 + 316496 * 2 ^ 59
def prefixEnd_316496 : Nat := 4983230072969 + 3 ^ 40 * 316496 * 2
def baseEnd_316496 : Nat := 162514573225498941644467

theorem tailTrace_316496 : CollatzResearch.WordTrace tailWord_316496 prefixEnd_316496 162514573225498941644467 := by
  unfold tailWord_316496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771778730698260029256671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7695704974264346705675561 5771778730698260029256671)
  ·
    refine ⟨8657668096047390043885007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771778730698260029256671 8657668096047390043885007)
    ·
      refine ⟨12986502144071085065827511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8657668096047390043885007 12986502144071085065827511)
      ·
        refine ⟨19479753216106627598741267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12986502144071085065827511 19479753216106627598741267)
        ·
          refine ⟨29219629824159941398111901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19479753216106627598741267 29219629824159941398111901)
          ·
            refine ⟨10957361184059978024291963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29219629824159941398111901 10957361184059978024291963)
            ·
              refine ⟨16436041776089967036437945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10957361184059978024291963 16436041776089967036437945)
              ·
                refine ⟨12327031332067475277328459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16436041776089967036437945 12327031332067475277328459)
                ·
                  refine ⟨18490546998101212915992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12327031332067475277328459 18490546998101212915992689)
                  ·
                    refine ⟨13867910248575909686994517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18490546998101212915992689 13867910248575909686994517)
                    ·
                      refine ⟨162514573225498941644467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13867910248575909686994517 162514573225498941644467)
                      ·
                        rfl

theorem cell23_316496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_316496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316496 prefixEnd_316496 := by exact prefixLift 316496
  have htrace : WordTrace (prefixWord ++ tailWord_316496) baseStart_316496 baseEnd_316496 := by
    simpa [prefixWord, tailWord_316496, baseEnd_316496] using wordTrace_append hprefix tailTrace_316496
  have hstable : (prefixWord ++ tailWord_316496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316496).length < 2 ^ (prefixWord ++ tailWord_316496).sum := by decide
  have hdescent : baseEnd_316496 < baseStart_316496 := by decide
  rcases family_descends (prefixWord ++ tailWord_316496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316580 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_316580 : Nat := 118140960795 + 316580 * 2 ^ 59
def prefixEnd_316580 : Nat := 4983230072969 + 3 ^ 40 * 316580 * 2
def baseEnd_316580 : Nat := 162557705600476612994081

theorem tailTrace_316580 : CollatzResearch.WordTrace tailWord_316580 prefixEnd_316580 162557705600476612994081 := by
  unfold tailWord_316580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773310596546101202285597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7697747462061468269714129 5773310596546101202285597)
  ·
    refine ⟨2164991473704787950857099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5773310596546101202285597 2164991473704787950857099)
    ·
      refine ⟨3247487210557181926285649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164991473704787950857099 3247487210557181926285649)
      ·
        refine ⟨2435615407917886444714237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247487210557181926285649 2435615407917886444714237)
        ·
          refine ⟨913355777969207416767839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2435615407917886444714237 913355777969207416767839)
          ·
            refine ⟨1370033666953811125151759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913355777969207416767839 1370033666953811125151759)
            ·
              refine ⟨2055050500430716687727639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370033666953811125151759 2055050500430716687727639)
              ·
                refine ⟨3082575750646075031591459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055050500430716687727639 3082575750646075031591459)
                ·
                  refine ⟨4623863625969112547387189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082575750646075031591459 4623863625969112547387189)
                  ·
                    refine ⟨433487214934604301317549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623863625969112547387189 433487214934604301317549)
                    ·
                      refine ⟨162557705600476612994081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433487214934604301317549 162557705600476612994081)
                      ·
                        rfl

theorem cell23_316580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_316580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316580 prefixEnd_316580 := by exact prefixLift 316580
  have htrace : WordTrace (prefixWord ++ tailWord_316580) baseStart_316580 baseEnd_316580 := by
    simpa [prefixWord, tailWord_316580, baseEnd_316580] using wordTrace_append hprefix tailTrace_316580
  have hstable : (prefixWord ++ tailWord_316580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316580).length < 2 ^ (prefixWord ++ tailWord_316580).sum := by decide
  have hdescent : baseEnd_316580 < baseStart_316580 := by decide
  rcases family_descends (prefixWord ++ tailWord_316580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316633 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_316633 : Nat := 118140960795 + 316633 * 2 ^ 59
def prefixEnd_316633 : Nat := 4983230072969 + 3 ^ 40 * 316633 * 2
def baseEnd_316633 : Nat := 162584920075164905631337

theorem tailTrace_316633 : CollatzResearch.WordTrace tailWord_316633 prefixEnd_316633 162584920075164905631337 := by
  unfold tailWord_316633
  simp only [CollatzResearch.WordTrace]
  refine ⟨11548554261900192456250553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7699036174600128304167035 11548554261900192456250553)
  ·
    refine ⟨8661415696425144342187915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11548554261900192456250553 8661415696425144342187915)
    ·
      refine ⟨12992123544637716513281873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8661415696425144342187915 12992123544637716513281873)
      ·
        refine ⟨9744092658478287384961405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12992123544637716513281873 9744092658478287384961405)
        ·
          refine ⟨3654034746929357769360527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9744092658478287384961405 3654034746929357769360527)
          ·
            refine ⟨5481052120394036654040791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654034746929357769360527 5481052120394036654040791)
            ·
              refine ⟨8221578180591054981061187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481052120394036654040791 8221578180591054981061187)
              ·
                refine ⟨12332367270886582471591781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8221578180591054981061187 12332367270886582471591781)
                ·
                  refine ⟨2312318863291234213423459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12332367270886582471591781 2312318863291234213423459)
                  ·
                    refine ⟨3468478294936851320135189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312318863291234213423459 3468478294936851320135189)
                    ·
                      refine ⟨162584920075164905631337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3468478294936851320135189 162584920075164905631337)
                      ·
                        rfl

theorem cell23_316633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_316633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316633 prefixEnd_316633 := by exact prefixLift 316633
  have htrace : WordTrace (prefixWord ++ tailWord_316633) baseStart_316633 baseEnd_316633 := by
    simpa [prefixWord, tailWord_316633, baseEnd_316633] using wordTrace_append hprefix tailTrace_316633
  have hstable : (prefixWord ++ tailWord_316633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316633).length < 2 ^ (prefixWord ++ tailWord_316633).sum := by decide
  have hdescent : baseEnd_316633 < baseStart_316633 := by decide
  rcases family_descends (prefixWord ++ tailWord_316633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316640 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_316640 : Nat := 118140960795 + 316640 * 2 ^ 59
def prefixEnd_316640 : Nat := 4983230072969 + 3 ^ 40 * 316640 * 2
def baseEnd_316640 : Nat := 162588514439746378243805

theorem tailTrace_316640 : CollatzResearch.WordTrace tailWord_316640 prefixEnd_316640 162588514439746378243805 := by
  unfold tailWord_316640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774404786437416325877687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7699206381916555101170249 5774404786437416325877687)
  ·
    refine ⟨8661607179656124488816531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774404786437416325877687 8661607179656124488816531)
    ·
      refine ⟨12992410769484186733224797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8661607179656124488816531 12992410769484186733224797)
      ·
        refine ⟨4872154038556570024959299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12992410769484186733224797 4872154038556570024959299)
        ·
          refine ⟨7308231057834855037438949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872154038556570024959299 7308231057834855037438949)
          ·
            refine ⟨1370293323344035319519803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7308231057834855037438949 1370293323344035319519803)
            ·
              refine ⟨2055439985016052979279705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370293323344035319519803 2055439985016052979279705)
              ·
                refine ⟨1541579988762039734459779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055439985016052979279705 1541579988762039734459779)
                ·
                  refine ⟨2312369983143059601689669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541579988762039734459779 2312369983143059601689669)
                  ·
                    refine ⟨433569371839323675316813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312369983143059601689669 433569371839323675316813)
                    ·
                      refine ⟨162588514439746378243805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433569371839323675316813 162588514439746378243805)
                      ·
                        rfl

theorem cell23_316640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_316640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316640 prefixEnd_316640 := by exact prefixLift 316640
  have htrace : WordTrace (prefixWord ++ tailWord_316640) baseStart_316640 baseEnd_316640 := by
    simpa [prefixWord, tailWord_316640, baseEnd_316640] using wordTrace_append hprefix tailTrace_316640
  have hstable : (prefixWord ++ tailWord_316640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316640).length < 2 ^ (prefixWord ++ tailWord_316640).sum := by decide
  have hdescent : baseEnd_316640 < baseStart_316640 := by decide
  rcases family_descends (prefixWord ++ tailWord_316640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_316663 : Nat := 118140960795 + 316663 * 2 ^ 59
def prefixEnd_316663 : Nat := 4983230072969 + 3 ^ 40 * 316663 * 2
def baseEnd_316663 : Nat := 162600324494799788256199

theorem tailTrace_316663 : CollatzResearch.WordTrace tailWord_316663 prefixEnd_316663 162600324494799788256199 := by
  unfold tailWord_316663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11549648451791507579842643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7699765634527671719895095 11549648451791507579842643)
  ·
    refine ⟨17324472677687261369763965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11549648451791507579842643 17324472677687261369763965)
    ·
      refine ⟨6496677254132723013661487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17324472677687261369763965 6496677254132723013661487)
      ·
        refine ⟨9745015881199084520492231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496677254132723013661487 9745015881199084520492231)
        ·
          refine ⟨14617523821798626780738347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9745015881199084520492231 14617523821798626780738347)
          ·
            refine ⟨21926285732697940171107521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14617523821798626780738347 21926285732697940171107521)
            ·
              refine ⟨16444714299523455128330641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21926285732697940171107521 16444714299523455128330641)
              ·
                refine ⟨12333535724642591346247981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16444714299523455128330641 12333535724642591346247981)
                ·
                  refine ⟨4625075896740971754842993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12333535724642591346247981 4625075896740971754842993)
                  ·
                    refine ⟨3468806922555728816132245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625075896740971754842993 3468806922555728816132245)
                    ·
                      refine ⟨162600324494799788256199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3468806922555728816132245 162600324494799788256199)
                      ·
                        rfl

theorem cell23_316663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_316663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316663 prefixEnd_316663 := by exact prefixLift 316663
  have htrace : WordTrace (prefixWord ++ tailWord_316663) baseStart_316663 baseEnd_316663 := by
    simpa [prefixWord, tailWord_316663, baseEnd_316663] using wordTrace_append hprefix tailTrace_316663
  have hstable : (prefixWord ++ tailWord_316663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316663).length < 2 ^ (prefixWord ++ tailWord_316663).sum := by decide
  have hdescent : baseEnd_316663 < baseStart_316663 := by decide
  rcases family_descends (prefixWord ++ tailWord_316663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316707 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 1, 5]
def baseStart_316707 : Nat := 118140960795 + 316707 * 2 ^ 59
def prefixEnd_316707 : Nat := 4983230072969 + 3 ^ 40 * 316707 * 2
def baseEnd_316707 : Nat := 54207639214532538701999

theorem tailTrace_316707 : CollatzResearch.WordTrace tailWord_316707 prefixEnd_316707 54207639214532538701999 := by
  unfold tailWord_316707
  simp only [CollatzResearch.WordTrace]
  refine ⟨11551253263632103094444375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7700835509088068729629583 11551253263632103094444375)
  ·
    refine ⟨17326879895448154641666563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11551253263632103094444375 17326879895448154641666563)
    ·
      refine ⟨25990319843172231962499845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17326879895448154641666563 25990319843172231962499845)
      ·
        refine ⟨4873184970594793492968721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25990319843172231962499845 4873184970594793492968721)
        ·
          refine ⟨3654888727946095119726541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4873184970594793492968721 3654888727946095119726541)
          ·
            refine ⟨1370583272979785669897453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3654888727946095119726541 1370583272979785669897453)
            ·
              refine ⟨513968727367419626211545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1370583272979785669897453 513968727367419626211545)
              ·
                refine ⟨385476545525564719658659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513968727367419626211545 385476545525564719658659)
                ·
                  refine ⟨578214818288347079487989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385476545525564719658659 578214818288347079487989)
                  ·
                    refine ⟨54207639214532538701999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 578214818288347079487989 54207639214532538701999)
                    ·
                      rfl

theorem cell23_316707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 5].length) (baseStart_316707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316707 prefixEnd_316707 := by exact prefixLift 316707
  have htrace : WordTrace (prefixWord ++ tailWord_316707) baseStart_316707 baseEnd_316707 := by
    simpa [prefixWord, tailWord_316707, baseEnd_316707] using wordTrace_append hprefix tailTrace_316707
  have hstable : (prefixWord ++ tailWord_316707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316707).length < 2 ^ (prefixWord ++ tailWord_316707).sum := by decide
  have hdescent : baseEnd_316707 < baseStart_316707 := by decide
  rcases family_descends (prefixWord ++ tailWord_316707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316720 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_316720 : Nat := 118140960795 + 316720 * 2 ^ 59
def prefixEnd_316720 : Nat := 4983230072969 + 3 ^ 40 * 316720 * 2
def baseEnd_316720 : Nat := 54209864297368688414479

theorem tailTrace_316720 : CollatzResearch.WordTrace tailWord_316720 prefixEnd_316720 54209864297368688414479 := by
  unfold tailWord_316720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775863706292503157333807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7701151608390004209778409 5775863706292503157333807)
  ·
    refine ⟨8663795559438754736000711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775863706292503157333807 8663795559438754736000711)
    ·
      refine ⟨12995693339158132104001067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663795559438754736000711 12995693339158132104001067)
      ·
        refine ⟨19493540008737198156001601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12995693339158132104001067 19493540008737198156001601)
        ·
          refine ⟨14620155006552898617001201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19493540008737198156001601 14620155006552898617001201)
          ·
            refine ⟨10965116254914673962750901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14620155006552898617001201 10965116254914673962750901)
            ·
              refine ⟨1027979648898250684007897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10965116254914673962750901 1027979648898250684007897)
              ·
                refine ⟨770984736673688013005923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027979648898250684007897 770984736673688013005923)
                ·
                  refine ⟨1156477105010532019508885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770984736673688013005923 1156477105010532019508885)
                  ·
                    refine ⟨54209864297368688414479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1156477105010532019508885 54209864297368688414479)
                    ·
                      rfl

theorem cell23_316720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_316720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316720 prefixEnd_316720 := by exact prefixLift 316720
  have htrace : WordTrace (prefixWord ++ tailWord_316720) baseStart_316720 baseEnd_316720 := by
    simpa [prefixWord, tailWord_316720, baseEnd_316720] using wordTrace_append hprefix tailTrace_316720
  have hstable : (prefixWord ++ tailWord_316720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316720).length < 2 ^ (prefixWord ++ tailWord_316720).sum := by decide
  have hdescent : baseEnd_316720 < baseStart_316720 := by decide
  rcases family_descends (prefixWord ++ tailWord_316720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316744 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_316744 : Nat := 118140960795 + 316744 * 2 ^ 59
def prefixEnd_316744 : Nat := 4983230072969 + 3 ^ 40 * 316744 * 2
def baseEnd_316744 : Nat := 162641916427813971343327

theorem tailTrace_316744 : CollatzResearch.WordTrace tailWord_316744 prefixEnd_316744 162641916427813971343327 := by
  unfold tailWord_316744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776301382249029206770643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7701735176332038942360857 5776301382249029206770643)
  ·
    refine ⟨8664452073373543810155965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5776301382249029206770643 8664452073373543810155965)
    ·
      refine ⟨3249169527515078928808487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8664452073373543810155965 3249169527515078928808487)
      ·
        refine ⟨4873754291272618393212731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249169527515078928808487 4873754291272618393212731)
        ·
          refine ⟨7310631436908927589819097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873754291272618393212731 7310631436908927589819097)
          ·
            refine ⟨5482973577681695692364323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7310631436908927589819097 5482973577681695692364323)
            ·
              refine ⟨8224460366522543538546485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482973577681695692364323 8224460366522543538546485)
              ·
                refine ⟨771043159361488456738733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8224460366522543538546485 771043159361488456738733)
                ·
                  refine ⟨289141184760558171277025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771043159361488456738733 289141184760558171277025)
                  ·
                    refine ⟨216855888570418628457769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 289141184760558171277025 216855888570418628457769)
                    ·
                      refine ⟨162641916427813971343327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216855888570418628457769 162641916427813971343327)
                      ·
                        rfl

theorem cell23_316744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_316744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316744 prefixEnd_316744 := by exact prefixLift 316744
  have htrace : WordTrace (prefixWord ++ tailWord_316744) baseStart_316744 baseEnd_316744 := by
    simpa [prefixWord, tailWord_316744, baseEnd_316744] using wordTrace_append hprefix tailTrace_316744
  have hstable : (prefixWord ++ tailWord_316744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316744).length < 2 ^ (prefixWord ++ tailWord_316744).sum := by decide
  have hdescent : baseEnd_316744 < baseStart_316744 := by decide
  rcases family_descends (prefixWord ++ tailWord_316744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316757 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_316757 : Nat := 118140960795 + 316757 * 2 ^ 59
def prefixEnd_316757 : Nat := 4983230072969 + 3 ^ 40 * 316757 * 2
def baseEnd_316757 : Nat := 162648591676322420480767

theorem tailTrace_316757 : CollatzResearch.WordTrace tailWord_316757 prefixEnd_316757 162648591676322420480767 := by
  unfold tailWord_316757
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553076913450961633764525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7702051275633974422509683 11553076913450961633764525)
  ·
    refine ⟨4332403842544110612661697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11553076913450961633764525 4332403842544110612661697)
    ·
      refine ⟨3249302881908082959496273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4332403842544110612661697 3249302881908082959496273)
      ·
        refine ⟨2436977161431062219622205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249302881908082959496273 2436977161431062219622205)
        ·
          refine ⟨913866435536648332358327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2436977161431062219622205 913866435536648332358327)
          ·
            refine ⟨1370799653304972498537491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913866435536648332358327 1370799653304972498537491)
            ·
              refine ⟨2056199479957458747806237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370799653304972498537491 2056199479957458747806237)
              ·
                refine ⟨771074804984047030427339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056199479957458747806237 771074804984047030427339)
                ·
                  refine ⟨1156612207476070545641009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771074804984047030427339 1156612207476070545641009)
                  ·
                    refine ⟨867459155607052909230757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156612207476070545641009 867459155607052909230757)
                    ·
                      refine ⟨162648591676322420480767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 867459155607052909230757 162648591676322420480767)
                      ·
                        rfl

theorem cell23_316757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_316757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316757 prefixEnd_316757 := by exact prefixLift 316757
  have htrace : WordTrace (prefixWord ++ tailWord_316757) baseStart_316757 baseEnd_316757 := by
    simpa [prefixWord, tailWord_316757, baseEnd_316757] using wordTrace_append hprefix tailTrace_316757
  have hstable : (prefixWord ++ tailWord_316757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316757).length < 2 ^ (prefixWord ++ tailWord_316757).sum := by decide
  have hdescent : baseEnd_316757 < baseStart_316757 := by decide
  rcases family_descends (prefixWord ++ tailWord_316757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316778 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_316778 : Nat := 118140960795 + 316778 * 2 ^ 59
def prefixEnd_316778 : Nat := 4983230072969 + 3 ^ 40 * 316778 * 2
def baseEnd_316778 : Nat := 162659374770066838318171

theorem tailTrace_316778 : CollatzResearch.WordTrace tailWord_316778 prefixEnd_316778 162659374770066838318171 := by
  unfold tailWord_316778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888460711593720555069747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7702561897583254813519325 2888460711593720555069747)
  ·
    refine ⟨4332691067390580832604621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2888460711593720555069747 4332691067390580832604621)
    ·
      refine ⟨1624759150271467812226733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4332691067390580832604621 1624759150271467812226733)
      ·
        refine ⟨609284681351800429585025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1624759150271467812226733 609284681351800429585025)
        ·
          refine ⟨456963511013850322188769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609284681351800429585025 456963511013850322188769)
          ·
            refine ⟨342722633260387741641577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456963511013850322188769 342722633260387741641577)
            ·
              refine ⟨257041974945290806231183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342722633260387741641577 257041974945290806231183)
              ·
                refine ⟨385562962417936209346775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257041974945290806231183 385562962417936209346775)
                ·
                  refine ⟨578344443626904314020163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385562962417936209346775 578344443626904314020163)
                  ·
                    refine ⟨867516665440356471030245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578344443626904314020163 867516665440356471030245)
                    ·
                      refine ⟨162659374770066838318171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 867516665440356471030245 162659374770066838318171)
                      ·
                        rfl

theorem cell23_316778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_316778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316778 prefixEnd_316778 := by exact prefixLift 316778
  have htrace : WordTrace (prefixWord ++ tailWord_316778) baseStart_316778 baseEnd_316778 := by
    simpa [prefixWord, tailWord_316778, baseEnd_316778] using wordTrace_append hprefix tailTrace_316778
  have hstable : (prefixWord ++ tailWord_316778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316778).length < 2 ^ (prefixWord ++ tailWord_316778).sum := by decide
  have hdescent : baseEnd_316778 < baseStart_316778 := by decide
  rcases family_descends (prefixWord ++ tailWord_316778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316781 : List Nat := [1, 5, 1, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_316781 : Nat := 118140960795 + 316781 * 2 ^ 59
def prefixEnd_316781 : Nat := 4983230072969 + 3 ^ 40 * 316781 * 2
def baseEnd_316781 : Nat := 162660915212030326580657

theorem tailTrace_316781 : CollatzResearch.WordTrace tailWord_316781 prefixEnd_316781 162660915212030326580657 := by
  unfold tailWord_316781
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553952265364013732638197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7702634843576009155092131 11553952265364013732638197)
  ·
    refine ⟨1083183024877876287434831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11553952265364013732638197 1083183024877876287434831)
    ·
      refine ⟨1624774537316814431152247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083183024877876287434831 1624774537316814431152247)
      ·
        refine ⟨2437161805975221646728371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624774537316814431152247 2437161805975221646728371)
        ·
          refine ⟨3655742708962832470092557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437161805975221646728371 3655742708962832470092557)
          ·
            refine ⟨1370903515861062176284709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655742708962832470092557 1370903515861062176284709)
            ·
              refine ⟨257044409223949158053383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1370903515861062176284709 257044409223949158053383)
              ·
                refine ⟨385566613835923737080075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257044409223949158053383 385566613835923737080075)
                ·
                  refine ⟨578349920753885605620113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385566613835923737080075 578349920753885605620113)
                  ·
                    refine ⟨433762440565414204215085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578349920753885605620113 433762440565414204215085)
                    ·
                      refine ⟨162660915212030326580657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433762440565414204215085 162660915212030326580657)
                      ·
                        rfl

theorem cell23_316781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_316781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316781 prefixEnd_316781 := by exact prefixLift 316781
  have htrace : WordTrace (prefixWord ++ tailWord_316781) baseStart_316781 baseEnd_316781 := by
    simpa [prefixWord, tailWord_316781, baseEnd_316781] using wordTrace_append hprefix tailTrace_316781
  have hstable : (prefixWord ++ tailWord_316781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316781).length < 2 ^ (prefixWord ++ tailWord_316781).sum := by decide
  have hdescent : baseEnd_316781 < baseStart_316781 := by decide
  rcases family_descends (prefixWord ++ tailWord_316781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316800 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_316800 : Nat := 118140960795 + 316800 * 2 ^ 59
def prefixEnd_316800 : Nat := 4983230072969 + 3 ^ 40 * 316800 * 2
def baseEnd_316800 : Nat := 162670671344465752243069

theorem tailTrace_316800 : CollatzResearch.WordTrace tailWord_316800 prefixEnd_316800 162670671344465752243069 := by
  unfold tailWord_316800
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777322626147589988789927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7703096834863453318386569 5777322626147589988789927)
  ·
    refine ⟨8665983939221384983184891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5777322626147589988789927 8665983939221384983184891)
    ·
      refine ⟨12998975908832077474777337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665983939221384983184891 12998975908832077474777337)
      ·
        refine ⟨9749231931624058106083003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12998975908832077474777337 9749231931624058106083003)
        ·
          refine ⟨14623847897436087159124505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9749231931624058106083003 14623847897436087159124505)
          ·
            refine ⟨10967885923077065369343379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14623847897436087159124505 10967885923077065369343379)
            ·
              refine ⟨16451828884615598054015069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967885923077065369343379 16451828884615598054015069)
              ·
                refine ⟨6169435831730849270255651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451828884615598054015069 6169435831730849270255651)
                ·
                  refine ⟨9254153747596273905383477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169435831730849270255651 9254153747596273905383477)
                  ·
                    refine ⟨867576913837150678629701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9254153747596273905383477 867576913837150678629701)
                    ·
                      refine ⟨162670671344465752243069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 867576913837150678629701 162670671344465752243069)
                      ·
                        rfl

theorem cell23_316800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_316800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316800 prefixEnd_316800 := by exact prefixLift 316800
  have htrace : WordTrace (prefixWord ++ tailWord_316800) baseStart_316800 baseEnd_316800 := by
    simpa [prefixWord, tailWord_316800, baseEnd_316800] using wordTrace_append hprefix tailTrace_316800
  have hstable : (prefixWord ++ tailWord_316800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316800).length < 2 ^ (prefixWord ++ tailWord_316800).sum := by decide
  have hdescent : baseEnd_316800 < baseStart_316800 := by decide
  rcases family_descends (prefixWord ++ tailWord_316800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316811 : List Nat := [1, 1, 1, 1, 4, 3, 5, 1, 2, 1, 3]
def baseStart_316811 : Nat := 118140960795 + 316811 * 2 ^ 59
def prefixEnd_316811 : Nat := 4983230072969 + 3 ^ 40 * 316811 * 2
def baseEnd_316811 : Nat := 162676319631665209205519

theorem tailTrace_316811 : CollatzResearch.WordTrace tailWord_316811 prefixEnd_316811 162676319631665209205519 := by
  unfold tailWord_316811
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555046455255328856230287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7703364303503552570820191 11555046455255328856230287)
  ·
    refine ⟨17332569682882993284345431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11555046455255328856230287 17332569682882993284345431)
    ·
      refine ⟨25998854524324489926518147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17332569682882993284345431 25998854524324489926518147)
      ·
        refine ⟨38998281786486734889777221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25998854524324489926518147 38998281786486734889777221)
        ·
          refine ⟨7312177834966262791833229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38998281786486734889777221 7312177834966262791833229)
          ·
            refine ⟨2742066688112348546937461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7312177834966262791833229 2742066688112348546937461)
            ·
              refine ⟨257068752010532676275387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2742066688112348546937461 257068752010532676275387)
              ·
                refine ⟨385603128015799014413081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257068752010532676275387 385603128015799014413081)
                ·
                  refine ⟨289202346011849260809811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385603128015799014413081 289202346011849260809811)
                  ·
                    refine ⟨433803519017773891214717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289202346011849260809811 433803519017773891214717)
                    ·
                      refine ⟨162676319631665209205519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433803519017773891214717 162676319631665209205519)
                      ·
                        rfl

theorem cell23_316811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 2, 1, 3].length) (baseStart_316811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316811 prefixEnd_316811 := by exact prefixLift 316811
  have htrace : WordTrace (prefixWord ++ tailWord_316811) baseStart_316811 baseEnd_316811 := by
    simpa [prefixWord, tailWord_316811, baseEnd_316811] using wordTrace_append hprefix tailTrace_316811
  have hstable : (prefixWord ++ tailWord_316811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316811).length < 2 ^ (prefixWord ++ tailWord_316811).sum := by decide
  have hdescent : baseEnd_316811 < baseStart_316811 := by decide
  rcases family_descends (prefixWord ++ tailWord_316811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316818 : List Nat := [3, 2, 3, 3, 2, 1, 2, 7]
def baseStart_316818 : Nat := 118140960795 + 316818 * 2 ^ 59
def prefixEnd_316818 : Nat := 4983230072969 + 3 ^ 40 * 316818 * 2
def baseEnd_316818 : Nat := 6025181999860988215481

theorem tailTrace_316818 : CollatzResearch.WordTrace tailWord_316818 prefixEnd_316818 6025181999860988215481 := by
  unfold tailWord_316818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888825441557492262933777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7703534510819979367823405 2888825441557492262933777)
  ·
    refine ⟨2166619081168119197200333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2888825441557492262933777 2166619081168119197200333)
    ·
      refine ⟨812482155438044698950125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2166619081168119197200333 812482155438044698950125)
      ·
        refine ⟨304680808289266762106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 812482155438044698950125 304680808289266762106297)
        ·
          refine ⟨228510606216950071579723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304680808289266762106297 228510606216950071579723)
          ·
            refine ⟨342765909325425107369585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228510606216950071579723 342765909325425107369585)
            ·
              refine ⟨257074431994068830527189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342765909325425107369585 257074431994068830527189)
              ·
                refine ⟨6025181999860988215481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 257074431994068830527189 6025181999860988215481)
                ·
                  rfl

theorem cell23_316818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_316818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316818 prefixEnd_316818 := by exact prefixLift 316818
  have htrace : WordTrace (prefixWord ++ tailWord_316818) baseStart_316818 baseEnd_316818 := by
    simpa [prefixWord, tailWord_316818, baseEnd_316818] using wordTrace_append hprefix tailTrace_316818
  have hstable : (prefixWord ++ tailWord_316818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316818).length < 2 ^ (prefixWord ++ tailWord_316818).sum := by decide
  have hdescent : baseEnd_316818 < baseStart_316818 := by decide
  rcases family_descends (prefixWord ++ tailWord_316818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316867 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3]
def baseStart_316867 : Nat := 118140960795 + 316867 * 2 ^ 59
def prefixEnd_316867 : Nat := 4983230072969 + 3 ^ 40 * 316867 * 2
def baseEnd_316867 : Nat := 162705074548316990105261

theorem tailTrace_316867 : CollatzResearch.WordTrace tailWord_316867 prefixEnd_316867 162705074548316990105261 := by
  unfold tailWord_316867
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557088943052450420268855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7704725962034966946845903 11557088943052450420268855)
  ·
    refine ⟨17335633414578675630403283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11557088943052450420268855 17335633414578675630403283)
    ·
      refine ⟨26003450121868013445604925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17335633414578675630403283 26003450121868013445604925)
      ·
        refine ⟨9751293795700505042101847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26003450121868013445604925 9751293795700505042101847)
        ·
          refine ⟨14626940693550757563152771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751293795700505042101847 14626940693550757563152771)
          ·
            refine ⟨21940411040326136344729157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14626940693550757563152771 21940411040326136344729157)
            ·
              refine ⟨4113827070061150564636717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21940411040326136344729157 4113827070061150564636717)
              ·
                refine ⟨1542685151272931461738769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113827070061150564636717 1542685151272931461738769)
                ·
                  refine ⟨1157013863454698596304077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542685151272931461738769 1157013863454698596304077)
                  ·
                    refine ⟨433880198795511973614029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157013863454698596304077 433880198795511973614029)
                    ·
                      refine ⟨162705074548316990105261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 433880198795511973614029 162705074548316990105261)
                      ·
                        rfl

theorem cell23_316867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_316867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316867 prefixEnd_316867 := by exact prefixLift 316867
  have htrace : WordTrace (prefixWord ++ tailWord_316867) baseStart_316867 baseEnd_316867 := by
    simpa [prefixWord, tailWord_316867, baseEnd_316867] using wordTrace_append hprefix tailTrace_316867
  have hstable : (prefixWord ++ tailWord_316867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316867).length < 2 ^ (prefixWord ++ tailWord_316867).sum := by decide
  have hdescent : baseEnd_316867 < baseStart_316867 := by decide
  rcases family_descends (prefixWord ++ tailWord_316867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316897 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_316897 : Nat := 118140960795 + 316897 * 2 ^ 59
def prefixEnd_316897 : Nat := 4983230072969 + 3 ^ 40 * 316897 * 2
def baseEnd_316897 : Nat := 162720478967951872730123

theorem tailTrace_316897 : CollatzResearch.WordTrace tailWord_316897 prefixEnd_316897 162720478967951872730123 := by
  unfold tailWord_316897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558183132943765543860945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7705455421962510362573963 11558183132943765543860945)
  ·
    refine ⟨8668637349707824157895709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11558183132943765543860945 8668637349707824157895709)
    ·
      refine ⟨3250739006140434059210891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8668637349707824157895709 3250739006140434059210891)
      ·
        refine ⟨4876108509210651088816337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250739006140434059210891 4876108509210651088816337)
        ·
          refine ⟨3657081381907988316612253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876108509210651088816337 3657081381907988316612253)
          ·
            refine ⟨1371405518215495618729595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3657081381907988316612253 1371405518215495618729595)
            ·
              refine ⟨2057108277323243428094393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371405518215495618729595 2057108277323243428094393)
              ·
                refine ⟨1542831207992432571070795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057108277323243428094393 1542831207992432571070795)
                ·
                  refine ⟨2314246811988648856606193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542831207992432571070795 2314246811988648856606193)
                  ·
                    refine ⟨1735685108991486642454645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314246811988648856606193 1735685108991486642454645)
                    ·
                      refine ⟨162720478967951872730123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1735685108991486642454645 162720478967951872730123)
                      ·
                        rfl

theorem cell23_316897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_316897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316897 prefixEnd_316897 := by exact prefixLift 316897
  have htrace : WordTrace (prefixWord ++ tailWord_316897) baseStart_316897 baseEnd_316897 := by
    simpa [prefixWord, tailWord_316897, baseEnd_316897] using wordTrace_append hprefix tailTrace_316897
  have hstable : (prefixWord ++ tailWord_316897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316897).length < 2 ^ (prefixWord ++ tailWord_316897).sum := by decide
  have hdescent : baseEnd_316897 < baseStart_316897 := by decide
  rcases family_descends (prefixWord ++ tailWord_316897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316907 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4]
def baseStart_316907 : Nat := 118140960795 + 316907 * 2 ^ 59
def prefixEnd_316907 : Nat := 4983230072969 + 3 ^ 40 * 316907 * 2
def baseEnd_316907 : Nat := 162725613774496833605077

theorem tailTrace_316907 : CollatzResearch.WordTrace tailWord_316907 prefixEnd_316907 162725613774496833605077 := by
  unfold tailWord_316907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558547862907537251724975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7705698575271691501149983 11558547862907537251724975)
  ·
    refine ⟨17337821794361305877587463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11558547862907537251724975 17337821794361305877587463)
    ·
      refine ⟨26006732691541958816381195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17337821794361305877587463 26006732691541958816381195)
      ·
        refine ⟨39010099037312938224571793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26006732691541958816381195 39010099037312938224571793)
        ·
          refine ⟨29257574277984703668428845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39010099037312938224571793 29257574277984703668428845)
          ·
            refine ⟨10971590354244263875660817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29257574277984703668428845 10971590354244263875660817)
            ·
              refine ⟨8228692765683197906745613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10971590354244263875660817 8228692765683197906745613)
              ·
                refine ⟨3085759787131199215029605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8228692765683197906745613 3085759787131199215029605)
                ·
                  refine ⟨578579960087099852818051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3085759787131199215029605 578579960087099852818051)
                  ·
                    refine ⟨867869940130649779227077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578579960087099852818051 867869940130649779227077)
                    ·
                      refine ⟨162725613774496833605077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 867869940130649779227077 162725613774496833605077)
                      ·
                        rfl

theorem cell23_316907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_316907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316907 prefixEnd_316907 := by exact prefixLift 316907
  have htrace : WordTrace (prefixWord ++ tailWord_316907) baseStart_316907 baseEnd_316907 := by
    simpa [prefixWord, tailWord_316907, baseEnd_316907] using wordTrace_append hprefix tailTrace_316907
  have hstable : (prefixWord ++ tailWord_316907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316907).length < 2 ^ (prefixWord ++ tailWord_316907).sum := by decide
  have hdescent : baseEnd_316907 < baseStart_316907 := by decide
  rcases family_descends (prefixWord ++ tailWord_316907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316914 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_316914 : Nat := 118140960795 + 316914 * 2 ^ 59
def prefixEnd_316914 : Nat := 4983230072969 + 3 ^ 40 * 316914 * 2
def baseEnd_316914 : Nat := 162729208139078306217545

theorem tailTrace_316914 : CollatzResearch.WordTrace tailWord_316914 prefixEnd_316914 162729208139078306217545 := by
  unfold tailWord_316914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889700793470544361807449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7705868782588118298153197 2889700793470544361807449)
  ·
    refine ⟨2167275595102908271355587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2889700793470544361807449 2167275595102908271355587)
    ·
      refine ⟨3250913392654362407033381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167275595102908271355587 3250913392654362407033381)
      ·
        refine ⟨609546261122692951318759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3250913392654362407033381 609546261122692951318759)
        ·
          refine ⟨914319391684039426978139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609546261122692951318759 914319391684039426978139)
          ·
            refine ⟨1371479087526059140467209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914319391684039426978139 1371479087526059140467209)
            ·
              refine ⟨1028609315644544355350407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371479087526059140467209 1028609315644544355350407)
              ·
                refine ⟨1542913973466816533025611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028609315644544355350407 1542913973466816533025611)
                ·
                  refine ⟨2314370960200224799538417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542913973466816533025611 2314370960200224799538417)
                  ·
                    refine ⟨1735778220150168599653813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314370960200224799538417 1735778220150168599653813)
                    ·
                      refine ⟨162729208139078306217545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1735778220150168599653813 162729208139078306217545)
                      ·
                        rfl

theorem cell23_316914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_316914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316914 prefixEnd_316914 := by exact prefixLift 316914
  have htrace : WordTrace (prefixWord ++ tailWord_316914) baseStart_316914 baseEnd_316914 := by
    simpa [prefixWord, tailWord_316914, baseEnd_316914] using wordTrace_append hprefix tailTrace_316914
  have hstable : (prefixWord ++ tailWord_316914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316914).length < 2 ^ (prefixWord ++ tailWord_316914).sum := by decide
  have hdescent : baseEnd_316914 < baseStart_316914 := by decide
  rcases family_descends (prefixWord ++ tailWord_316914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316924 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_316924 : Nat := 118140960795 + 316924 * 2 ^ 59
def prefixEnd_316924 : Nat := 4983230072969 + 3 ^ 40 * 316924 * 2
def baseEnd_316924 : Nat := 162734342945623267092499

theorem tailTrace_316924 : CollatzResearch.WordTrace tailWord_316924 prefixEnd_316924 162734342945623267092499 := by
  unfold tailWord_316924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779583951922974577546913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7706111935897299436729217 5779583951922974577546913)
  ·
    refine ⟨4334687963942230933160185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5779583951922974577546913 4334687963942230933160185)
    ·
      refine ⟨3251015972956673199870139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334687963942230933160185 3251015972956673199870139)
      ·
        refine ⟨4876523959435009799805209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251015972956673199870139 4876523959435009799805209)
        ·
          refine ⟨3657392969576257349853907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876523959435009799805209 3657392969576257349853907)
          ·
            refine ⟨5486089454364386024780861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657392969576257349853907 5486089454364386024780861)
            ·
              refine ⟨2057283545386644759292823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5486089454364386024780861 2057283545386644759292823)
              ·
                refine ⟨3085925318079967138939235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057283545386644759292823 3085925318079967138939235)
                ·
                  refine ⟨4628887977119950708408853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085925318079967138939235 4628887977119950708408853)
                  ·
                    refine ⟨216979123927497689456665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4628887977119950708408853 216979123927497689456665)
                    ·
                      refine ⟨162734342945623267092499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 216979123927497689456665 162734342945623267092499)
                      ·
                        rfl

theorem cell23_316924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_316924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316924 prefixEnd_316924 := by exact prefixLift 316924
  have htrace : WordTrace (prefixWord ++ tailWord_316924) baseStart_316924 baseEnd_316924 := by
    simpa [prefixWord, tailWord_316924, baseEnd_316924] using wordTrace_append hprefix tailTrace_316924
  have hstable : (prefixWord ++ tailWord_316924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316924).length < 2 ^ (prefixWord ++ tailWord_316924).sum := by decide
  have hdescent : baseEnd_316924 < baseStart_316924 := by decide
  rcases family_descends (prefixWord ++ tailWord_316924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316968 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_316968 : Nat := 118140960795 + 316968 * 2 ^ 59
def prefixEnd_316968 : Nat := 4983230072969 + 3 ^ 40 * 316968 * 2
def baseEnd_316968 : Nat := 54252312031473698314099

theorem tailTrace_316968 : CollatzResearch.WordTrace tailWord_316968 prefixEnd_316968 54252312031473698314099 := by
  unfold tailWord_316968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780386357843272334847779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7707181810457696446463705 5780386357843272334847779)
  ·
    refine ⟨8670579536764908502271669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5780386357843272334847779 8670579536764908502271669)
    ·
      refine ⟨812866831571710172087969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8670579536764908502271669 812866831571710172087969)
      ·
        refine ⟨609650123678782629065977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812866831571710172087969 609650123678782629065977)
        ·
          refine ⟨457237592759086971799483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609650123678782629065977 457237592759086971799483)
          ·
            refine ⟨685856389138630457699225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457237592759086971799483 685856389138630457699225)
            ·
              refine ⟨514392291853972843274419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685856389138630457699225 514392291853972843274419)
              ·
                refine ⟨771588437780959264911629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514392291853972843274419 771588437780959264911629)
                ·
                  refine ⟨289345664167859724341861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771588437780959264911629 289345664167859724341861)
                  ·
                    refine ⟨54252312031473698314099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 289345664167859724341861 54252312031473698314099)
                    ·
                      rfl

theorem cell23_316968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_316968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316968 prefixEnd_316968 := by exact prefixLift 316968
  have htrace : WordTrace (prefixWord ++ tailWord_316968) baseStart_316968 baseEnd_316968 := by
    simpa [prefixWord, tailWord_316968, baseEnd_316968] using wordTrace_append hprefix tailTrace_316968
  have hstable : (prefixWord ++ tailWord_316968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316968).length < 2 ^ (prefixWord ++ tailWord_316968).sum := by decide
  have hdescent : baseEnd_316968 < baseStart_316968 := by decide
  rcases family_descends (prefixWord ++ tailWord_316968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316981 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 6]
def baseStart_316981 : Nat := 118140960795 + 316981 * 2 ^ 59
def prefixEnd_316981 : Nat := 4983230072969 + 3 ^ 40 * 316981 * 2
def baseEnd_316981 : Nat := 18084845704769949342193

theorem tailTrace_316981 : CollatzResearch.WordTrace tailWord_316981 prefixEnd_316981 18084845704769949342193 := by
  unfold tailWord_316981
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561246864639447889918797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7707497909759631926612531 11561246864639447889918797)
  ·
    refine ⟨4335467574239792958719549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11561246864639447889918797 4335467574239792958719549)
    ·
      refine ⟨1625800340339922359519831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4335467574239792958719549 1625800340339922359519831)
      ·
        refine ⟨2438700510509883539279747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625800340339922359519831 2438700510509883539279747)
        ·
          refine ⟨3658050765764825308919621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438700510509883539279747 3658050765764825308919621)
          ·
            refine ⟨685884518580904745422429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3658050765764825308919621 685884518580904745422429)
            ·
              refine ⟨257206694467839279533411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 685884518580904745422429 257206694467839279533411)
              ·
                refine ⟨385810041701758919300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257206694467839279533411 385810041701758919300117)
                ·
                  refine ⟨18084845704769949342193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 385810041701758919300117 18084845704769949342193)
                  ·
                    rfl

theorem cell23_316981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_316981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316981 prefixEnd_316981 := by exact prefixLift 316981
  have htrace : WordTrace (prefixWord ++ tailWord_316981) baseStart_316981 baseEnd_316981 := by
    simpa [prefixWord, tailWord_316981, baseEnd_316981] using wordTrace_append hprefix tailTrace_316981
  have hstable : (prefixWord ++ tailWord_316981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316981).length < 2 ^ (prefixWord ++ tailWord_316981).sum := by decide
  have hdescent : baseEnd_316981 < baseStart_316981 := by decide
  rcases family_descends (prefixWord ++ tailWord_316981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316991 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_316991 : Nat := 118140960795 + 316991 * 2 ^ 59
def prefixEnd_316991 : Nat := 4983230072969 + 3 ^ 40 * 316991 * 2
def baseEnd_316991 : Nat := 162768746149474504954691

theorem tailTrace_316991 : CollatzResearch.WordTrace tailWord_316991 prefixEnd_316991 162768746149474504954691 := by
  unfold tailWord_316991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561611594603219597782827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7707741063068813065188551 11561611594603219597782827)
  ·
    refine ⟨17342417391904829396674241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561611594603219597782827 17342417391904829396674241)
    ·
      refine ⟨13006813043928622047505681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17342417391904829396674241 13006813043928622047505681)
      ·
        refine ⟨9755109782946466535629261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13006813043928622047505681 9755109782946466535629261)
        ·
          refine ⟨3658166168604924950860973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9755109782946466535629261 3658166168604924950860973)
          ·
            refine ⟨1371812313226846856572865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658166168604924950860973 1371812313226846856572865)
            ·
              refine ⟨1028859234920135142429649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371812313226846856572865 1028859234920135142429649)
              ·
                refine ⟨771644426190101356822237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028859234920135142429649 771644426190101356822237)
                ·
                  refine ⟨289366659821288008808339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 771644426190101356822237 289366659821288008808339)
                  ·
                    refine ⟨434049989731932013212509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289366659821288008808339 434049989731932013212509)
                    ·
                      refine ⟨162768746149474504954691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434049989731932013212509 162768746149474504954691)
                      ·
                        rfl

theorem cell23_316991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_316991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_316991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_316991 prefixEnd_316991 := by exact prefixLift 316991
  have htrace : WordTrace (prefixWord ++ tailWord_316991) baseStart_316991 baseEnd_316991 := by
    simpa [prefixWord, tailWord_316991, baseEnd_316991] using wordTrace_append hprefix tailTrace_316991
  have hstable : (prefixWord ++ tailWord_316991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316991).length < 2 ^ (prefixWord ++ tailWord_316991).sum := by decide
  have hdescent : baseEnd_316991 < baseStart_316991 := by decide
  rcases family_descends (prefixWord ++ tailWord_316991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317007 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 3, 6]
def baseStart_317007 : Nat := 118140960795 + 317007 * 2 ^ 59
def prefixEnd_317007 : Nat := 4983230072969 + 3 ^ 40 * 317007 * 2
def baseEnd_317007 : Nat := 54258987279982147451539

theorem tailTrace_317007 : CollatzResearch.WordTrace tailWord_317007 prefixEnd_317007 54258987279982147451539 := by
  unfold tailWord_317007
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562195162545254330365275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7708130108363502886910183 11562195162545254330365275)
  ·
    refine ⟨17343292743817881495547913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562195162545254330365275 17343292743817881495547913)
    ·
      refine ⟨13007469557863411121660935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17343292743817881495547913 13007469557863411121660935)
      ·
        refine ⟨19511204336795116682491403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13007469557863411121660935 19511204336795116682491403)
        ·
          refine ⟨29266806505192675023737105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19511204336795116682491403 29266806505192675023737105)
          ·
            refine ⟨21950104878894506267802829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29266806505192675023737105 21950104878894506267802829)
            ·
              refine ⟨8231289329585439850426061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21950104878894506267802829 8231289329585439850426061)
              ·
                refine ⟨3086733498594539943909773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231289329585439850426061 3086733498594539943909773)
                ·
                  refine ⟨1157525061972952478966165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3086733498594539943909773 1157525061972952478966165)
                  ·
                    refine ⟨54258987279982147451539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1157525061972952478966165 54258987279982147451539)
                    ·
                      rfl

theorem cell23_317007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_317007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317007 prefixEnd_317007 := by exact prefixLift 317007
  have htrace : WordTrace (prefixWord ++ tailWord_317007) baseStart_317007 baseEnd_317007 := by
    simpa [prefixWord, tailWord_317007, baseEnd_317007] using wordTrace_append hprefix tailTrace_317007
  have hstable : (prefixWord ++ tailWord_317007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317007).length < 2 ^ (prefixWord ++ tailWord_317007).sum := by decide
  have hdescent : baseEnd_317007 < baseStart_317007 := by decide
  rcases family_descends (prefixWord ++ tailWord_317007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317025 : List Nat := [1, 2, 3, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_317025 : Nat := 118140960795 + 317025 * 2 ^ 59
def prefixEnd_317025 : Nat := 4983230072969 + 3 ^ 40 * 317025 * 2
def baseEnd_317025 : Nat := 162786204491727371929535

theorem tailTrace_317025 : CollatzResearch.WordTrace tailWord_317025 prefixEnd_317025 162786204491727371929535 := by
  unfold tailWord_317025
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562851676480043404520529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7708567784320028936347019 11562851676480043404520529)
  ·
    refine ⟨8672138757360032553390397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11562851676480043404520529 8672138757360032553390397)
    ·
      refine ⟨3252052034010012207521399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8672138757360032553390397 3252052034010012207521399)
      ·
        refine ⟨4878078051015018311282099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252052034010012207521399 4878078051015018311282099)
        ·
          refine ⟨7317117076522527466923149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878078051015018311282099 7317117076522527466923149)
          ·
            refine ⟨2743918903695947800096181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7317117076522527466923149 2743918903695947800096181)
            ·
              refine ⟨257242397221495106259017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2743918903695947800096181 257242397221495106259017)
              ·
                refine ⟨192931797916121329694263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257242397221495106259017 192931797916121329694263)
                ·
                  refine ⟨289397696874181994541395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192931797916121329694263 289397696874181994541395)
                  ·
                    refine ⟨434096545311272991812093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289397696874181994541395 434096545311272991812093)
                    ·
                      refine ⟨162786204491727371929535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434096545311272991812093 162786204491727371929535)
                      ·
                        rfl

theorem cell23_317025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_317025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317025 prefixEnd_317025 := by exact prefixLift 317025
  have htrace : WordTrace (prefixWord ++ tailWord_317025) baseStart_317025 baseEnd_317025 := by
    simpa [prefixWord, tailWord_317025, baseEnd_317025] using wordTrace_append hprefix tailTrace_317025
  have hstable : (prefixWord ++ tailWord_317025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317025).length < 2 ^ (prefixWord ++ tailWord_317025).sum := by decide
  have hdescent : baseEnd_317025 < baseStart_317025 := by decide
  rcases family_descends (prefixWord ++ tailWord_317025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317068 : List Nat := [2, 2, 1, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_317068 : Nat := 118140960795 + 317068 * 2 ^ 59
def prefixEnd_317068 : Nat := 4983230072969 + 3 ^ 40 * 317068 * 2
def baseEnd_317068 : Nat := 162808284159870703691837

theorem tailTrace_317068 : CollatzResearch.WordTrace tailWord_317068 prefixEnd_317068 162808284159870703691837 := by
  unfold tailWord_317068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782210007662130874167929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7709613343549507832223905 5782210007662130874167929)
  ·
    refine ⟨4336657505746598155625947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5782210007662130874167929 4336657505746598155625947)
    ·
      refine ⟨6504986258619897233438921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336657505746598155625947 6504986258619897233438921)
      ·
        refine ⟨4878739693964922925079191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6504986258619897233438921 4878739693964922925079191)
        ·
          refine ⟨7318109540947384387618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878739693964922925079191 7318109540947384387618787)
          ·
            refine ⟨10977164311421076581428181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318109540947384387618787 10977164311421076581428181)
            ·
              refine ⟨257277288548931482377223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10977164311421076581428181 257277288548931482377223)
              ·
                refine ⟨385915932823397223565835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257277288548931482377223 385915932823397223565835)
                ·
                  refine ⟨578873899235095835348753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385915932823397223565835 578873899235095835348753)
                  ·
                    refine ⟨434155424426321876511565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578873899235095835348753 434155424426321876511565)
                    ·
                      refine ⟨162808284159870703691837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434155424426321876511565 162808284159870703691837)
                      ·
                        rfl

theorem cell23_317068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_317068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317068 prefixEnd_317068 := by exact prefixLift 317068
  have htrace : WordTrace (prefixWord ++ tailWord_317068) baseStart_317068 baseEnd_317068 := by
    simpa [prefixWord, tailWord_317068, baseEnd_317068] using wordTrace_append hprefix tailTrace_317068
  have hstable : (prefixWord ++ tailWord_317068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317068).length < 2 ^ (prefixWord ++ tailWord_317068).sum := by decide
  have hdescent : baseEnd_317068 < baseStart_317068 := by decide
  rcases family_descends (prefixWord ++ tailWord_317068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317076 : List Nat := [2, 4, 2, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_317076 : Nat := 118140960795 + 317076 * 2 ^ 59
def prefixEnd_317076 : Nat := 4983230072969 + 3 ^ 40 * 317076 * 2
def baseEnd_317076 : Nat := 162812392005106672391801

theorem tailTrace_317076 : CollatzResearch.WordTrace tailWord_317076 prefixEnd_317076 162812392005106672391801 := by
  unfold tailWord_317076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782355899647639557313541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7709807866196852743084721 5782355899647639557313541)
  ·
    refine ⟨1084191731183932416996289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5782355899647639557313541 1084191731183932416996289)
    ·
      refine ⟨813143798387949312747217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1084191731183932416996289 813143798387949312747217)
      ·
        refine ⟨609857848790961984560413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 813143798387949312747217 609857848790961984560413)
        ·
          refine ⟨228696693296610744210155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609857848790961984560413 228696693296610744210155)
          ·
            refine ⟨343045039944916116315233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228696693296610744210155 343045039944916116315233)
            ·
              refine ⟨257283779958687087236425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343045039944916116315233 257283779958687087236425)
              ·
                refine ⟨192962834969015315427319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257283779958687087236425 192962834969015315427319)
                ·
                  refine ⟨289444252453522973140979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192962834969015315427319 289444252453522973140979)
                  ·
                    refine ⟨434166378680284459711469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289444252453522973140979 434166378680284459711469)
                    ·
                      refine ⟨162812392005106672391801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434166378680284459711469 162812392005106672391801)
                      ·
                        rfl

theorem cell23_317076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_317076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317076 prefixEnd_317076 := by exact prefixLift 317076
  have htrace : WordTrace (prefixWord ++ tailWord_317076) baseStart_317076 baseEnd_317076 := by
    simpa [prefixWord, tailWord_317076, baseEnd_317076] using wordTrace_append hprefix tailTrace_317076
  have hstable : (prefixWord ++ tailWord_317076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317076).length < 2 ^ (prefixWord ++ tailWord_317076).sum := by decide
  have hdescent : baseEnd_317076 < baseStart_317076 := by decide
  rcases family_descends (prefixWord ++ tailWord_317076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317091 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 5, 3, 2]
def baseStart_317091 : Nat := 118140960795 + 317091 * 2 ^ 59
def prefixEnd_317091 : Nat := 4983230072969 + 3 ^ 40 * 317091 * 2
def baseEnd_317091 : Nat := 162820094214924113704231

theorem tailTrace_317091 : CollatzResearch.WordTrace tailWord_317091 prefixEnd_317091 162820094214924113704231 := by
  unfold tailWord_317091
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565258894240936676423127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7710172596160624450948751 11565258894240936676423127)
  ·
    refine ⟨17347888341361405014634691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11565258894240936676423127 17347888341361405014634691)
    ·
      refine ⟨26021832512042107521952037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17347888341361405014634691 26021832512042107521952037)
      ·
        refine ⟨4879093596007895160366007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26021832512042107521952037 4879093596007895160366007)
        ·
          refine ⟨7318640394011842740549011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879093596007895160366007 7318640394011842740549011)
          ·
            refine ⟨10977960591017764110823517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318640394011842740549011 10977960591017764110823517)
            ·
              refine ⟨4116735221631661541558819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977960591017764110823517 4116735221631661541558819)
              ·
                refine ⟨6175102832447492312338229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116735221631661541558819 6175102832447492312338229)
                ·
                  refine ⟨578915890541952404281709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6175102832447492312338229 578915890541952404281709)
                  ·
                    refine ⟨217093458953232151605641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 578915890541952404281709 217093458953232151605641)
                    ·
                      refine ⟨162820094214924113704231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217093458953232151605641 162820094214924113704231)
                      ·
                        rfl

theorem cell23_317091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_317091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317091 prefixEnd_317091 := by exact prefixLift 317091
  have htrace : WordTrace (prefixWord ++ tailWord_317091) baseStart_317091 baseEnd_317091 := by
    simpa [prefixWord, tailWord_317091, baseEnd_317091] using wordTrace_append hprefix tailTrace_317091
  have hstable : (prefixWord ++ tailWord_317091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317091).length < 2 ^ (prefixWord ++ tailWord_317091).sum := by decide
  have hdescent : baseEnd_317091 < baseStart_317091 := by decide
  rcases family_descends (prefixWord ++ tailWord_317091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317132 : List Nat := [2, 2, 1, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_317132 : Nat := 118140960795 + 317132 * 2 ^ 59
def prefixEnd_317132 : Nat := 4983230072969 + 3 ^ 40 * 317132 * 2
def baseEnd_317132 : Nat := 162841146921758453291543

theorem tailTrace_317132 : CollatzResearch.WordTrace tailWord_317132 prefixEnd_317132 162841146921758453291543 := by
  unfold tailWord_317132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783377143546200339332825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7711169524728267119110433 5783377143546200339332825)
  ·
    refine ⟨4337532857659650254499619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5783377143546200339332825 4337532857659650254499619)
    ·
      refine ⟨6506299286489475381749429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337532857659650254499619 6506299286489475381749429)
      ·
        refine ⟨609965558108388317039009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6506299286489475381749429 609965558108388317039009)
        ·
          refine ⟨457474168581291237779257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609965558108388317039009 457474168581291237779257)
          ·
            refine ⟨343105626435968428334443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457474168581291237779257 343105626435968428334443)
            ·
              refine ⟨514658439653952642501665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343105626435968428334443 514658439653952642501665)
              ·
                refine ⟨385993829740464481876249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514658439653952642501665 385993829740464481876249)
                ·
                  refine ⟨289495372305348361407187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385993829740464481876249 289495372305348361407187)
                  ·
                    refine ⟨434243058458022542110781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289495372305348361407187 434243058458022542110781)
                    ·
                      refine ⟨162841146921758453291543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434243058458022542110781 162841146921758453291543)
                      ·
                        rfl

theorem cell23_317132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_317132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317132 prefixEnd_317132 := by exact prefixLift 317132
  have htrace : WordTrace (prefixWord ++ tailWord_317132) baseStart_317132 baseEnd_317132 := by
    simpa [prefixWord, tailWord_317132, baseEnd_317132] using wordTrace_append hprefix tailTrace_317132
  have hstable : (prefixWord ++ tailWord_317132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317132).length < 2 ^ (prefixWord ++ tailWord_317132).sum := by decide
  have hdescent : baseEnd_317132 < baseStart_317132 := by decide
  rcases family_descends (prefixWord ++ tailWord_317132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317149 : List Nat := [1, 4, 3, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_317149 : Nat := 118140960795 + 317149 * 2 ^ 59
def prefixEnd_317149 : Nat := 4983230072969 + 3 ^ 40 * 317149 * 2
def baseEnd_317149 : Nat := 162849876092884886778965

theorem tailTrace_317149 : CollatzResearch.WordTrace tailWord_317149 prefixEnd_317149 162849876092884886778965 := by
  unfold tailWord_317149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567374328030812582034501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7711582885353875054689667 11567374328030812582034501)
  ·
    refine ⟨2168882686505777359131469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11567374328030812582034501 2168882686505777359131469)
    ·
      refine ⟨813331007439666509674301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2168882686505777359131469 813331007439666509674301)
      ·
        refine ⟨304999127789874941127863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 813331007439666509674301 304999127789874941127863)
        ·
          refine ⟨457498691684812411691795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304999127789874941127863 457498691684812411691795)
          ·
            refine ⟨686248037527218617537693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457498691684812411691795 686248037527218617537693)
            ·
              refine ⟨257343014072706981576635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 686248037527218617537693 257343014072706981576635)
              ·
                refine ⟨386014521109060472364953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257343014072706981576635 386014521109060472364953)
                ·
                  refine ⟨289510890831795354273715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386014521109060472364953 289510890831795354273715)
                  ·
                    refine ⟨434266336247693031410573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289510890831795354273715 434266336247693031410573)
                    ·
                      refine ⟨162849876092884886778965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434266336247693031410573 162849876092884886778965)
                      ·
                        rfl

theorem cell23_317149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_317149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317149 prefixEnd_317149 := by exact prefixLift 317149
  have htrace : WordTrace (prefixWord ++ tailWord_317149) baseStart_317149 baseEnd_317149 := by
    simpa [prefixWord, tailWord_317149, baseEnd_317149] using wordTrace_append hprefix tailTrace_317149
  have hstable : (prefixWord ++ tailWord_317149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317149).length < 2 ^ (prefixWord ++ tailWord_317149).sum := by decide
  have hdescent : baseEnd_317149 < baseStart_317149 := by decide
  rcases family_descends (prefixWord ++ tailWord_317149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317184 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_317184 : Nat := 118140960795 + 317184 * 2 ^ 59
def prefixEnd_317184 : Nat := 4983230072969 + 3 ^ 40 * 317184 * 2
def baseEnd_317184 : Nat := 162867847915792249841303

theorem tailTrace_317184 : CollatzResearch.WordTrace tailWord_317184 prefixEnd_317184 162867847915792249841303 := by
  unfold tailWord_317184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784325441452006779779303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7712433921936009039705737 5784325441452006779779303)
  ·
    refine ⟨8676488162178010169668955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784325441452006779779303 8676488162178010169668955)
    ·
      refine ⟨13014732243267015254503433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676488162178010169668955 13014732243267015254503433)
      ·
        refine ⟨9761049182450261440877575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13014732243267015254503433 9761049182450261440877575)
        ·
          refine ⟨14641573773675392161316363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9761049182450261440877575 14641573773675392161316363)
          ·
            refine ⟨21962360660513088241974545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14641573773675392161316363 21962360660513088241974545)
            ·
              refine ⟨16471770495384816181480909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21962360660513088241974545 16471770495384816181480909)
              ·
                refine ⟨6176913935769306068055341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16471770495384816181480909 6176913935769306068055341)
                ·
                  refine ⟨2316342725913489775520753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6176913935769306068055341 2316342725913489775520753)
                  ·
                    refine ⟨1737257044435117331640565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316342725913489775520753 1737257044435117331640565)
                    ·
                      refine ⟨162867847915792249841303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1737257044435117331640565 162867847915792249841303)
                      ·
                        rfl

theorem cell23_317184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_317184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317184 prefixEnd_317184 := by exact prefixLift 317184
  have htrace : WordTrace (prefixWord ++ tailWord_317184) baseStart_317184 baseEnd_317184 := by
    simpa [prefixWord, tailWord_317184, baseEnd_317184] using wordTrace_append hprefix tailTrace_317184
  have hstable : (prefixWord ++ tailWord_317184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317184).length < 2 ^ (prefixWord ++ tailWord_317184).sum := by decide
  have hdescent : baseEnd_317184 < baseStart_317184 := by decide
  rcases family_descends (prefixWord ++ tailWord_317184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317228 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_317228 : Nat := 118140960795 + 317228 * 2 ^ 59
def prefixEnd_317228 : Nat := 4983230072969 + 3 ^ 40 * 317228 * 2
def baseEnd_317228 : Nat := 162890441064590077691101

theorem tailTrace_317228 : CollatzResearch.WordTrace tailWord_317228 prefixEnd_317228 162890441064590077691101 := by
  unfold tailWord_317228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785127847372304537080169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7713503796496406049440225 5785127847372304537080169)
  ·
    refine ⟨4338845885529228402810127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5785127847372304537080169 4338845885529228402810127)
    ·
      refine ⟨6508268828293842604215191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4338845885529228402810127 6508268828293842604215191)
      ·
        refine ⟨9762403242440763906322787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508268828293842604215191 9762403242440763906322787)
        ·
          refine ⟨14643604863661145859484181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9762403242440763906322787 14643604863661145859484181)
          ·
            refine ⟨686418977984116212163321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14643604863661145859484181 686418977984116212163321)
            ·
              refine ⟨514814233488087159122491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686418977984116212163321 514814233488087159122491)
              ·
                refine ⟨772221350232130738683737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514814233488087159122491 772221350232130738683737)
                ·
                  refine ⟨579166012674098054012803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772221350232130738683737 579166012674098054012803)
                  ·
                    refine ⟨868749019011147081019205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579166012674098054012803 868749019011147081019205)
                    ·
                      refine ⟨162890441064590077691101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 868749019011147081019205 162890441064590077691101)
                      ·
                        rfl

theorem cell23_317228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_317228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317228 prefixEnd_317228 := by exact prefixLift 317228
  have htrace : WordTrace (prefixWord ++ tailWord_317228) baseStart_317228 baseEnd_317228 := by
    simpa [prefixWord, tailWord_317228, baseEnd_317228] using wordTrace_append hprefix tailTrace_317228
  have hstable : (prefixWord ++ tailWord_317228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317228).length < 2 ^ (prefixWord ++ tailWord_317228).sum := by decide
  have hdescent : baseEnd_317228 < baseStart_317228 := by decide
  rcases family_descends (prefixWord ++ tailWord_317228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317231 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_317231 : Nat := 118140960795 + 317231 * 2 ^ 59
def prefixEnd_317231 : Nat := 4983230072969 + 3 ^ 40 * 317231 * 2
def baseEnd_317231 : Nat := 162891981506553565953587

theorem tailTrace_317231 : CollatzResearch.WordTrace tailWord_317231 prefixEnd_317231 162891981506553565953587 := by
  unfold tailWord_317231
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570365113733740586519547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7713576742489160391013031 11570365113733740586519547)
  ·
    refine ⟨17355547670600610879779321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11570365113733740586519547 17355547670600610879779321)
    ·
      refine ⟨13016660752950458159834491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17355547670600610879779321 13016660752950458159834491)
      ·
        refine ⟨19524991129425687239751737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13016660752950458159834491 19524991129425687239751737)
        ·
          refine ⟨14643743347069265429813803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19524991129425687239751737 14643743347069265429813803)
          ·
            refine ⟨21965615020603898144720705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14643743347069265429813803 21965615020603898144720705)
            ·
              refine ⟨16474211265452923608540529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21965615020603898144720705 16474211265452923608540529)
              ·
                refine ⟨12355658449089692706405397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16474211265452923608540529 12355658449089692706405397)
                ·
                  refine ⟨579171489801079345612753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12355658449089692706405397 579171489801079345612753)
                  ·
                    refine ⟨434378617350809509209565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579171489801079345612753 434378617350809509209565)
                    ·
                      refine ⟨162891981506553565953587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434378617350809509209565 162891981506553565953587)
                      ·
                        rfl

theorem cell23_317231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_317231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317231 prefixEnd_317231 := by exact prefixLift 317231
  have htrace : WordTrace (prefixWord ++ tailWord_317231) baseStart_317231 baseEnd_317231 := by
    simpa [prefixWord, tailWord_317231, baseEnd_317231] using wordTrace_append hprefix tailTrace_317231
  have hstable : (prefixWord ++ tailWord_317231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317231).length < 2 ^ (prefixWord ++ tailWord_317231).sum := by decide
  have hdescent : baseEnd_317231 < baseStart_317231 := by decide
  rcases family_descends (prefixWord ++ tailWord_317231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317251 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 6]
def baseStart_317251 : Nat := 118140960795 + 317251 * 2 ^ 59
def prefixEnd_317251 : Nat := 4983230072969 + 3 ^ 40 * 317251 * 2
def baseEnd_317251 : Nat := 18100250124404831967055

theorem tailTrace_317251 : CollatzResearch.WordTrace tailWord_317251 prefixEnd_317251 18100250124404831967055 := by
  unfold tailWord_317251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571094573661284002247607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7714063049107522668165071 11571094573661284002247607)
  ·
    refine ⟨17356641860491926003371411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11571094573661284002247607 17356641860491926003371411)
    ·
      refine ⟨26034962790737889005057117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17356641860491926003371411 26034962790737889005057117)
      ·
        refine ⟨9763111046526708376896419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26034962790737889005057117 9763111046526708376896419)
        ·
          refine ⟨14644666569790062565344629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763111046526708376896419 14644666569790062565344629)
          ·
            refine ⟨1372937490917818365501059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14644666569790062565344629 1372937490917818365501059)
            ·
              refine ⟨2059406236376727548251589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372937490917818365501059 2059406236376727548251589)
              ·
                refine ⟨386138669320636415297173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2059406236376727548251589 386138669320636415297173)
                ·
                  refine ⟨18100250124404831967055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 386138669320636415297173 18100250124404831967055)
                  ·
                    rfl

theorem cell23_317251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 6].length) (baseStart_317251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317251 prefixEnd_317251 := by exact prefixLift 317251
  have htrace : WordTrace (prefixWord ++ tailWord_317251) baseStart_317251 baseEnd_317251 := by
    simpa [prefixWord, tailWord_317251, baseEnd_317251] using wordTrace_append hprefix tailTrace_317251
  have hstable : (prefixWord ++ tailWord_317251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317251).length < 2 ^ (prefixWord ++ tailWord_317251).sum := by decide
  have hdescent : baseEnd_317251 < baseStart_317251 := by decide
  rcases family_descends (prefixWord ++ tailWord_317251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317268 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 6]
def baseStart_317268 : Nat := 118140960795 + 317268 * 2 ^ 59
def prefixEnd_317268 : Nat := 4983230072969 + 3 ^ 40 * 317268 * 2
def baseEnd_317268 : Nat := 18101220032307769021213

theorem tailTrace_317268 : CollatzResearch.WordTrace tailWord_317268 prefixEnd_317268 18101220032307769021213 := by
  unfold tailWord_317268
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785857307299847952808229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7714476409733130603744305 5785857307299847952808229)
  ·
    refine ⟨1084848245118721491151543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5785857307299847952808229 1084848245118721491151543)
    ·
      refine ⟨1627272367678082236727315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084848245118721491151543 1627272367678082236727315)
      ·
        refine ⟨2440908551517123355090973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627272367678082236727315 2440908551517123355090973)
        ·
          refine ⟨915340706818921258159115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2440908551517123355090973 915340706818921258159115)
          ·
            refine ⟨1373011060228381887238673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915340706818921258159115 1373011060228381887238673)
            ·
              refine ⟨1029758295171286415429005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373011060228381887238673 1029758295171286415429005)
              ·
                refine ⟨386159360689232405785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1029758295171286415429005 386159360689232405785877)
                ·
                  refine ⟨18101220032307769021213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 386159360689232405785877 18101220032307769021213)
                  ·
                    rfl

theorem cell23_317268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_317268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317268 prefixEnd_317268 := by exact prefixLift 317268
  have htrace : WordTrace (prefixWord ++ tailWord_317268) baseStart_317268 baseEnd_317268 := by
    simpa [prefixWord, tailWord_317268, baseEnd_317268] using wordTrace_append hprefix tailTrace_317268
  have hstable : (prefixWord ++ tailWord_317268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317268).length < 2 ^ (prefixWord ++ tailWord_317268).sum := by decide
  have hdescent : baseEnd_317268 < baseStart_317268 := by decide
  rcases family_descends (prefixWord ++ tailWord_317268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317281 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_317281 : Nat := 118140960795 + 317281 * 2 ^ 59
def prefixEnd_317281 : Nat := 4983230072969 + 3 ^ 40 * 317281 * 2
def baseEnd_317281 : Nat := 54305885179759456776119

theorem tailTrace_317281 : CollatzResearch.WordTrace tailWord_317281 prefixEnd_317281 54305885179759456776119 := by
  unfold tailWord_317281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572188763552599125839697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7714792509035066083893131 11572188763552599125839697)
  ·
    refine ⟨8679141572664449344379773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11572188763552599125839697 8679141572664449344379773)
    ·
      refine ⟨3254678089749168504142415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8679141572664449344379773 3254678089749168504142415)
      ·
        refine ⟨4882017134623752756213623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254678089749168504142415 4882017134623752756213623)
        ·
          refine ⟨7323025701935629134320435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882017134623752756213623 7323025701935629134320435)
          ·
            refine ⟨10984538552903443701480653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323025701935629134320435 10984538552903443701480653)
            ·
              refine ⟨4119201957338791388055245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10984538552903443701480653 4119201957338791388055245)
              ·
                refine ⟨1544700734002046770520717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119201957338791388055245 1544700734002046770520717)
                ·
                  refine ⟨579262775250767538945269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1544700734002046770520717 579262775250767538945269)
                  ·
                    refine ⟨54305885179759456776119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 579262775250767538945269 54305885179759456776119)
                    ·
                      rfl

theorem cell23_317281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_317281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317281 prefixEnd_317281 := by exact prefixLift 317281
  have htrace : WordTrace (prefixWord ++ tailWord_317281) baseStart_317281 baseEnd_317281 := by
    simpa [prefixWord, tailWord_317281, baseEnd_317281] using wordTrace_append hprefix tailTrace_317281
  have hstable : (prefixWord ++ tailWord_317281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317281).length < 2 ^ (prefixWord ++ tailWord_317281).sum := by decide
  have hdescent : baseEnd_317281 < baseStart_317281 := by decide
  rcases family_descends (prefixWord ++ tailWord_317281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317282 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_317282 : Nat := 118140960795 + 317282 * 2 ^ 59
def prefixEnd_317282 : Nat := 4983230072969 + 3 ^ 40 * 317282 * 2
def baseEnd_317282 : Nat := 162918169019932866415853

theorem tailTrace_317282 : CollatzResearch.WordTrace tailWord_317282 prefixEnd_317282 162918169019932866415853 := by
  unfold tailWord_317282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893056309137244074156525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7714816824365984197750733 2893056309137244074156525)
  ·
    refine ⟨1084896115926466527808697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2893056309137244074156525 1084896115926466527808697)
    ·
      refine ⟨813672086944849895856523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1084896115926466527808697 813672086944849895856523)
      ·
        refine ⟨1220508130417274843784785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813672086944849895856523 1220508130417274843784785)
        ·
          refine ⟨915381097812956132838589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220508130417274843784785 915381097812956132838589)
          ·
            refine ⟨343267911679858549814471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915381097812956132838589 343267911679858549814471)
            ·
              refine ⟨514901867519787824721707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343267911679858549814471 514901867519787824721707)
              ·
                refine ⟨772352801279681737082561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514901867519787824721707 772352801279681737082561)
                ·
                  refine ⟨579264600959761302811921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772352801279681737082561 579264600959761302811921)
                  ·
                    refine ⟨434448450719820977108941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579264600959761302811921 434448450719820977108941)
                    ·
                      refine ⟨162918169019932866415853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434448450719820977108941 162918169019932866415853)
                      ·
                        rfl

theorem cell23_317282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_317282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317282 prefixEnd_317282 := by exact prefixLift 317282
  have htrace : WordTrace (prefixWord ++ tailWord_317282) baseStart_317282 baseEnd_317282 := by
    simpa [prefixWord, tailWord_317282, baseEnd_317282] using wordTrace_append hprefix tailTrace_317282
  have hstable : (prefixWord ++ tailWord_317282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317282).length < 2 ^ (prefixWord ++ tailWord_317282).sum := by decide
  have hdescent : baseEnd_317282 < baseStart_317282 := by decide
  rcases family_descends (prefixWord ++ tailWord_317282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317302 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_317302 : Nat := 118140960795 + 317302 * 2 ^ 59
def prefixEnd_317302 : Nat := 4983230072969 + 3 ^ 40 * 317302 * 2
def baseEnd_317302 : Nat := 18103159848113643129529

theorem tailTrace_317302 : CollatzResearch.WordTrace tailWord_317302 prefixEnd_317302 18103159848113643129529 := by
  unfold tailWord_317302
  simp only [CollatzResearch.WordTrace]
  refine ⟨723309668529782482022135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7715303130984346474902773 723309668529782482022135)
  ·
    refine ⟨1084964502794673723033203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723309668529782482022135 1084964502794673723033203)
    ·
      refine ⟨1627446754192010584549805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084964502794673723033203 1627446754192010584549805)
      ·
        refine ⟨610292532822003969206177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1627446754192010584549805 610292532822003969206177)
        ·
          refine ⟨457719399616502976904633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610292532822003969206177 457719399616502976904633)
          ·
            refine ⟨343289549712377232678475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457719399616502976904633 343289549712377232678475)
            ·
              refine ⟨514934324568565849017713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343289549712377232678475 514934324568565849017713)
              ·
                refine ⟨386200743426424386763285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514934324568565849017713 386200743426424386763285)
                ·
                  refine ⟨18103159848113643129529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 386200743426424386763285 18103159848113643129529)
                  ·
                    rfl

theorem cell23_317302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_317302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317302 prefixEnd_317302 := by exact prefixLift 317302
  have htrace : WordTrace (prefixWord ++ tailWord_317302) baseStart_317302 baseEnd_317302 := by
    simpa [prefixWord, tailWord_317302, baseEnd_317302] using wordTrace_append hprefix tailTrace_317302
  have hstable : (prefixWord ++ tailWord_317302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317302).length < 2 ^ (prefixWord ++ tailWord_317302).sum := by decide
  have hdescent : baseEnd_317302 < baseStart_317302 := by decide
  rcases family_descends (prefixWord ++ tailWord_317302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317335 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_317335 : Nat := 118140960795 + 317335 * 2 ^ 59
def prefixEnd_317335 : Nat := 4983230072969 + 3 ^ 40 * 317335 * 2
def baseEnd_317335 : Nat := 162945383494621159053109

theorem tailTrace_317335 : CollatzResearch.WordTrace tailWord_317335 prefixEnd_317335 162945383494621159053109 := by
  unfold tailWord_317335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574158305356966348305459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7716105536904644232203639 11574158305356966348305459)
  ·
    refine ⟨17361237458035449522458189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11574158305356966348305459 17361237458035449522458189)
    ·
      refine ⟨6510464046763293570921821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17361237458035449522458189 6510464046763293570921821)
      ·
        refine ⟨2441424017536235089095683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6510464046763293570921821 2441424017536235089095683)
        ·
          refine ⟨3662136026304352633643525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441424017536235089095683 3662136026304352633643525)
          ·
            refine ⟨686650504932066118808161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3662136026304352633643525 686650504932066118808161)
            ·
              refine ⟨514987878699049589106121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686650504932066118808161 514987878699049589106121)
              ·
                refine ⟨386240909024287191829591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514987878699049589106121 386240909024287191829591)
                ·
                  refine ⟨579361363536430787744387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386240909024287191829591 579361363536430787744387)
                  ·
                    refine ⟨869042045304646181616581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579361363536430787744387 869042045304646181616581)
                    ·
                      refine ⟨162945383494621159053109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 869042045304646181616581 162945383494621159053109)
                      ·
                        rfl

theorem cell23_317335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_317335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317335 prefixEnd_317335 := by exact prefixLift 317335
  have htrace : WordTrace (prefixWord ++ tailWord_317335) baseStart_317335 baseEnd_317335 := by
    simpa [prefixWord, tailWord_317335, baseEnd_317335] using wordTrace_append hprefix tailTrace_317335
  have hstable : (prefixWord ++ tailWord_317335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317335).length < 2 ^ (prefixWord ++ tailWord_317335).sum := by decide
  have hdescent : baseEnd_317335 < baseStart_317335 := by decide
  rcases family_descends (prefixWord ++ tailWord_317335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317346 : List Nat := [3, 3, 1, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_317346 : Nat := 118140960795 + 317346 * 2 ^ 59
def prefixEnd_317346 : Nat := 4983230072969 + 3 ^ 40 * 317346 * 2
def baseEnd_317346 : Nat := 162951031781820616015559

theorem tailTrace_317346 : CollatzResearch.WordTrace tailWord_317346 prefixEnd_317346 162951031781820616015559 := by
  unfold tailWord_317346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893639877079278806738973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7716373005544743484637261 2893639877079278806738973)
  ·
    refine ⟨1085114953904729552527115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2893639877079278806738973 1085114953904729552527115)
    ·
      refine ⟨1627672430857094328790673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085114953904729552527115 1627672430857094328790673)
      ·
        refine ⟨1220754323142820746593005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627672430857094328790673 1220754323142820746593005)
        ·
          refine ⟨457782871178557779972377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220754323142820746593005 457782871178557779972377)
          ·
            refine ⟨343337153383918334979283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457782871178557779972377 343337153383918334979283)
            ·
              refine ⟨515005730075877502468925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343337153383918334979283 515005730075877502468925)
              ·
                refine ⟨193127148778454063425847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515005730075877502468925 193127148778454063425847)
                ·
                  refine ⟨289690723167681095138771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193127148778454063425847 289690723167681095138771)
                  ·
                    refine ⟨434536084751521642708157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289690723167681095138771 434536084751521642708157)
                    ·
                      refine ⟨162951031781820616015559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434536084751521642708157 162951031781820616015559)
                      ·
                        rfl

theorem cell23_317346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_317346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317346 prefixEnd_317346 := by exact prefixLift 317346
  have htrace : WordTrace (prefixWord ++ tailWord_317346) baseStart_317346 baseEnd_317346 := by
    simpa [prefixWord, tailWord_317346, baseEnd_317346] using wordTrace_append hprefix tailTrace_317346
  have hstable : (prefixWord ++ tailWord_317346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317346).length < 2 ^ (prefixWord ++ tailWord_317346).sum := by decide
  have hdescent : baseEnd_317346 < baseStart_317346 := by decide
  rcases family_descends (prefixWord ++ tailWord_317346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317381 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_317381 : Nat := 118140960795 + 317381 * 2 ^ 59
def prefixEnd_317381 : Nat := 4983230072969 + 3 ^ 40 * 317381 * 2
def baseEnd_317381 : Nat := 162969003604727979077897

theorem tailTrace_317381 : CollatzResearch.WordTrace tailWord_317381 prefixEnd_317381 162969003604727979077897 := by
  unfold tailWord_317381
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575836063190316204479997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7717224042126877469653331 11575836063190316204479997)
  ·
    refine ⟨4340938523696368576679999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11575836063190316204479997 4340938523696368576679999)
    ·
      refine ⟨6511407785544552865019999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340938523696368576679999 6511407785544552865019999)
      ·
        refine ⟨9767111678316829297529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511407785544552865019999 9767111678316829297529999)
        ·
          refine ⟨14650667517475243946294999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767111678316829297529999 14650667517475243946294999)
          ·
            refine ⟨21976001276212865919442499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14650667517475243946294999 21976001276212865919442499)
            ·
              refine ⟨32964001914319298879163749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21976001276212865919442499 32964001914319298879163749)
              ·
                refine ⟨6180750358934868539843203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32964001914319298879163749 6180750358934868539843203)
                ·
                  refine ⟨9271125538402302809764805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180750358934868539843203 9271125538402302809764805)
                  ·
                    refine ⟨1738336038450431776830901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9271125538402302809764805 1738336038450431776830901)
                    ·
                      refine ⟨162969003604727979077897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1738336038450431776830901 162969003604727979077897)
                      ·
                        rfl

theorem cell23_317381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_317381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317381 prefixEnd_317381 := by exact prefixLift 317381
  have htrace : WordTrace (prefixWord ++ tailWord_317381) baseStart_317381 baseEnd_317381 := by
    simpa [prefixWord, tailWord_317381, baseEnd_317381] using wordTrace_append hprefix tailTrace_317381
  have hstable : (prefixWord ++ tailWord_317381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317381).length < 2 ^ (prefixWord ++ tailWord_317381).sum := by decide
  have hdescent : baseEnd_317381 < baseStart_317381 := by decide
  rcases family_descends (prefixWord ++ tailWord_317381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317385 : List Nat := [1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 3]
def baseStart_317385 : Nat := 118140960795 + 317385 * 2 ^ 59
def prefixEnd_317385 : Nat := 4983230072969 + 3 ^ 40 * 317385 * 2
def baseEnd_317385 : Nat := 162971057527345963427879

theorem tailTrace_317385 : CollatzResearch.WordTrace tailWord_317385 prefixEnd_317385 162971057527345963427879 := by
  unfold tailWord_317385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575981955175824887625609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7717321303450549925083739 11575981955175824887625609)
  ·
    refine ⟨8681986466381868665719207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11575981955175824887625609 8681986466381868665719207)
    ·
      refine ⟨13022979699572802998578811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8681986466381868665719207 13022979699572802998578811)
      ·
        refine ⟨19534469549359204497868217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022979699572802998578811 19534469549359204497868217)
        ·
          refine ⟨14650852162019403373401163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19534469549359204497868217 14650852162019403373401163)
          ·
            refine ⟨21976278243029105060101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14650852162019403373401163 21976278243029105060101745)
            ·
              refine ⟨16482208682271828795076309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21976278243029105060101745 16482208682271828795076309)
              ·
                refine ⟨386301765990745987384601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16482208682271828795076309 386301765990745987384601)
                ·
                  refine ⟨289726324493059490538451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386301765990745987384601 289726324493059490538451)
                  ·
                    refine ⟨434589486739589235807677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 289726324493059490538451 434589486739589235807677)
                    ·
                      refine ⟨162971057527345963427879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434589486739589235807677 162971057527345963427879)
                      ·
                        rfl

theorem cell23_317385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_317385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317385 prefixEnd_317385 := by exact prefixLift 317385
  have htrace : WordTrace (prefixWord ++ tailWord_317385) baseStart_317385 baseEnd_317385 := by
    simpa [prefixWord, tailWord_317385, baseEnd_317385] using wordTrace_append hprefix tailTrace_317385
  have hstable : (prefixWord ++ tailWord_317385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317385).length < 2 ^ (prefixWord ++ tailWord_317385).sum := by decide
  have hdescent : baseEnd_317385 < baseStart_317385 := by decide
  rcases family_descends (prefixWord ++ tailWord_317385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317418 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_317418 : Nat := 118140960795 + 317418 * 2 ^ 59
def prefixEnd_317418 : Nat := 4983230072969 + 3 ^ 40 * 317418 * 2
def baseEnd_317418 : Nat := 54329334129648111438409

theorem tailTrace_317418 : CollatzResearch.WordTrace tailWord_317418 prefixEnd_317418 54329334129648111438409 := by
  unfold tailWord_317418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894296391014067880894227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7718123709370847682384605 2894296391014067880894227)
  ·
    refine ⟨4341444586521101821341341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894296391014067880894227 4341444586521101821341341)
    ·
      refine ⟨1628041719945413183003003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4341444586521101821341341 1628041719945413183003003)
      ·
        refine ⟨2442062579918119774504505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628041719945413183003003 2442062579918119774504505)
        ·
          refine ⟨1831546934938589830878379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442062579918119774504505 1831546934938589830878379)
          ·
            refine ⟨2747320402407884746317569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831546934938589830878379 2747320402407884746317569)
            ·
              refine ⟨2060490301805913559738177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747320402407884746317569 2060490301805913559738177)
              ·
                refine ⟨1545367726354435169803633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060490301805913559738177 1545367726354435169803633)
                ·
                  refine ⟨1159025794765826377352725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545367726354435169803633 1159025794765826377352725)
                  ·
                    refine ⟨54329334129648111438409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1159025794765826377352725 54329334129648111438409)
                    ·
                      rfl

theorem cell23_317418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_317418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317418 prefixEnd_317418 := by exact prefixLift 317418
  have htrace : WordTrace (prefixWord ++ tailWord_317418) baseStart_317418 baseEnd_317418 := by
    simpa [prefixWord, tailWord_317418, baseEnd_317418] using wordTrace_append hprefix tailTrace_317418
  have hstable : (prefixWord ++ tailWord_317418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317418).length < 2 ^ (prefixWord ++ tailWord_317418).sum := by decide
  have hdescent : baseEnd_317418 < baseStart_317418 := by decide
  rcases family_descends (prefixWord ++ tailWord_317418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317431 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 13]
def baseStart_317431 : Nat := 118140960795 + 317431 * 2 ^ 59
def prefixEnd_317431 : Nat := 4983230072969 + 3 ^ 40 * 317431 * 2
def baseEnd_317431 : Nat := 18110519737494753716963

theorem tailTrace_317431 : CollatzResearch.WordTrace tailWord_317431 prefixEnd_317431 18110519737494753716963 := by
  unfold tailWord_317431
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577659713009174743800147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7718439808672783162533431 11577659713009174743800147)
  ·
    refine ⟨17366489569513762115700221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11577659713009174743800147 17366489569513762115700221)
    ·
      refine ⟨6512433588567660793387583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17366489569513762115700221 6512433588567660793387583)
      ·
        refine ⟨9768650382851491190081375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512433588567660793387583 9768650382851491190081375)
        ·
          refine ⟨14652975574277236785122063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9768650382851491190081375 14652975574277236785122063)
          ·
            refine ⟨21979463361415855177683095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14652975574277236785122063 21979463361415855177683095)
            ·
              refine ⟨32969195042123782766524643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21979463361415855177683095 32969195042123782766524643)
              ·
                refine ⟨49453792563185674149786965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32969195042123782766524643 49453792563185674149786965)
                ·
                  refine ⟨18110519737494753716963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 49453792563185674149786965 18110519737494753716963)
                  ·
                    rfl

theorem cell23_317431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 13].length) (baseStart_317431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317431 prefixEnd_317431 := by exact prefixLift 317431
  have htrace : WordTrace (prefixWord ++ tailWord_317431) baseStart_317431 baseEnd_317431 := by
    simpa [prefixWord, tailWord_317431, baseEnd_317431] using wordTrace_append hprefix tailTrace_317431
  have hstable : (prefixWord ++ tailWord_317431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317431).length < 2 ^ (prefixWord ++ tailWord_317431).sum := by decide
  have hdescent : baseEnd_317431 < baseStart_317431 := by decide
  rcases family_descends (prefixWord ++ tailWord_317431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317448 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 7]
def baseStart_317448 : Nat := 118140960795 + 317448 * 2 ^ 59
def prefixEnd_317448 : Nat := 4983230072969 + 3 ^ 40 * 317448 * 2
def baseEnd_317448 : Nat := 18111489645397690771121

theorem tailTrace_317448 : CollatzResearch.WordTrace tailWord_317448 prefixEnd_317448 18111489645397690771121 := by
  unfold tailWord_317448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789139876973793323584499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7718853169298391098112665 5789139876973793323584499)
  ·
    refine ⟨8683709815460689985376749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5789139876973793323584499 8683709815460689985376749)
    ·
      refine ⟨3256391180797758744516281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8683709815460689985376749 3256391180797758744516281)
      ·
        refine ⟨2442293385598319058387211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3256391180797758744516281 2442293385598319058387211)
        ·
          refine ⟨3663440078397478587580817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442293385598319058387211 3663440078397478587580817)
          ·
            refine ⟨2747580058798108940685613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663440078397478587580817 2747580058798108940685613)
            ·
              refine ⟨1030342522049290852757105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2747580058798108940685613 1030342522049290852757105)
              ·
                refine ⟨772756891536968139567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030342522049290852757105 772756891536968139567829)
                ·
                  refine ⟨18111489645397690771121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 772756891536968139567829 18111489645397690771121)
                  ·
                    rfl

theorem cell23_317448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_317448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317448 prefixEnd_317448 := by exact prefixLift 317448
  have htrace : WordTrace (prefixWord ++ tailWord_317448) baseStart_317448 baseEnd_317448 := by
    simpa [prefixWord, tailWord_317448, baseEnd_317448] using wordTrace_append hprefix tailTrace_317448
  have hstable : (prefixWord ++ tailWord_317448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317448).length < 2 ^ (prefixWord ++ tailWord_317448).sum := by decide
  have hdescent : baseEnd_317448 < baseStart_317448 := by decide
  rcases family_descends (prefixWord ++ tailWord_317448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317463 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_317463 : Nat := 118140960795 + 317463 * 2 ^ 59
def prefixEnd_317463 : Nat := 4983230072969 + 3 ^ 40 * 317463 * 2
def baseEnd_317463 : Nat := 163011109018396658252521

theorem tailTrace_317463 : CollatzResearch.WordTrace tailWord_317463 prefixEnd_317463 163011109018396658252521 := by
  unfold tailWord_317463
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578826848893244208965043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7719217899262162805976695 11578826848893244208965043)
  ·
    refine ⟨17368240273339866313447565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11578826848893244208965043 17368240273339866313447565)
    ·
      refine ⟨6513090102502449867542837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17368240273339866313447565 6513090102502449867542837)
      ·
        refine ⟨610602197109604675082141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6513090102502449867542837 610602197109604675082141)
        ·
          refine ⟨228975823916101753155803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610602197109604675082141 228975823916101753155803)
          ·
            refine ⟨343463735874152629733705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228975823916101753155803 343463735874152629733705)
            ·
              refine ⟨257597801905614472300279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343463735874152629733705 257597801905614472300279)
              ·
                refine ⟨386396702858421708450419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257597801905614472300279 386396702858421708450419)
                ·
                  refine ⟨579595054287632562675629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386396702858421708450419 579595054287632562675629)
                  ·
                    refine ⟨217348145357862211003361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 579595054287632562675629 217348145357862211003361)
                    ·
                      refine ⟨163011109018396658252521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217348145357862211003361 163011109018396658252521)
                      ·
                        rfl

theorem cell23_317463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_317463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317463 prefixEnd_317463 := by exact prefixLift 317463
  have htrace : WordTrace (prefixWord ++ tailWord_317463) baseStart_317463 baseEnd_317463 := by
    simpa [prefixWord, tailWord_317463, baseEnd_317463] using wordTrace_append hprefix tailTrace_317463
  have hstable : (prefixWord ++ tailWord_317463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317463).length < 2 ^ (prefixWord ++ tailWord_317463).sum := by decide
  have hdescent : baseEnd_317463 < baseStart_317463 := by decide
  rcases family_descends (prefixWord ++ tailWord_317463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317482 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_317482 : Nat := 118140960795 + 317482 * 2 ^ 59
def prefixEnd_317482 : Nat := 4983230072969 + 3 ^ 40 * 317482 * 2
def baseEnd_317482 : Nat := 18113429461203564879437

theorem tailTrace_317482 : CollatzResearch.WordTrace tailWord_317482 prefixEnd_317482 18113429461203564879437 := by
  unfold tailWord_317482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894879958956102613476675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7719679890549606969271133 2894879958956102613476675)
  ·
    refine ⟨4342319938434153920215013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894879958956102613476675 4342319938434153920215013)
    ·
      refine ⟨814184988456403860040315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4342319938434153920215013 814184988456403860040315)
      ·
        refine ⟨1221277482684605790060473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814184988456403860040315 1221277482684605790060473)
        ·
          refine ⟨915958112013454342545355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221277482684605790060473 915958112013454342545355)
          ·
            refine ⟨1373937168020181513818033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915958112013454342545355 1373937168020181513818033)
            ·
              refine ⟨1030452876015136135363525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373937168020181513818033 1030452876015136135363525)
              ·
                refine ⟨193209914252838025380661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1030452876015136135363525 193209914252838025380661)
                ·
                  refine ⟨18113429461203564879437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193209914252838025380661 18113429461203564879437)
                  ·
                    rfl

theorem cell23_317482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_317482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317482 prefixEnd_317482 := by exact prefixLift 317482
  have htrace : WordTrace (prefixWord ++ tailWord_317482) baseStart_317482 baseEnd_317482 := by
    simpa [prefixWord, tailWord_317482, baseEnd_317482] using wordTrace_append hprefix tailTrace_317482
  have hstable : (prefixWord ++ tailWord_317482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317482).length < 2 ^ (prefixWord ++ tailWord_317482).sum := by decide
  have hdescent : baseEnd_317482 < baseStart_317482 := by decide
  rcases family_descends (prefixWord ++ tailWord_317482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317532 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_317532 : Nat := 118140960795 + 317532 * 2 ^ 59
def prefixEnd_317532 : Nat := 4983230072969 + 3 ^ 40 * 317532 * 2
def baseEnd_317532 : Nat := 163046539183556888289703

theorem tailTrace_317532 : CollatzResearch.WordTrace tailWord_317532 prefixEnd_317532 163046539183556888289703 := by
  unfold tailWord_317532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790671742821634496613425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7720895657095512662151233 5790671742821634496613425)
  ·
    refine ⟨4343003807116225872460069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5790671742821634496613425 4343003807116225872460069)
    ·
      refine ⟨814313213834292351086263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4343003807116225872460069 814313213834292351086263)
      ·
        refine ⟨1221469820751438526629395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814313213834292351086263 1221469820751438526629395)
        ·
          refine ⟨1832204731127157789944093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221469820751438526629395 1832204731127157789944093)
          ·
            refine ⟨687076774172684171229035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1832204731127157789944093 687076774172684171229035)
            ·
              refine ⟨1030615161259026256843553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687076774172684171229035 1030615161259026256843553)
              ·
                refine ⟨772961370944269692632665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030615161259026256843553 772961370944269692632665)
                ·
                  refine ⟨579721028208202269474499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772961370944269692632665 579721028208202269474499)
                  ·
                    refine ⟨869581542312303404211749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579721028208202269474499 869581542312303404211749)
                    ·
                      refine ⟨163046539183556888289703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 869581542312303404211749 163046539183556888289703)
                      ·
                        rfl

theorem cell23_317532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_317532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317532 prefixEnd_317532 := by exact prefixLift 317532
  have htrace : WordTrace (prefixWord ++ tailWord_317532) baseStart_317532 baseEnd_317532 := by
    simpa [prefixWord, tailWord_317532, baseEnd_317532] using wordTrace_append hprefix tailTrace_317532
  have hstable : (prefixWord ++ tailWord_317532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317532).length < 2 ^ (prefixWord ++ tailWord_317532).sum := by decide
  have hdescent : baseEnd_317532 < baseStart_317532 := by decide
  rcases family_descends (prefixWord ++ tailWord_317532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317569 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_317569 : Nat := 118140960795 + 317569 * 2 ^ 59
def prefixEnd_317569 : Nat := 4983230072969 + 3 ^ 40 * 317569 * 2
def baseEnd_317569 : Nat := 163065537967773243527033

theorem tailTrace_317569 : CollatzResearch.WordTrace tailWord_317569 prefixEnd_317569 163065537967773243527033 := by
  unfold tailWord_317569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582692986509224312323761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7721795324339482874882507 11582692986509224312323761)
  ·
    refine ⟨8687019739881918234242821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11582692986509224312323761 8687019739881918234242821)
    ·
      refine ⟨1628816201227859668920529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8687019739881918234242821 1628816201227859668920529)
      ·
        refine ⟨1221612150920894751690397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1628816201227859668920529 1221612150920894751690397)
        ·
          refine ⟨458104556595335531883899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1221612150920894751690397 458104556595335531883899)
          ·
            refine ⟨687156834893003297825849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458104556595335531883899 687156834893003297825849)
            ·
              refine ⟨515367626169752473369387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687156834893003297825849 515367626169752473369387)
              ·
                refine ⟨773051439254628710054081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515367626169752473369387 773051439254628710054081)
                ·
                  refine ⟨579788579440971532540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773051439254628710054081 579788579440971532540561)
                  ·
                    refine ⟨434841434580728649405421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579788579440971532540561 434841434580728649405421)
                    ·
                      refine ⟨163065537967773243527033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434841434580728649405421 163065537967773243527033)
                      ·
                        rfl

theorem cell23_317569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_317569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317569 prefixEnd_317569 := by exact prefixLift 317569
  have htrace : WordTrace (prefixWord ++ tailWord_317569) baseStart_317569 baseEnd_317569 := by
    simpa [prefixWord, tailWord_317569, baseEnd_317569] using wordTrace_append hprefix tailTrace_317569
  have hstable : (prefixWord ++ tailWord_317569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317569).length < 2 ^ (prefixWord ++ tailWord_317569).sum := by decide
  have hdescent : baseEnd_317569 < baseStart_317569 := by decide
  rcases family_descends (prefixWord ++ tailWord_317569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317602 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_317602 : Nat := 118140960795 + 317602 * 2 ^ 59
def prefixEnd_317602 : Nat := 4983230072969 + 3 ^ 40 * 317602 * 2
def baseEnd_317602 : Nat := 54360827609790538138127

theorem tailTrace_317602 : CollatzResearch.WordTrace tailWord_317602 prefixEnd_317602 54360827609790538138127 := by
  unfold tailWord_317602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895974148847417737068765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7722597730259780632183373 2895974148847417737068765)
  ·
    refine ⟨1085990305817781651400787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2895974148847417737068765 1085990305817781651400787)
    ·
      refine ⟨1628985458726672477101181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085990305817781651400787 1628985458726672477101181)
      ·
        refine ⟨610869547022502178912943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1628985458726672477101181 610869547022502178912943)
        ·
          refine ⟨916304320533753268369415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610869547022502178912943 916304320533753268369415)
          ·
            refine ⟨1374456480800629902554123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916304320533753268369415 1374456480800629902554123)
            ·
              refine ⟨2061684721200944853831185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374456480800629902554123 2061684721200944853831185)
              ·
                refine ⟨1546263540900708640373389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061684721200944853831185 1546263540900708640373389)
                ·
                  refine ⟨579848827837765740140021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1546263540900708640373389 579848827837765740140021)
                  ·
                    refine ⟨54360827609790538138127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 579848827837765740140021 54360827609790538138127)
                    ·
                      rfl

theorem cell23_317602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_317602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317602 prefixEnd_317602 := by exact prefixLift 317602
  have htrace : WordTrace (prefixWord ++ tailWord_317602) baseStart_317602 baseEnd_317602 := by
    simpa [prefixWord, tailWord_317602, baseEnd_317602] using wordTrace_append hprefix tailTrace_317602
  have hstable : (prefixWord ++ tailWord_317602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317602).length < 2 ^ (prefixWord ++ tailWord_317602).sum := by decide
  have hdescent : baseEnd_317602 < baseStart_317602 := by decide
  rcases family_descends (prefixWord ++ tailWord_317602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317605 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_317605 : Nat := 118140960795 + 317605 * 2 ^ 59
def prefixEnd_317605 : Nat := 4983230072969 + 3 ^ 40 * 317605 * 2
def baseEnd_317605 : Nat := 163084023271335102676867

theorem tailTrace_317605 : CollatzResearch.WordTrace tailWord_317605 prefixEnd_317605 163084023271335102676867 := by
  unfold tailWord_317605
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584006014378802460634269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7722670676252534973756179 11584006014378802460634269)
  ·
    refine ⟨4344002255392050922737851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11584006014378802460634269 4344002255392050922737851)
    ·
      refine ⟨6516003383088076384106777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344002255392050922737851 6516003383088076384106777)
      ·
        refine ⟨4887002537316057288080083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6516003383088076384106777 4887002537316057288080083)
        ·
          refine ⟨7330503805974085932120125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887002537316057288080083 7330503805974085932120125)
          ·
            refine ⟨2748938927240282224545047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7330503805974085932120125 2748938927240282224545047)
            ·
              refine ⟨4123408390860423336817571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748938927240282224545047 4123408390860423336817571)
              ·
                refine ⟨6185112586290635005226357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123408390860423336817571 6185112586290635005226357)
                ·
                  refine ⟨579854304964747031739971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6185112586290635005226357 579854304964747031739971)
                  ·
                    refine ⟨869781457447120547609957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579854304964747031739971 869781457447120547609957)
                    ·
                      refine ⟨163084023271335102676867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 869781457447120547609957 163084023271335102676867)
                      ·
                        rfl

theorem cell23_317605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_317605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317605 prefixEnd_317605 := by exact prefixLift 317605
  have htrace : WordTrace (prefixWord ++ tailWord_317605) baseStart_317605 baseEnd_317605 := by
    simpa [prefixWord, tailWord_317605, baseEnd_317605] using wordTrace_append hprefix tailTrace_317605
  have hstable : (prefixWord ++ tailWord_317605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317605).length < 2 ^ (prefixWord ++ tailWord_317605).sum := by decide
  have hdescent : baseEnd_317605 < baseStart_317605 := by decide
  rcases family_descends (prefixWord ++ tailWord_317605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317615 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 6, 4]
def baseStart_317615 : Nat := 118140960795 + 317615 * 2 ^ 59
def prefixEnd_317615 : Nat := 4983230072969 + 3 ^ 40 * 317615 * 2
def baseEnd_317615 : Nat := 54363052692626687850607

theorem tailTrace_317615 : CollatzResearch.WordTrace tailWord_317615 prefixEnd_317615 54363052692626687850607 := by
  unfold tailWord_317615
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584370744342574168498299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7722913829561716112332199 11584370744342574168498299)
  ·
    refine ⟨17376556116513861252747449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11584370744342574168498299 17376556116513861252747449)
    ·
      refine ⟨13032417087385395939560587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17376556116513861252747449 13032417087385395939560587)
      ·
        refine ⟨19548625631078093909340881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13032417087385395939560587 19548625631078093909340881)
        ·
          refine ⟨14661469223308570432005661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19548625631078093909340881 14661469223308570432005661)
          ·
            refine ⟨5498050958740713912002123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14661469223308570432005661 5498050958740713912002123)
            ·
              refine ⟨8247076438111070868003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498050958740713912002123 8247076438111070868003185)
              ·
                refine ⟨6185307328583303151002389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8247076438111070868003185 6185307328583303151002389)
                ·
                  refine ⟨289936281027342335203237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6185307328583303151002389 289936281027342335203237)
                  ·
                    refine ⟨54363052692626687850607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 289936281027342335203237 54363052692626687850607)
                    ·
                      rfl

theorem cell23_317615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_317615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317615 prefixEnd_317615 := by exact prefixLift 317615
  have htrace : WordTrace (prefixWord ++ tailWord_317615) baseStart_317615 baseEnd_317615 := by
    simpa [prefixWord, tailWord_317615, baseEnd_317615] using wordTrace_append hprefix tailTrace_317615
  have hstable : (prefixWord ++ tailWord_317615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317615).length < 2 ^ (prefixWord ++ tailWord_317615).sum := by decide
  have hdescent : baseEnd_317615 < baseStart_317615 := by decide
  rcases family_descends (prefixWord ++ tailWord_317615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317620 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_317620 : Nat := 118140960795 + 317620 * 2 ^ 59
def prefixEnd_317620 : Nat := 4983230072969 + 3 ^ 40 * 317620 * 2
def baseEnd_317620 : Nat := 163091725481152543989299

theorem tailTrace_317620 : CollatzResearch.WordTrace tailWord_317620 prefixEnd_317620 163091725481152543989299 := by
  unfold tailWord_317620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792276554662230011215157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7723035406216306681620209 5792276554662230011215157)
  ·
    refine ⟨543025926999584063551421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5792276554662230011215157 543025926999584063551421)
    ·
      refine ⟨203634722624844023831783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 543025926999584063551421 203634722624844023831783)
      ·
        refine ⟨305452083937266035747675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203634722624844023831783 305452083937266035747675)
        ·
          refine ⟨458178125905899053621513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305452083937266035747675 458178125905899053621513)
          ·
            refine ⟨343633594429424290216135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458178125905899053621513 343633594429424290216135)
            ·
              refine ⟨515450391644136435324203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343633594429424290216135 515450391644136435324203)
              ·
                refine ⟨773175587466204652986305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515450391644136435324203 773175587466204652986305)
                ·
                  refine ⟨579881690599653489739729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773175587466204652986305 579881690599653489739729)
                  ·
                    refine ⟨434911267949740117304797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579881690599653489739729 434911267949740117304797)
                    ·
                      refine ⟨163091725481152543989299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 434911267949740117304797 163091725481152543989299)
                      ·
                        rfl

theorem cell23_317620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_317620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317620 prefixEnd_317620 := by exact prefixLift 317620
  have htrace : WordTrace (prefixWord ++ tailWord_317620) baseStart_317620 baseEnd_317620 := by
    simpa [prefixWord, tailWord_317620, baseEnd_317620] using wordTrace_append hprefix tailTrace_317620
  have hstable : (prefixWord ++ tailWord_317620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317620).length < 2 ^ (prefixWord ++ tailWord_317620).sum := by decide
  have hdescent : baseEnd_317620 < baseStart_317620 := by decide
  rcases family_descends (prefixWord ++ tailWord_317620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317636 : List Nat := [2, 3, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_317636 : Nat := 118140960795 + 317636 * 2 ^ 59
def prefixEnd_317636 : Nat := 4983230072969 + 3 ^ 40 * 317636 * 2
def baseEnd_317636 : Nat := 54366647057208160463075

theorem tailTrace_317636 : CollatzResearch.WordTrace tailWord_317636 prefixEnd_317636 54366647057208160463075 := by
  unfold tailWord_317636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792568338633247377506381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7723424451510996503341841 5792568338633247377506381)
  ·
    refine ⟨2172213126987467766564893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5792568338633247377506381 2172213126987467766564893)
    ·
      refine ⟨814579922620300412461835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2172213126987467766564893 814579922620300412461835)
      ·
        refine ⟨1221869883930450618692753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814579922620300412461835 1221869883930450618692753)
        ·
          refine ⟨916402412947837964019565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221869883930450618692753 916402412947837964019565)
          ·
            refine ⟨343650904855439236507337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 916402412947837964019565 343650904855439236507337)
            ·
              refine ⟨257738178641579427380503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343650904855439236507337 257738178641579427380503)
              ·
                refine ⟨386607267962369141070755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257738178641579427380503 386607267962369141070755)
                ·
                  refine ⟨579910901943553711606133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386607267962369141070755 579910901943553711606133)
                  ·
                    refine ⟨54366647057208160463075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 579910901943553711606133 54366647057208160463075)
                    ·
                      rfl

theorem cell23_317636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_317636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317636 prefixEnd_317636 := by exact prefixLift 317636
  have htrace : WordTrace (prefixWord ++ tailWord_317636) baseStart_317636 baseEnd_317636 := by
    simpa [prefixWord, tailWord_317636, baseEnd_317636] using wordTrace_append hprefix tailTrace_317636
  have hstable : (prefixWord ++ tailWord_317636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317636).length < 2 ^ (prefixWord ++ tailWord_317636).sum := by decide
  have hdescent : baseEnd_317636 < baseStart_317636 := by decide
  rcases family_descends (prefixWord ++ tailWord_317636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317656 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_317656 : Nat := 118140960795 + 317656 * 2 ^ 59
def prefixEnd_317656 : Nat := 4983230072969 + 3 ^ 40 * 317656 * 2
def baseEnd_317656 : Nat := 163110210784714403139133

theorem tailTrace_317656 : CollatzResearch.WordTrace tailWord_317656 prefixEnd_317656 163110210784714403139133 := by
  unfold tailWord_317656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792933068597019085370411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7723910758129358780493881 5792933068597019085370411)
  ·
    refine ⟨8689399602895528628055617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792933068597019085370411 8689399602895528628055617)
    ·
      refine ⟨6517049702171646471041713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8689399602895528628055617 6517049702171646471041713)
      ·
        refine ⟨4887787276628734853281285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6517049702171646471041713 4887787276628734853281285)
        ·
          refine ⟨916460114367887784990241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4887787276628734853281285 916460114367887784990241)
          ·
            refine ⟨687345085775915838742681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916460114367887784990241 687345085775915838742681)
            ·
              refine ⟨515508814331936879057011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687345085775915838742681 515508814331936879057011)
              ·
                refine ⟨773263221497905318585517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515508814331936879057011 773263221497905318585517)
                ·
                  refine ⟨289973708061714494469569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 773263221497905318585517 289973708061714494469569)
                  ·
                    refine ⟨217480281046285870852177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 289973708061714494469569 217480281046285870852177)
                    ·
                      refine ⟨163110210784714403139133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217480281046285870852177 163110210784714403139133)
                      ·
                        rfl

theorem cell23_317656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_317656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317656 prefixEnd_317656 := by exact prefixLift 317656
  have htrace : WordTrace (prefixWord ++ tailWord_317656) baseStart_317656 baseEnd_317656 := by
    simpa [prefixWord, tailWord_317656, baseEnd_317656] using wordTrace_append hprefix tailTrace_317656
  have hstable : (prefixWord ++ tailWord_317656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317656).length < 2 ^ (prefixWord ++ tailWord_317656).sum := by decide
  have hdescent : baseEnd_317656 < baseStart_317656 := by decide
  rcases family_descends (prefixWord ++ tailWord_317656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317669 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_317669 : Nat := 118140960795 + 317669 * 2 ^ 59
def prefixEnd_317669 : Nat := 4983230072969 + 3 ^ 40 * 317669 * 2
def baseEnd_317669 : Nat := 163116886033222852276573

theorem tailTrace_317669 : CollatzResearch.WordTrace tailWord_317669 prefixEnd_317669 163116886033222852276573 := by
  unfold tailWord_317669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586340286146941390964061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7724226857431294260642707 11586340286146941390964061)
  ·
    refine ⟨4344877607305103021611523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11586340286146941390964061 4344877607305103021611523)
    ·
      refine ⟨6517316410957654532417285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4344877607305103021611523 6517316410957654532417285)
      ·
        refine ⟨1221996827054560224828241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6517316410957654532417285 1221996827054560224828241)
        ·
          refine ⟨916497620290920168621181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221996827054560224828241 916497620290920168621181)
          ·
            refine ⟨343686607609095063232943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 916497620290920168621181 343686607609095063232943)
            ·
              refine ⟨515529911413642594849415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343686607609095063232943 515529911413642594849415)
              ·
                refine ⟨773294867120463892274123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515529911413642594849415 773294867120463892274123)
                ·
                  refine ⟨1159942300680695838411185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773294867120463892274123 1159942300680695838411185)
                  ·
                    refine ⟨869956725510521878808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159942300680695838411185 869956725510521878808389)
                    ·
                      refine ⟨163116886033222852276573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 869956725510521878808389 163116886033222852276573)
                      ·
                        rfl

theorem cell23_317669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_317669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317669 prefixEnd_317669 := by exact prefixLift 317669
  have htrace : WordTrace (prefixWord ++ tailWord_317669) baseStart_317669 baseEnd_317669 := by
    simpa [prefixWord, tailWord_317669, baseEnd_317669] using wordTrace_append hprefix tailTrace_317669
  have hstable : (prefixWord ++ tailWord_317669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317669).length < 2 ^ (prefixWord ++ tailWord_317669).sum := by decide
  have hdescent : baseEnd_317669 < baseStart_317669 := by decide
  rcases family_descends (prefixWord ++ tailWord_317669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317699 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 1, 3, 2]
def baseStart_317699 : Nat := 118140960795 + 317699 * 2 ^ 59
def prefixEnd_317699 : Nat := 4983230072969 + 3 ^ 40 * 317699 * 2
def baseEnd_317699 : Nat := 163132290452857734901435

theorem tailTrace_317699 : CollatzResearch.WordTrace tailWord_317699 prefixEnd_317699 163132290452857734901435 := by
  unfold tailWord_317699
  simp only [CollatzResearch.WordTrace]
  refine ⟨11587434476038256514556151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7724956317358837676370767 11587434476038256514556151)
  ·
    refine ⟨17381151714057384771834227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11587434476038256514556151 17381151714057384771834227)
    ·
      refine ⟨26071727571086077157751341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17381151714057384771834227 26071727571086077157751341)
      ·
        refine ⟨9776897839157278934156753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26071727571086077157751341 9776897839157278934156753)
        ·
          refine ⟨7332673379367959200617565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9776897839157278934156753 7332673379367959200617565)
          ·
            refine ⟨2749752517262984700231587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7332673379367959200617565 2749752517262984700231587)
            ·
              refine ⟨4124628775894477050347381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749752517262984700231587 4124628775894477050347381)
              ·
                refine ⟨386683947740107223470067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4124628775894477050347381 386683947740107223470067)
                ·
                  refine ⟨580025921610160835205101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386683947740107223470067 580025921610160835205101)
                  ·
                    refine ⟨217509720603810313201913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580025921610160835205101 217509720603810313201913)
                    ·
                      refine ⟨163132290452857734901435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217509720603810313201913 163132290452857734901435)
                      ·
                        rfl

theorem cell23_317699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_317699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317699 prefixEnd_317699 := by exact prefixLift 317699
  have htrace : WordTrace (prefixWord ++ tailWord_317699) baseStart_317699 baseEnd_317699 := by
    simpa [prefixWord, tailWord_317699, baseEnd_317699] using wordTrace_append hprefix tailTrace_317699
  have hstable : (prefixWord ++ tailWord_317699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317699).length < 2 ^ (prefixWord ++ tailWord_317699).sum := by decide
  have hdescent : baseEnd_317699 < baseStart_317699 := by decide
  rcases family_descends (prefixWord ++ tailWord_317699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317732 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_317732 : Nat := 118140960795 + 317732 * 2 ^ 59
def prefixEnd_317732 : Nat := 4983230072969 + 3 ^ 40 * 317732 * 2
def baseEnd_317732 : Nat := 163149235314456105788783

theorem tailTrace_317732 : CollatzResearch.WordTrace tailWord_317732 prefixEnd_317732 163149235314456105788783 := by
  unfold tailWord_317732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794319042459351575253725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7725758723279135433671633 5794319042459351575253725)
  ·
    refine ⟨2172869640922256840720147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5794319042459351575253725 2172869640922256840720147)
    ·
      refine ⟨3259304461383385261080221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172869640922256840720147 3259304461383385261080221)
      ·
        refine ⟨1222239173018769472905083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3259304461383385261080221 1222239173018769472905083)
        ·
          refine ⟨1833358759528154209357625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222239173018769472905083 1833358759528154209357625)
          ·
            refine ⟨1375019069646115657018219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833358759528154209357625 1375019069646115657018219)
            ·
              refine ⟨2062528604469173485527329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375019069646115657018219 2062528604469173485527329)
              ·
                refine ⟨1546896453351880114145497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062528604469173485527329 1546896453351880114145497)
                ·
                  refine ⟨1160172340013910085609123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546896453351880114145497 1160172340013910085609123)
                  ·
                    refine ⟨1740258510020865128413685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160172340013910085609123 1740258510020865128413685)
                    ·
                      refine ⟨163149235314456105788783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1740258510020865128413685 163149235314456105788783)
                      ·
                        rfl

theorem cell23_317732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_317732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317732 prefixEnd_317732 := by exact prefixLift 317732
  have htrace : WordTrace (prefixWord ++ tailWord_317732) baseStart_317732 baseEnd_317732 := by
    simpa [prefixWord, tailWord_317732, baseEnd_317732] using wordTrace_append hprefix tailTrace_317732
  have hstable : (prefixWord ++ tailWord_317732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317732).length < 2 ^ (prefixWord ++ tailWord_317732).sum := by decide
  have hdescent : baseEnd_317732 < baseStart_317732 := by decide
  rcases family_descends (prefixWord ++ tailWord_317732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317733 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_317733 : Nat := 118140960795 + 317733 * 2 ^ 59
def prefixEnd_317733 : Nat := 4983230072969 + 3 ^ 40 * 317733 * 2
def baseEnd_317733 : Nat := 163149748795110601876279

theorem tailTrace_317733 : CollatzResearch.WordTrace tailWord_317733 prefixEnd_317733 163149748795110601876279 := by
  unfold tailWord_317733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588674557915080321293853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7725783038610053547529235 11588674557915080321293853)
  ·
    refine ⟨4345752959218155120485195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11588674557915080321293853 4345752959218155120485195)
    ·
      refine ⟨6518629438827232680727793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345752959218155120485195 6518629438827232680727793)
      ·
        refine ⟨4888972079120424510545845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6518629438827232680727793 4888972079120424510545845)
        ·
          refine ⟨458341132417539797863673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4888972079120424510545845 458341132417539797863673)
          ·
            refine ⟨343755849313154848397755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458341132417539797863673 343755849313154848397755)
            ·
              refine ⟨515633773969732272596633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343755849313154848397755 515633773969732272596633)
              ·
                refine ⟨386725330477299204447475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515633773969732272596633 386725330477299204447475)
                ·
                  refine ⟨580087995715948806671213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386725330477299204447475 580087995715948806671213)
                  ·
                    refine ⟨217532998393480802501705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 580087995715948806671213 217532998393480802501705)
                    ·
                      refine ⟨163149748795110601876279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217532998393480802501705 163149748795110601876279)
                      ·
                        rfl

theorem cell23_317733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_317733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317733 prefixEnd_317733 := by exact prefixLift 317733
  have htrace : WordTrace (prefixWord ++ tailWord_317733) baseStart_317733 baseEnd_317733 := by
    simpa [prefixWord, tailWord_317733, baseEnd_317733] using wordTrace_append hprefix tailTrace_317733
  have hstable : (prefixWord ++ tailWord_317733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317733).length < 2 ^ (prefixWord ++ tailWord_317733).sum := by decide
  have hdescent : baseEnd_317733 < baseStart_317733 := by decide
  rcases family_descends (prefixWord ++ tailWord_317733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317746 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_317746 : Nat := 118140960795 + 317746 * 2 ^ 59
def prefixEnd_317746 : Nat := 4983230072969 + 3 ^ 40 * 317746 * 2
def baseEnd_317746 : Nat := 163156424043619051013719

theorem tailTrace_317746 : CollatzResearch.WordTrace tailWord_317746 prefixEnd_317746 163156424043619051013719 := by
  unfold tailWord_317746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897287176716995885379273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7726099137911989027678061 2897287176716995885379273)
  ·
    refine ⟨2172965382537746914034455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897287176716995885379273 2172965382537746914034455)
    ·
      refine ⟨3259448073806620371051683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172965382537746914034455 3259448073806620371051683)
      ·
        refine ⟨4889172110709930556577525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259448073806620371051683 4889172110709930556577525)
        ·
          refine ⟨458359885379055989679143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4889172110709930556577525 458359885379055989679143)
          ·
            refine ⟨687539828068583984518715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458359885379055989679143 687539828068583984518715)
            ·
              refine ⟨1031309742102875976778073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687539828068583984518715 1031309742102875976778073)
              ·
                refine ⟨773482306577156982583555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031309742102875976778073 773482306577156982583555)
                ·
                  refine ⟨1160223459865735473875333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773482306577156982583555 1160223459865735473875333)
                  ·
                    refine ⟨217541898724825401351625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160223459865735473875333 217541898724825401351625)
                    ·
                      refine ⟨163156424043619051013719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217541898724825401351625 163156424043619051013719)
                      ·
                        rfl

theorem cell23_317746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_317746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317746 prefixEnd_317746 := by exact prefixLift 317746
  have htrace : WordTrace (prefixWord ++ tailWord_317746) baseStart_317746 baseEnd_317746 := by
    simpa [prefixWord, tailWord_317746, baseEnd_317746] using wordTrace_append hprefix tailTrace_317746
  have hstable : (prefixWord ++ tailWord_317746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317746).length < 2 ^ (prefixWord ++ tailWord_317746).sum := by decide
  have hdescent : baseEnd_317746 < baseStart_317746 := by decide
  rcases family_descends (prefixWord ++ tailWord_317746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317765 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_317765 : Nat := 118140960795 + 317765 * 2 ^ 59
def prefixEnd_317765 : Nat := 4983230072969 + 3 ^ 40 * 317765 * 2
def baseEnd_317765 : Nat := 54388726725351492225377

theorem tailTrace_317765 : CollatzResearch.WordTrace tailWord_317765 prefixEnd_317765 54388726725351492225377 := by
  unfold tailWord_317765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11589841693799149786458749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7726561129199433190972499 11589841693799149786458749)
  ·
    refine ⟨4346190635174681169922031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11589841693799149786458749 4346190635174681169922031)
    ·
      refine ⟨6519285952762021754883047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4346190635174681169922031 6519285952762021754883047)
      ·
        refine ⟨9778928929143032632324571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519285952762021754883047 9778928929143032632324571)
        ·
          refine ⟨14668393393714548948486857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778928929143032632324571 14668393393714548948486857)
          ·
            refine ⟨11001295045285911711365143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14668393393714548948486857 11001295045285911711365143)
            ·
              refine ⟨16501942567928867567047715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001295045285911711365143 16501942567928867567047715)
              ·
                refine ⟨24752913851893301350571573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16501942567928867567047715 24752913851893301350571573)
                ·
                  refine ⟨2320585673614997001616085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24752913851893301350571573 2320585673614997001616085)
                  ·
                    refine ⟨54388726725351492225377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2320585673614997001616085 54388726725351492225377)
                    ·
                      rfl

theorem cell23_317765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_317765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317765 prefixEnd_317765 := by exact prefixLift 317765
  have htrace : WordTrace (prefixWord ++ tailWord_317765) baseStart_317765 baseEnd_317765 := by
    simpa [prefixWord, tailWord_317765, baseEnd_317765] using wordTrace_append hprefix tailTrace_317765
  have hstable : (prefixWord ++ tailWord_317765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317765).length < 2 ^ (prefixWord ++ tailWord_317765).sum := by decide
  have hdescent : baseEnd_317765 < baseStart_317765 := by decide
  rcases family_descends (prefixWord ++ tailWord_317765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317775 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_317775 : Nat := 118140960795 + 317775 * 2 ^ 59
def prefixEnd_317775 : Nat := 4983230072969 + 3 ^ 40 * 317775 * 2
def baseEnd_317775 : Nat := 163171314982599437551085

theorem tailTrace_317775 : CollatzResearch.WordTrace tailWord_317775 prefixEnd_317775 163171314982599437551085 := by
  unfold tailWord_317775
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590206423762921494322779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7726804282508614329548519 11590206423762921494322779)
  ·
    refine ⟨17385309635644382241484169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11590206423762921494322779 17385309635644382241484169)
    ·
      refine ⟨13038982226733286681113127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17385309635644382241484169 13038982226733286681113127)
      ·
        refine ⟨19558473340099930021669691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13038982226733286681113127 19558473340099930021669691)
        ·
          refine ⟨29337710010149895032504537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19558473340099930021669691 29337710010149895032504537)
          ·
            refine ⟨22003282507612421274378403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29337710010149895032504537 22003282507612421274378403)
            ·
              refine ⟨33004923761418631911567605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22003282507612421274378403 33004923761418631911567605)
              ·
                refine ⟨3094211602632996741709463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33004923761418631911567605 3094211602632996741709463)
                ·
                  refine ⟨4641317403949495112564195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094211602632996741709463 4641317403949495112564195)
                  ·
                    refine ⟨6961976105924242668846293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641317403949495112564195 6961976105924242668846293)
                    ·
                      refine ⟨163171314982599437551085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6961976105924242668846293 163171314982599437551085)
                      ·
                        rfl

theorem cell23_317775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_317775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317775 prefixEnd_317775 := by exact prefixLift 317775
  have htrace : WordTrace (prefixWord ++ tailWord_317775) baseStart_317775 baseEnd_317775 := by
    simpa [prefixWord, tailWord_317775, baseEnd_317775] using wordTrace_append hprefix tailTrace_317775
  have hstable : (prefixWord ++ tailWord_317775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317775).length < 2 ^ (prefixWord ++ tailWord_317775).sum := by decide
  have hdescent : baseEnd_317775 < baseStart_317775 := by decide
  rcases family_descends (prefixWord ++ tailWord_317775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317799 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 2, 5]
def baseStart_317799 : Nat := 118140960795 + 317799 * 2 ^ 59
def prefixEnd_317799 : Nat := 4983230072969 + 3 ^ 40 * 317799 * 2
def baseEnd_317799 : Nat := 54394546172769114550325

theorem tailTrace_317799 : CollatzResearch.WordTrace tailWord_317799 prefixEnd_317799 54394546172769114550325 := by
  unfold tailWord_317799
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591081775675973593196451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7727387850450649062130967 11591081775675973593196451)
  ·
    refine ⟨17386622663513960389794677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11591081775675973593196451 17386622663513960389794677)
    ·
      refine ⟨1629995874704433786543251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17386622663513960389794677 1629995874704433786543251)
      ·
        refine ⟨2444993812056650679814877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629995874704433786543251 2444993812056650679814877)
        ·
          refine ⟨916872679521244004930579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2444993812056650679814877 916872679521244004930579)
          ·
            refine ⟨1375309019281866007395869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916872679521244004930579 1375309019281866007395869)
            ·
              refine ⟨515740882230699752773451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375309019281866007395869 515740882230699752773451)
              ·
                refine ⟨773611323346049629160177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515740882230699752773451 773611323346049629160177)
                ·
                  refine ⟨580208492509537221870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773611323346049629160177 580208492509537221870133)
                  ·
                    refine ⟨54394546172769114550325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 580208492509537221870133 54394546172769114550325)
                    ·
                      rfl

theorem cell23_317799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_317799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317799 prefixEnd_317799 := by exact prefixLift 317799
  have htrace : WordTrace (prefixWord ++ tailWord_317799) baseStart_317799 baseEnd_317799 := by
    simpa [prefixWord, tailWord_317799, baseEnd_317799] using wordTrace_append hprefix tailTrace_317799
  have hstable : (prefixWord ++ tailWord_317799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317799).length < 2 ^ (prefixWord ++ tailWord_317799).sum := by decide
  have hdescent : baseEnd_317799 < baseStart_317799 := by decide
  rcases family_descends (prefixWord ++ tailWord_317799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317814 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_317814 : Nat := 118140960795 + 317814 * 2 ^ 59
def prefixEnd_317814 : Nat := 4983230072969 + 3 ^ 40 * 317814 * 2
def baseEnd_317814 : Nat := 163191340728124784963407

theorem tailTrace_317814 : CollatzResearch.WordTrace tailWord_317814 prefixEnd_317814 163191340728124784963407 := by
  unfold tailWord_317814
  simp only [CollatzResearch.WordTrace]
  refine ⟨724476804413851947187031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7727752580414420769994997 724476804413851947187031)
  ·
    refine ⟨1086715206620777920780547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724476804413851947187031 1086715206620777920780547)
    ·
      refine ⟨1630072809931166881170821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086715206620777920780547 1630072809931166881170821)
      ·
        refine ⟨305638651862093790219529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1630072809931166881170821 305638651862093790219529)
        ·
          refine ⟨229228988896570342664647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305638651862093790219529 229228988896570342664647)
          ·
            refine ⟨343843483344855513996971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229228988896570342664647 343843483344855513996971)
            ·
              refine ⟨515765225017283270995457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343843483344855513996971 515765225017283270995457)
              ·
                refine ⟨386823918762962453246593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515765225017283270995457 386823918762962453246593)
                ·
                  refine ⟨290117939072221839934945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386823918762962453246593 290117939072221839934945)
                  ·
                    refine ⟨217588454304166379951209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290117939072221839934945 217588454304166379951209)
                    ·
                      refine ⟨163191340728124784963407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217588454304166379951209 163191340728124784963407)
                      ·
                        rfl

theorem cell23_317814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_317814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317814 prefixEnd_317814 := by exact prefixLift 317814
  have htrace : WordTrace (prefixWord ++ tailWord_317814) baseStart_317814 baseEnd_317814 := by
    simpa [prefixWord, tailWord_317814, baseEnd_317814] using wordTrace_append hprefix tailTrace_317814
  have hstable : (prefixWord ++ tailWord_317814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317814).length < 2 ^ (prefixWord ++ tailWord_317814).sum := by decide
  have hdescent : baseEnd_317814 < baseStart_317814 := by decide
  rcases family_descends (prefixWord ++ tailWord_317814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317819 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 2, 4, 2]
def baseStart_317819 : Nat := 118140960795 + 317819 * 2 ^ 59
def prefixEnd_317819 : Nat := 4983230072969 + 3 ^ 40 * 317819 * 2
def baseEnd_317819 : Nat := 163193908131397265400883

theorem tailTrace_317819 : CollatzResearch.WordTrace tailWord_317819 prefixEnd_317819 163193908131397265400883 := by
  unfold tailWord_317819
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591811235603517008924511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7727874157069011339283007 11591811235603517008924511)
  ·
    refine ⟨17387716853405275513386767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11591811235603517008924511 17387716853405275513386767)
    ·
      refine ⟨26081575280107913270080151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17387716853405275513386767 26081575280107913270080151)
      ·
        refine ⟨39122362920161869905120227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26081575280107913270080151 39122362920161869905120227)
        ·
          refine ⟨58683544380242804857680341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39122362920161869905120227 58683544380242804857680341)
          ·
            refine ⟨1375395571411940738851883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 58683544380242804857680341 1375395571411940738851883)
            ·
              refine ⟨2063093357117911108277825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375395571411940738851883 2063093357117911108277825)
              ·
                refine ⟨1547320017838433331208369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063093357117911108277825 1547320017838433331208369)
                ·
                  refine ⟨1160490013378824998406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547320017838433331208369 1160490013378824998406277)
                  ·
                    refine ⟨217591877508529687201177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160490013378824998406277 217591877508529687201177)
                    ·
                      refine ⟨163193908131397265400883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217591877508529687201177 163193908131397265400883)
                      ·
                        rfl

theorem cell23_317819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4, 2].length) (baseStart_317819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317819 prefixEnd_317819 := by exact prefixLift 317819
  have htrace : WordTrace (prefixWord ++ tailWord_317819) baseStart_317819 baseEnd_317819 := by
    simpa [prefixWord, tailWord_317819, baseEnd_317819] using wordTrace_append hprefix tailTrace_317819
  have hstable : (prefixWord ++ tailWord_317819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317819).length < 2 ^ (prefixWord ++ tailWord_317819).sum := by decide
  have hdescent : baseEnd_317819 < baseStart_317819 := by decide
  rcases family_descends (prefixWord ++ tailWord_317819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317832 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_317832 : Nat := 118140960795 + 317832 * 2 ^ 59
def prefixEnd_317832 : Nat := 4983230072969 + 3 ^ 40 * 317832 * 2
def baseEnd_317832 : Nat := 163200583379905714538323

theorem tailTrace_317832 : CollatzResearch.WordTrace tailWord_317832 prefixEnd_317832 163200583379905714538323 := by
  unfold tailWord_317832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5796142692278210114573875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7728190256370946819431833 5796142692278210114573875)
  ·
    refine ⟨8694214038417315171860813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5796142692278210114573875 8694214038417315171860813)
    ·
      refine ⟨3260330264406493189447805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8694214038417315171860813 3260330264406493189447805)
      ·
        refine ⟨1222623849152434946042927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3260330264406493189447805 1222623849152434946042927)
        ·
          refine ⟨1833935773728652419064391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222623849152434946042927 1833935773728652419064391)
          ·
            refine ⟨2750903660592978628596587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833935773728652419064391 2750903660592978628596587)
            ·
              refine ⟨4126355490889467942894881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750903660592978628596587 4126355490889467942894881)
              ·
                refine ⟨3094766618167100957171161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126355490889467942894881 3094766618167100957171161)
                ·
                  refine ⟨2321074963625325717878371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094766618167100957171161 2321074963625325717878371)
                  ·
                    refine ⟨3481612445437988576817557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2321074963625325717878371 3481612445437988576817557)
                    ·
                      refine ⟨163200583379905714538323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3481612445437988576817557 163200583379905714538323)
                      ·
                        rfl

theorem cell23_317832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_317832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317832 prefixEnd_317832 := by exact prefixLift 317832
  have htrace : WordTrace (prefixWord ++ tailWord_317832) baseStart_317832 baseEnd_317832 := by
    simpa [prefixWord, tailWord_317832, baseEnd_317832] using wordTrace_append hprefix tailTrace_317832
  have hstable : (prefixWord ++ tailWord_317832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317832).length < 2 ^ (prefixWord ++ tailWord_317832).sum := by decide
  have hdescent : baseEnd_317832 < baseStart_317832 := by decide
  rcases family_descends (prefixWord ++ tailWord_317832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317863 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 1, 4]
def baseStart_317863 : Nat := 118140960795 + 317863 * 2 ^ 59
def prefixEnd_317863 : Nat := 4983230072969 + 3 ^ 40 * 317863 * 2
def baseEnd_317863 : Nat := 54405500426731697750227

theorem tailTrace_317863 : CollatzResearch.WordTrace tailWord_317863 prefixEnd_317863 54405500426731697750227 := by
  unfold tailWord_317863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593416047444112523526243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7728944031629408349017495 11593416047444112523526243)
  ·
    refine ⟨17390124071166168785289365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593416047444112523526243 17390124071166168785289365)
    ·
      refine ⟨815162065835914161810439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17390124071166168785289365 815162065835914161810439)
      ·
        refine ⟨1222743098753871242715659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815162065835914161810439 1222743098753871242715659)
        ·
          refine ⟨1834114648130806864073489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222743098753871242715659 1834114648130806864073489)
          ·
            refine ⟨1375585986098105148055117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834114648130806864073489 1375585986098105148055117)
            ·
              refine ⟨515844744786789430520669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1375585986098105148055117 515844744786789430520669)
              ·
                refine ⟨193441779295046036445251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515844744786789430520669 193441779295046036445251)
                ·
                  refine ⟨290162668942569054667877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193441779295046036445251 290162668942569054667877)
                  ·
                    refine ⟨54405500426731697750227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290162668942569054667877 54405500426731697750227)
                    ·
                      rfl

theorem cell23_317863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_317863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317863 prefixEnd_317863 := by exact prefixLift 317863
  have htrace : WordTrace (prefixWord ++ tailWord_317863) baseStart_317863 baseEnd_317863 := by
    simpa [prefixWord, tailWord_317863, baseEnd_317863] using wordTrace_append hprefix tailTrace_317863
  have hstable : (prefixWord ++ tailWord_317863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317863).length < 2 ^ (prefixWord ++ tailWord_317863).sum := by decide
  have hdescent : baseEnd_317863 < baseStart_317863 := by decide
  rcases family_descends (prefixWord ++ tailWord_317863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317919 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 1, 6]
def baseStart_317919 : Nat := 118140960795 + 317919 * 2 ^ 59
def prefixEnd_317919 : Nat := 4983230072969 + 3 ^ 40 * 317919 * 2
def baseEnd_317919 : Nat := 54415085398948958050141

theorem tailTrace_317919 : CollatzResearch.WordTrace tailWord_317919 prefixEnd_317919 54415085398948958050141 := by
  unfold tailWord_317919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595458535241234087564811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7730305690160822725043207 11595458535241234087564811)
  ·
    refine ⟨17393187802861851131347217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595458535241234087564811 17393187802861851131347217)
    ·
      refine ⟨13044890852146388348510413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17393187802861851131347217 13044890852146388348510413)
      ·
        refine ⟨4891834069554895630691405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13044890852146388348510413 4891834069554895630691405)
        ·
          refine ⟨1834437776083085861509277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4891834069554895630691405 1834437776083085861509277)
          ·
            refine ⟨687914166031157198065979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1834437776083085861509277 687914166031157198065979)
            ·
              refine ⟨1031871249046735797098969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687914166031157198065979 1031871249046735797098969)
              ·
                refine ⟨773903436785051847824227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031871249046735797098969 773903436785051847824227)
                ·
                  refine ⟨1160855155177577771736341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773903436785051847824227 1160855155177577771736341)
                  ·
                    refine ⟨54415085398948958050141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1160855155177577771736341 54415085398948958050141)
                    ·
                      rfl

theorem cell23_317919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_317919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317919 prefixEnd_317919 := by exact prefixLift 317919
  have htrace : WordTrace (prefixWord ++ tailWord_317919) baseStart_317919 baseEnd_317919 := by
    simpa [prefixWord, tailWord_317919, baseEnd_317919] using wordTrace_append hprefix tailTrace_317919
  have hstable : (prefixWord ++ tailWord_317919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317919).length < 2 ^ (prefixWord ++ tailWord_317919).sum := by decide
  have hdescent : baseEnd_317919 < baseStart_317919 := by decide
  rcases family_descends (prefixWord ++ tailWord_317919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317923 : List Nat := [1, 1, 1, 6, 3, 1, 3, 1, 1, 5]
def baseStart_317923 : Nat := 118140960795 + 317923 * 2 ^ 59
def prefixEnd_317923 : Nat := 4983230072969 + 3 ^ 40 * 317923 * 2
def baseEnd_317923 : Nat := 54415770039821619500135

theorem tailTrace_317923 : CollatzResearch.WordTrace tailWord_317923 prefixEnd_317923 54415770039821619500135 := by
  unfold tailWord_317923
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595604427226742770710423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7730402951484495180473615 11595604427226742770710423)
  ·
    refine ⟨17393406640840114156065635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595604427226742770710423 17393406640840114156065635)
    ·
      refine ⟨26090109961260171234098453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17393406640840114156065635 26090109961260171234098453)
      ·
        refine ⟨1222973904434070526598365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26090109961260171234098453 1222973904434070526598365)
        ·
          refine ⟨458615214162776447474387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1222973904434070526598365 458615214162776447474387)
          ·
            refine ⟨687922821244164671211581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458615214162776447474387 687922821244164671211581)
            ·
              refine ⟨257971057966561751704343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687922821244164671211581 257971057966561751704343)
              ·
                refine ⟨386956586949842627556515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257971057966561751704343 386956586949842627556515)
                ·
                  refine ⟨580434880424763941334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386956586949842627556515 580434880424763941334773)
                  ·
                    refine ⟨54415770039821619500135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 580434880424763941334773 54415770039821619500135)
                    ·
                      rfl

theorem cell23_317923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 1, 5].length) (baseStart_317923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317923 prefixEnd_317923 := by exact prefixLift 317923
  have htrace : WordTrace (prefixWord ++ tailWord_317923) baseStart_317923 baseEnd_317923 := by
    simpa [prefixWord, tailWord_317923, baseEnd_317923] using wordTrace_append hprefix tailTrace_317923
  have hstable : (prefixWord ++ tailWord_317923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317923).length < 2 ^ (prefixWord ++ tailWord_317923).sum := by decide
  have hdescent : baseEnd_317923 < baseStart_317923 := by decide
  rcases family_descends (prefixWord ++ tailWord_317923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317936 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_317936 : Nat := 118140960795 + 317936 * 2 ^ 59
def prefixEnd_317936 : Nat := 4983230072969 + 3 ^ 40 * 317936 * 2
def baseEnd_317936 : Nat := 54417995122657769212615

theorem tailTrace_317936 : CollatzResearch.WordTrace tailWord_317936 prefixEnd_317936 54417995122657769212615 := by
  unfold tailWord_317936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798039288089822995466831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7730719050786430660622441 5798039288089822995466831)
  ·
    refine ⟨8697058932134734493200247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5798039288089822995466831 8697058932134734493200247)
    ·
      refine ⟨13045588398202101739800371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697058932134734493200247 13045588398202101739800371)
      ·
        refine ⟨19568382597303152609700557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13045588398202101739800371 19568382597303152609700557)
        ·
          refine ⟨7338143473988682228637709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19568382597303152609700557 7338143473988682228637709)
          ·
            refine ⟨2751803802745755835739141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7338143473988682228637709 2751803802745755835739141)
            ·
              refine ⟨515963213014829219201089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2751803802745755835739141 515963213014829219201089)
              ·
                refine ⟨386972409761121914400817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515963213014829219201089 386972409761121914400817)
                ·
                  refine ⟨290229307320841435800613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386972409761121914400817 290229307320841435800613)
                  ·
                    refine ⟨54417995122657769212615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290229307320841435800613 54417995122657769212615)
                    ·
                      rfl

theorem cell23_317936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_317936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317936 prefixEnd_317936 := by exact prefixLift 317936
  have htrace : WordTrace (prefixWord ++ tailWord_317936) baseStart_317936 baseEnd_317936 := by
    simpa [prefixWord, tailWord_317936, baseEnd_317936] using wordTrace_append hprefix tailTrace_317936
  have hstable : (prefixWord ++ tailWord_317936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317936).length < 2 ^ (prefixWord ++ tailWord_317936).sum := by decide
  have hdescent : baseEnd_317936 < baseStart_317936 := by decide
  rcases family_descends (prefixWord ++ tailWord_317936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317956 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_317956 : Nat := 118140960795 + 317956 * 2 ^ 59
def prefixEnd_317956 : Nat := 4983230072969 + 3 ^ 40 * 317956 * 2
def baseEnd_317956 : Nat := 163264254981063229387753

theorem tailTrace_317956 : CollatzResearch.WordTrace tailWord_317956 prefixEnd_317956 163264254981063229387753 := by
  unfold tailWord_317956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798404018053594703330861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7731205357404792937774481 5798404018053594703330861)
  ·
    refine ⟨2174401506770098013749073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5798404018053594703330861 2174401506770098013749073)
    ·
      refine ⟨1630801130077573510311805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2174401506770098013749073 1630801130077573510311805)
      ·
        refine ⟨611550423779090066366927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1630801130077573510311805 611550423779090066366927)
        ·
          refine ⟨917325635668635099550391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611550423779090066366927 917325635668635099550391)
          ·
            refine ⟨1375988453502952649325587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917325635668635099550391 1375988453502952649325587)
            ·
              refine ⟨2063982680254428973988381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375988453502952649325587 2063982680254428973988381)
              ·
                refine ⟨773993505095410865245643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063982680254428973988381 773993505095410865245643)
                ·
                  refine ⟨1160990257643116297868465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773993505095410865245643 1160990257643116297868465)
                  ·
                    refine ⟨870742693232337223401349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160990257643116297868465 870742693232337223401349)
                    ·
                      refine ⟨163264254981063229387753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 870742693232337223401349 163264254981063229387753)
                      ·
                        rfl

theorem cell23_317956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_317956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317956 prefixEnd_317956 := by exact prefixLift 317956
  have htrace : WordTrace (prefixWord ++ tailWord_317956) baseStart_317956 baseEnd_317956 := by
    simpa [prefixWord, tailWord_317956, baseEnd_317956] using wordTrace_append hprefix tailTrace_317956
  have hstable : (prefixWord ++ tailWord_317956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317956).length < 2 ^ (prefixWord ++ tailWord_317956).sum := by decide
  have hdescent : baseEnd_317956 < baseStart_317956 := by decide
  rcases family_descends (prefixWord ++ tailWord_317956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317966 : List Nat := [4, 1, 1, 2, 3, 2, 3, 7]
def baseStart_317966 : Nat := 118140960795 + 317966 * 2 ^ 59
def prefixEnd_317966 : Nat := 4983230072969 + 3 ^ 40 * 317966 * 2
def baseEnd_317966 : Nat := 6047014436578081120841

theorem tailTrace_317966 : CollatzResearch.WordTrace tailWord_317966 prefixEnd_317966 6047014436578081120841 := by
  unfold tailWord_317966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449646595758870139315719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7731448510713974076350501 1449646595758870139315719)
  ·
    refine ⟨2174469893638305208973579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449646595758870139315719 2174469893638305208973579)
    ·
      refine ⟨3261704840457457813460369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174469893638305208973579 3261704840457457813460369)
      ·
        refine ⟨2446278630343093360095277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261704840457457813460369 2446278630343093360095277)
        ·
          refine ⟨917354486378660010035729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2446278630343093360095277 917354486378660010035729)
          ·
            refine ⟨688015864783995007526797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917354486378660010035729 688015864783995007526797)
            ·
              refine ⟨258005949293998127822549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688015864783995007526797 258005949293998127822549)
              ·
                refine ⟨6047014436578081120841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 258005949293998127822549 6047014436578081120841)
                ·
                  rfl

theorem cell23_317966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_317966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317966 prefixEnd_317966 := by exact prefixLift 317966
  have htrace : WordTrace (prefixWord ++ tailWord_317966) baseStart_317966 baseEnd_317966 := by
    simpa [prefixWord, tailWord_317966, baseEnd_317966] using wordTrace_append hprefix tailTrace_317966
  have hstable : (prefixWord ++ tailWord_317966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317966).length < 2 ^ (prefixWord ++ tailWord_317966).sum := by decide
  have hdescent : baseEnd_317966 < baseStart_317966 := by decide
  rcases family_descends (prefixWord ++ tailWord_317966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317976 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_317976 : Nat := 118140960795 + 317976 * 2 ^ 59
def prefixEnd_317976 : Nat := 4983230072969 + 3 ^ 40 * 317976 * 2
def baseEnd_317976 : Nat := 163274524594153151137661

theorem tailTrace_317976 : CollatzResearch.WordTrace tailWord_317976 prefixEnd_317976 163274524594153151137661 := by
  unfold tailWord_317976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798768748017366411194891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7731691664023155214926521 5798768748017366411194891)
  ·
    refine ⟨8698153122026049616792337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5798768748017366411194891 8698153122026049616792337)
    ·
      refine ⟨6523614841519537212594253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8698153122026049616792337 6523614841519537212594253)
      ·
        refine ⟨2446355565569826454722845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6523614841519537212594253 2446355565569826454722845)
        ·
          refine ⟨917383337088684920521067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2446355565569826454722845 917383337088684920521067)
          ·
            refine ⟨1376075005633027380781601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917383337088684920521067 1376075005633027380781601)
            ·
              refine ⟨1032056254224770535586201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376075005633027380781601 1032056254224770535586201)
              ·
                refine ⟨774042190668577901689651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032056254224770535586201 774042190668577901689651)
                ·
                  refine ⟨1161063286002866852534477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774042190668577901689651 1161063286002866852534477)
                  ·
                    refine ⟨435398732251075069700429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161063286002866852534477 435398732251075069700429)
                    ·
                      refine ⟨163274524594153151137661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435398732251075069700429 163274524594153151137661)
                      ·
                        rfl

theorem cell23_317976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_317976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317976 prefixEnd_317976 := by exact prefixLift 317976
  have htrace : WordTrace (prefixWord ++ tailWord_317976) baseStart_317976 baseEnd_317976 := by
    simpa [prefixWord, tailWord_317976, baseEnd_317976] using wordTrace_append hprefix tailTrace_317976
  have hstable : (prefixWord ++ tailWord_317976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317976).length < 2 ^ (prefixWord ++ tailWord_317976).sum := by decide
  have hdescent : baseEnd_317976 < baseStart_317976 := by decide
  rcases family_descends (prefixWord ++ tailWord_317976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317980 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_317980 : Nat := 118140960795 + 317980 * 2 ^ 59
def prefixEnd_317980 : Nat := 4983230072969 + 3 ^ 40 * 317980 * 2
def baseEnd_317980 : Nat := 163276578516771135487643

theorem tailTrace_317980 : CollatzResearch.WordTrace tailWord_317980 prefixEnd_317980 163276578516771135487643 := by
  unfold tailWord_317980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798841694010120752767697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7731788925346827670356929 5798841694010120752767697)
  ·
    refine ⟨4349131270507590564575773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5798841694010120752767697 4349131270507590564575773)
    ·
      refine ⟨1630924226440346461715915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4349131270507590564575773 1630924226440346461715915)
      ·
        refine ⟨2446386339660519692573873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630924226440346461715915 2446386339660519692573873)
        ·
          refine ⟨1834789754745389769430405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446386339660519692573873 1834789754745389769430405)
          ·
            refine ⟨344023079014760581768201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1834789754745389769430405 344023079014760581768201)
            ·
              refine ⟨258017309261070436326151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344023079014760581768201 258017309261070436326151)
              ·
                refine ⟨387025963891605654489227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258017309261070436326151 387025963891605654489227)
                ·
                  refine ⟨580538945837408481733841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387025963891605654489227 580538945837408481733841)
                  ·
                    refine ⟨435404209378056361300381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580538945837408481733841 435404209378056361300381)
                    ·
                      refine ⟨163276578516771135487643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435404209378056361300381 163276578516771135487643)
                      ·
                        rfl

theorem cell23_317980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_317980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_317980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_317980 prefixEnd_317980 := by exact prefixLift 317980
  have htrace : WordTrace (prefixWord ++ tailWord_317980) baseStart_317980 baseEnd_317980 := by
    simpa [prefixWord, tailWord_317980, baseEnd_317980] using wordTrace_append hprefix tailTrace_317980
  have hstable : (prefixWord ++ tailWord_317980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317980).length < 2 ^ (prefixWord ++ tailWord_317980).sum := by decide
  have hdescent : baseEnd_317980 < baseStart_317980 := by decide
  rcases family_descends (prefixWord ++ tailWord_317980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318009 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 2, 6]
def baseStart_318009 : Nat := 118140960795 + 318009 * 2 ^ 59
def prefixEnd_318009 : Nat := 4983230072969 + 3 ^ 40 * 318009 * 2
def baseEnd_318009 : Nat := 54430489818583840675003

theorem tailTrace_318009 : CollatzResearch.WordTrace tailWord_318009 prefixEnd_318009 54430489818583840675003 := by
  unfold tailWord_318009
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598741104915179458341081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7732494069943452972227387 11598741104915179458341081)
  ·
    refine ⟨8699055828686384593755811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11598741104915179458341081 8699055828686384593755811)
    ·
      refine ⟨13048583743029576890633717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8699055828686384593755811 13048583743029576890633717)
      ·
        refine ⟨1223304725909022833496911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13048583743029576890633717 1223304725909022833496911)
        ·
          refine ⟨1834957088863534250245367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223304725909022833496911 1834957088863534250245367)
          ·
            refine ⟨2752435633295301375368051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834957088863534250245367 2752435633295301375368051)
            ·
              refine ⟨4128653449942952063052077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752435633295301375368051 4128653449942952063052077)
              ·
                refine ⟨1548245043728607023644529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4128653449942952063052077 1548245043728607023644529)
                ·
                  refine ⟨1161183782796455267733397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548245043728607023644529 1161183782796455267733397)
                  ·
                    refine ⟨54430489818583840675003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1161183782796455267733397 54430489818583840675003)
                    ·
                      rfl

theorem cell23_318009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_318009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318009 prefixEnd_318009 := by exact prefixLift 318009
  have htrace : WordTrace (prefixWord ++ tailWord_318009) baseStart_318009 baseEnd_318009 := by
    simpa [prefixWord, tailWord_318009, baseEnd_318009] using wordTrace_append hprefix tailTrace_318009
  have hstable : (prefixWord ++ tailWord_318009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318009).length < 2 ^ (prefixWord ++ tailWord_318009).sum := by decide
  have hdescent : baseEnd_318009 < baseStart_318009 := by decide
  rcases family_descends (prefixWord ++ tailWord_318009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318010 : List Nat := [3, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_318010 : Nat := 118140960795 + 318010 * 2 ^ 59
def prefixEnd_318010 : Nat := 4983230072969 + 3 ^ 40 * 318010 * 2
def baseEnd_318010 : Nat := 163291982936406018112505

theorem tailTrace_318010 : CollatzResearch.WordTrace tailWord_318010 prefixEnd_318010 163291982936406018112505 := by
  unfold tailWord_318010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899694394477889157281871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7732518385274371086084989 2899694394477889157281871)
  ·
    refine ⟨4349541591716833735922807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899694394477889157281871 4349541591716833735922807)
    ·
      refine ⟨6524312387575250603884211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349541591716833735922807 6524312387575250603884211)
      ·
        refine ⟨9786468581362875905826317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524312387575250603884211 9786468581362875905826317)
        ·
          refine ⟨3669925718011078464684869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9786468581362875905826317 3669925718011078464684869)
          ·
            refine ⟨688111072127077212128413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3669925718011078464684869 688111072127077212128413)
            ·
              refine ⟨258041652047653954548155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688111072127077212128413 258041652047653954548155)
              ·
                refine ⟨387062478071480931822233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258041652047653954548155 387062478071480931822233)
                ·
                  refine ⟨290296858553610698866675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387062478071480931822233 290296858553610698866675)
                  ·
                    refine ⟨435445287830416048300013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290296858553610698866675 435445287830416048300013)
                    ·
                      refine ⟨163291982936406018112505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435445287830416048300013 163291982936406018112505)
                      ·
                        rfl

theorem cell23_318010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_318010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318010 prefixEnd_318010 := by exact prefixLift 318010
  have htrace : WordTrace (prefixWord ++ tailWord_318010) baseStart_318010 baseEnd_318010 := by
    simpa [prefixWord, tailWord_318010, baseEnd_318010] using wordTrace_append hprefix tailTrace_318010
  have hstable : (prefixWord ++ tailWord_318010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318010).length < 2 ^ (prefixWord ++ tailWord_318010).sum := by decide
  have hdescent : baseEnd_318010 < baseStart_318010 := by decide
  rcases family_descends (prefixWord ++ tailWord_318010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3]
def baseStart_318019 : Nat := 118140960795 + 318019 * 2 ^ 59
def prefixEnd_318019 : Nat := 4983230072969 + 3 ^ 40 * 318019 * 2
def baseEnd_318019 : Nat := 163296604262296482899963

theorem tailTrace_318019 : CollatzResearch.WordTrace tailWord_318019 prefixEnd_318019 163296604262296482899963 := by
  unfold tailWord_318019
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599105834878951166205111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7732737223252634110803407 11599105834878951166205111)
  ·
    refine ⟨17398658752318426749307667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11599105834878951166205111 17398658752318426749307667)
    ·
      refine ⟨26097988128477640123961501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17398658752318426749307667 26097988128477640123961501)
      ·
        refine ⟨9786745548179115046485563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26097988128477640123961501 9786745548179115046485563)
        ·
          refine ⟨14680118322268672569728345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9786745548179115046485563 14680118322268672569728345)
          ·
            refine ⟨11010088741701504427296259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14680118322268672569728345 11010088741701504427296259)
            ·
              refine ⟨16515133112552256640944389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010088741701504427296259 16515133112552256640944389)
              ·
                refine ⟨3096587458603548120177073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16515133112552256640944389 3096587458603548120177073)
                ·
                  refine ⟨2322440593952661090132805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096587458603548120177073 2322440593952661090132805)
                  ·
                    refine ⟨435457611366123954399901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322440593952661090132805 435457611366123954399901)
                    ·
                      refine ⟨163296604262296482899963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435457611366123954399901 163296604262296482899963)
                      ·
                        rfl

theorem cell23_318019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_318019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318019 prefixEnd_318019 := by exact prefixLift 318019
  have htrace : WordTrace (prefixWord ++ tailWord_318019) baseStart_318019 baseEnd_318019 := by
    simpa [prefixWord, tailWord_318019, baseEnd_318019] using wordTrace_append hprefix tailTrace_318019
  have hstable : (prefixWord ++ tailWord_318019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318019).length < 2 ^ (prefixWord ++ tailWord_318019).sum := by decide
  have hdescent : baseEnd_318019 < baseStart_318019 := by decide
  rcases family_descends (prefixWord ++ tailWord_318019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318033 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 4, 2, 2]
def baseStart_318033 : Nat := 118140960795 + 318033 * 2 ^ 59
def prefixEnd_318033 : Nat := 4983230072969 + 3 ^ 40 * 318033 * 2
def baseEnd_318033 : Nat := 163303792991459428124899

theorem tailTrace_318033 : CollatzResearch.WordTrace tailWord_318033 prefixEnd_318033 163303792991459428124899 := by
  unfold tailWord_318033
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599616456828231557214753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7733077637885487704809835 11599616456828231557214753)
  ·
    refine ⟨8699712342621173667911065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11599616456828231557214753 8699712342621173667911065)
    ·
      refine ⟨6524784256965880250933299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699712342621173667911065 6524784256965880250933299)
      ·
        refine ⟨9787176385448820376399949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524784256965880250933299 9787176385448820376399949)
        ·
          refine ⟨3670191144543307641149981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9787176385448820376399949 3670191144543307641149981)
          ·
            refine ⟨1376321679203740365431243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3670191144543307641149981 1376321679203740365431243)
            ·
              refine ⟨2064482518805610548146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376321679203740365431243 2064482518805610548146865)
              ·
                refine ⟨1548361889104207911110149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064482518805610548146865 1548361889104207911110149)
                ·
                  refine ⟨290317854207038983333153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1548361889104207911110149 290317854207038983333153)
                  ·
                    refine ⟨217738390655279237499865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290317854207038983333153 217738390655279237499865)
                    ·
                      refine ⟨163303792991459428124899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217738390655279237499865 163303792991459428124899)
                      ·
                        rfl

theorem cell23_318033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_318033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318033 prefixEnd_318033 := by exact prefixLift 318033
  have htrace : WordTrace (prefixWord ++ tailWord_318033) baseStart_318033 baseEnd_318033 := by
    simpa [prefixWord, tailWord_318033, baseEnd_318033] using wordTrace_append hprefix tailTrace_318033
  have hstable : (prefixWord ++ tailWord_318033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318033).length < 2 ^ (prefixWord ++ tailWord_318033).sum := by decide
  have hdescent : baseEnd_318033 < baseStart_318033 := by decide
  rcases family_descends (prefixWord ++ tailWord_318033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318036 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_318036 : Nat := 118140960795 + 318036 * 2 ^ 59
def prefixEnd_318036 : Nat := 4983230072969 + 3 ^ 40 * 318036 * 2
def baseEnd_318036 : Nat := 163305333433422916387385

theorem tailTrace_318036 : CollatzResearch.WordTrace tailWord_318036 prefixEnd_318036 163305333433422916387385 := by
  unfold tailWord_318036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799862937908681534786981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7733150583878242046382641 5799862937908681534786981)
  ·
    refine ⟨1087474300857877787772559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5799862937908681534786981 1087474300857877787772559)
    ·
      refine ⟨1631211451286816681658839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087474300857877787772559 1631211451286816681658839)
      ·
        refine ⟨2446817176930225022488259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631211451286816681658839 2446817176930225022488259)
        ·
          refine ⟨3670225765395337533732389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446817176930225022488259 3670225765395337533732389)
          ·
            refine ⟨688167331011625787574823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3670225765395337533732389 688167331011625787574823)
            ·
              refine ⟨1032250996517438681362235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688167331011625787574823 1032250996517438681362235)
              ·
                refine ⟨1548376494776158022043353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032250996517438681362235 1548376494776158022043353)
                ·
                  refine ⟨1161282371082118516532515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548376494776158022043353 1161282371082118516532515)
                  ·
                    refine ⟨1741923556623177774798773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161282371082118516532515 1741923556623177774798773)
                    ·
                      refine ⟨163305333433422916387385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1741923556623177774798773 163305333433422916387385)
                      ·
                        rfl

theorem cell23_318036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_318036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318036 prefixEnd_318036 := by exact prefixLift 318036
  have htrace : WordTrace (prefixWord ++ tailWord_318036) baseStart_318036 baseEnd_318036 := by
    simpa [prefixWord, tailWord_318036, baseEnd_318036] using wordTrace_append hprefix tailTrace_318036
  have hstable : (prefixWord ++ tailWord_318036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318036).length < 2 ^ (prefixWord ++ tailWord_318036).sum := by decide
  have hdescent : baseEnd_318036 < baseStart_318036 := by decide
  rcases family_descends (prefixWord ++ tailWord_318036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318133 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_318133 : Nat := 118140960795 + 318133 * 2 ^ 59
def prefixEnd_318133 : Nat := 4983230072969 + 3 ^ 40 * 318133 * 2
def baseEnd_318133 : Nat := 54451713685636345624813

theorem tailTrace_318133 : CollatzResearch.WordTrace tailWord_318133 prefixEnd_318133 54451713685636345624813 := by
  unfold tailWord_318133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603263756465948635855053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735509170977299090570035 11603263756465948635855053)
  ·
    refine ⟨4351223908674730738445645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11603263756465948635855053 4351223908674730738445645)
    ·
      refine ⟨1631708965753024026917117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4351223908674730738445645 1631708965753024026917117)
      ·
        refine ⟨611890862157384010093919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1631708965753024026917117 611890862157384010093919)
        ·
          refine ⟨917836293236076015140879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611890862157384010093919 917836293236076015140879)
          ·
            refine ⟨1376754439854114022711319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917836293236076015140879 1376754439854114022711319)
            ·
              refine ⟨2065131659781171034066979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376754439854114022711319 2065131659781171034066979)
              ·
                refine ⟨3097697489671756551100469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065131659781171034066979 3097697489671756551100469)
                ·
                  refine ⟨290409139656727176665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3097697489671756551100469 290409139656727176665669)
                  ·
                    refine ⟨54451713685636345624813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290409139656727176665669 54451713685636345624813)
                    ·
                      rfl

theorem cell23_318133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_318133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318133 prefixEnd_318133 := by exact prefixLift 318133
  have htrace : WordTrace (prefixWord ++ tailWord_318133) baseStart_318133 baseEnd_318133 := by
    simpa [prefixWord, tailWord_318133, baseEnd_318133] using wordTrace_append hprefix tailTrace_318133
  have hstable : (prefixWord ++ tailWord_318133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318133).length < 2 ^ (prefixWord ++ tailWord_318133).sum := by decide
  have hdescent : baseEnd_318133 < baseStart_318133 := by decide
  rcases family_descends (prefixWord ++ tailWord_318133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318143 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_318143 : Nat := 118140960795 + 318143 * 2 ^ 59
def prefixEnd_318143 : Nat := 4983230072969 + 3 ^ 40 * 318143 * 2
def baseEnd_318143 : Nat := 163360275863453997749393

theorem tailTrace_318143 : CollatzResearch.WordTrace tailWord_318143 prefixEnd_318143 163360275863453997749393 := by
  unfold tailWord_318143
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603628486429720343719083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735752324286480229146055 11603628486429720343719083)
  ·
    refine ⟨17405442729644580515578625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11603628486429720343719083 17405442729644580515578625)
    ·
      refine ⟨13054082047233435386683969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17405442729644580515578625 13054082047233435386683969)
      ·
        refine ⟨9790561535425076540012977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13054082047233435386683969 9790561535425076540012977)
        ·
          refine ⟨7342921151568807405009733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9790561535425076540012977 7342921151568807405009733)
          ·
            refine ⟨1376797715919151388439325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7342921151568807405009733 1376797715919151388439325)
            ·
              refine ⟨516299143469681770664747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376797715919151388439325 516299143469681770664747)
              ·
                refine ⟨774448715204522655997121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516299143469681770664747 774448715204522655997121)
                ·
                  refine ⟨580836536403391991997841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 774448715204522655997121 580836536403391991997841)
                  ·
                    refine ⟨435627402302543993998381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580836536403391991997841 435627402302543993998381)
                    ·
                      refine ⟨163360275863453997749393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435627402302543993998381 163360275863453997749393)
                      ·
                        rfl

theorem cell23_318143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_318143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318143 prefixEnd_318143 := by exact prefixLift 318143
  have htrace : WordTrace (prefixWord ++ tailWord_318143) baseStart_318143 baseEnd_318143 := by
    simpa [prefixWord, tailWord_318143, baseEnd_318143] using wordTrace_append hprefix tailTrace_318143
  have hstable : (prefixWord ++ tailWord_318143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318143).length < 2 ^ (prefixWord ++ tailWord_318143).sum := by decide
  have hdescent : baseEnd_318143 < baseStart_318143 := by decide
  rcases family_descends (prefixWord ++ tailWord_318143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318149 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_318149 : Nat := 118140960795 + 318149 * 2 ^ 59
def prefixEnd_318149 : Nat := 4983230072969 + 3 ^ 40 * 318149 * 2
def baseEnd_318149 : Nat := 163363356747380974274365

theorem tailTrace_318149 : CollatzResearch.WordTrace tailWord_318149 prefixEnd_318149 163363356747380974274365 := by
  unfold tailWord_318149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603847324407983368437501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7735898216271988912291667 11603847324407983368437501)
  ·
    refine ⟨4351442746652993763164063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11603847324407983368437501 4351442746652993763164063)
    ·
      refine ⟨6527164119979490644746095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351442746652993763164063 6527164119979490644746095)
      ·
        refine ⟨9790746179969235967119143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527164119979490644746095 9790746179969235967119143)
        ·
          refine ⟨14686119269953853950678715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790746179969235967119143 14686119269953853950678715)
          ·
            refine ⟨22029178904930780926018073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14686119269953853950678715 22029178904930780926018073)
            ·
              refine ⟨16521884178698085694513555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22029178904930780926018073 16521884178698085694513555)
              ·
                refine ⟨24782826268047128541770333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16521884178698085694513555 24782826268047128541770333)
                ·
                  refine ⟨9293559850517673203163875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24782826268047128541770333 9293559850517673203163875)
                  ·
                    refine ⟨13940339775776509804745813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9293559850517673203163875 13940339775776509804745813)
                    ·
                      refine ⟨163363356747380974274365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 13940339775776509804745813 163363356747380974274365)
                      ·
                        rfl

theorem cell23_318149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_318149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318149 prefixEnd_318149 := by exact prefixLift 318149
  have htrace : WordTrace (prefixWord ++ tailWord_318149) baseStart_318149 baseEnd_318149 := by
    simpa [prefixWord, tailWord_318149, baseEnd_318149] using wordTrace_append hprefix tailTrace_318149
  have hstable : (prefixWord ++ tailWord_318149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318149).length < 2 ^ (prefixWord ++ tailWord_318149).sum := by decide
  have hdescent : baseEnd_318149 < baseStart_318149 := by decide
  rcases family_descends (prefixWord ++ tailWord_318149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318190 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_318190 : Nat := 118140960795 + 318190 * 2 ^ 59
def prefixEnd_318190 : Nat := 4983230072969 + 3 ^ 40 * 318190 * 2
def baseEnd_318190 : Nat := 163384409454215313861677

theorem tailTrace_318190 : CollatzResearch.WordTrace tailWord_318190 prefixEnd_318190 163384409454215313861677 := by
  unfold tailWord_318190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450667839657430921335003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7736895144839631580453349 1450667839657430921335003)
  ·
    refine ⟨2176001759486146382002505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450667839657430921335003 2176001759486146382002505)
    ·
      refine ⟨1632001319614609786501879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176001759486146382002505 1632001319614609786501879)
      ·
        refine ⟨2448001979421914679752819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632001319614609786501879 2448001979421914679752819)
        ·
          refine ⟨3672002969132872019629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448001979421914679752819 3672002969132872019629229)
          ·
            refine ⟨1377001113424827007360961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3672002969132872019629229 1377001113424827007360961)
            ·
              refine ⟨1032750835068620255520721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377001113424827007360961 1032750835068620255520721)
              ·
                refine ⟨774563126301465191640541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032750835068620255520721 774563126301465191640541)
                ·
                  refine ⟨290461172363049446865203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 774563126301465191640541 290461172363049446865203)
                  ·
                    refine ⟨435691758544574170297805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290461172363049446865203 435691758544574170297805)
                    ·
                      refine ⟨163384409454215313861677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435691758544574170297805 163384409454215313861677)
                      ·
                        rfl

theorem cell23_318190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_318190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318190 prefixEnd_318190 := by exact prefixLift 318190
  have htrace : WordTrace (prefixWord ++ tailWord_318190) baseStart_318190 baseEnd_318190 := by
    simpa [prefixWord, tailWord_318190, baseEnd_318190] using wordTrace_append hprefix tailTrace_318190
  have hstable : (prefixWord ++ tailWord_318190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318190).length < 2 ^ (prefixWord ++ tailWord_318190).sum := by decide
  have hdescent : baseEnd_318190 < baseStart_318190 := by decide
  rcases family_descends (prefixWord ++ tailWord_318190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318193 : List Nat := [1, 2, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_318193 : Nat := 118140960795 + 318193 * 2 ^ 59
def prefixEnd_318193 : Nat := 4983230072969 + 3 ^ 40 * 318193 * 2
def baseEnd_318193 : Nat := 54461983298726267374721

theorem tailTrace_318193 : CollatzResearch.WordTrace tailWord_318193 prefixEnd_318193 54461983298726267374721 := by
  unfold tailWord_318193
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605452136248578883039233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7736968090832385922026155 11605452136248578883039233)
  ·
    refine ⟨8704089102186434162279425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11605452136248578883039233 8704089102186434162279425)
    ·
      refine ⟨6528066826639825621709569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8704089102186434162279425 6528066826639825621709569)
      ·
        refine ⟨4896050119979869216282177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6528066826639825621709569 4896050119979869216282177)
        ·
          refine ⟨3672037589984901912211633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4896050119979869216282177 3672037589984901912211633)
          ·
            refine ⟨2754028192488676434158725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672037589984901912211633 2754028192488676434158725)
            ·
              refine ⟨516380286091626831404761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2754028192488676434158725 516380286091626831404761)
              ·
                refine ⟨387285214568720123553571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516380286091626831404761 387285214568720123553571)
                ·
                  refine ⟨580927821853080185330357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387285214568720123553571 580927821853080185330357)
                  ·
                    refine ⟨54461983298726267374721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 580927821853080185330357 54461983298726267374721)
                    ·
                      rfl

theorem cell23_318193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_318193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318193 prefixEnd_318193 := by exact prefixLift 318193
  have htrace : WordTrace (prefixWord ++ tailWord_318193) baseStart_318193 baseEnd_318193 := by
    simpa [prefixWord, tailWord_318193, baseEnd_318193] using wordTrace_append hprefix tailTrace_318193
  have hstable : (prefixWord ++ tailWord_318193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318193).length < 2 ^ (prefixWord ++ tailWord_318193).sum := by decide
  have hdescent : baseEnd_318193 < baseStart_318193 := by decide
  rcases family_descends (prefixWord ++ tailWord_318193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318210 : List Nat := [3, 4, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_318210 : Nat := 118140960795 + 318210 * 2 ^ 59
def prefixEnd_318210 : Nat := 4983230072969 + 3 ^ 40 * 318210 * 2
def baseEnd_318210 : Nat := 54464893022435078537195

theorem tailTrace_318210 : CollatzResearch.WordTrace tailWord_318210 prefixEnd_318210 54464893022435078537195 := by
  unfold tailWord_318210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901518044296747696602021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7737381451457993857605389 2901518044296747696602021)
  ·
    refine ⟨544034633305640193112879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2901518044296747696602021 544034633305640193112879)
    ·
      refine ⟨816051949958460289669319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544034633305640193112879 816051949958460289669319)
      ·
        refine ⟨1224077924937690434503979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816051949958460289669319 1224077924937690434503979)
        ·
          refine ⟨1836116887406535651755969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224077924937690434503979 1836116887406535651755969)
          ·
            refine ⟨1377087665554901738816977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836116887406535651755969 1377087665554901738816977)
            ·
              refine ⟨1032815749166176304112733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377087665554901738816977 1032815749166176304112733)
              ·
                refine ⟨387305905937316114042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032815749166176304112733 387305905937316114042275)
                ·
                  refine ⟨580958858905974171063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387305905937316114042275 580958858905974171063413)
                  ·
                    refine ⟨54464893022435078537195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 580958858905974171063413 54464893022435078537195)
                    ·
                      rfl

theorem cell23_318210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_318210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318210 prefixEnd_318210 := by exact prefixLift 318210
  have htrace : WordTrace (prefixWord ++ tailWord_318210) baseStart_318210 baseEnd_318210 := by
    simpa [prefixWord, tailWord_318210, baseEnd_318210] using wordTrace_append hprefix tailTrace_318210
  have hstable : (prefixWord ++ tailWord_318210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318210).length < 2 ^ (prefixWord ++ tailWord_318210).sum := by decide
  have hdescent : baseEnd_318210 < baseStart_318210 := by decide
  rcases family_descends (prefixWord ++ tailWord_318210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318223 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 2, 4]
def baseStart_318223 : Nat := 118140960795 + 318223 * 2 ^ 59
def prefixEnd_318223 : Nat := 4983230072969 + 3 ^ 40 * 318223 * 2
def baseEnd_318223 : Nat := 54467118105271228249675

theorem tailTrace_318223 : CollatzResearch.WordTrace tailWord_318223 prefixEnd_318223 54467118105271228249675 := by
  unfold tailWord_318223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606546326139894006631323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7737697550759929337754215 11606546326139894006631323)
  ·
    refine ⟨17409819489209841009946985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11606546326139894006631323 17409819489209841009946985)
    ·
      refine ⟨13057364616907380757460239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17409819489209841009946985 13057364616907380757460239)
      ·
        refine ⟨19586046925361071136190359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13057364616907380757460239 19586046925361071136190359)
        ·
          refine ⟨29379070388041606704285539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19586046925361071136190359 29379070388041606704285539)
          ·
            refine ⟨44068605582062410056428309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29379070388041606704285539 44068605582062410056428309)
            ·
              refine ⟨2065715886659175471395077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44068605582062410056428309 2065715886659175471395077)
              ·
                refine ⟨387321728748595400886577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065715886659175471395077 387321728748595400886577)
                ·
                  refine ⟨290491296561446550664933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387321728748595400886577 290491296561446550664933)
                  ·
                    refine ⟨54467118105271228249675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290491296561446550664933 54467118105271228249675)
                    ·
                      rfl

theorem cell23_318223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_318223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318223 prefixEnd_318223 := by exact prefixLift 318223
  have htrace : WordTrace (prefixWord ++ tailWord_318223) baseStart_318223 baseEnd_318223 := by
    simpa [prefixWord, tailWord_318223, baseEnd_318223] using wordTrace_append hprefix tailTrace_318223
  have hstable : (prefixWord ++ tailWord_318223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318223).length < 2 ^ (prefixWord ++ tailWord_318223).sum := by decide
  have hdescent : baseEnd_318223 < baseStart_318223 := by decide
  rcases family_descends (prefixWord ++ tailWord_318223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318236 : List Nat := [2, 2, 3, 1, 1, 3, 1, 10]
def baseStart_318236 : Nat := 118140960795 + 318236 * 2 ^ 59
def prefixEnd_318236 : Nat := 4983230072969 + 3 ^ 40 * 318236 * 2
def baseEnd_318236 : Nat := 6052149243123041995795

theorem tailTrace_318236 : CollatzResearch.WordTrace tailWord_318236 prefixEnd_318236 6052149243123041995795 := by
  unfold tailWord_318236
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803510237546398613427281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7738013650061864817903041 5803510237546398613427281)
  ·
    refine ⟨4352632678159798960070461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5803510237546398613427281 4352632678159798960070461)
    ·
      refine ⟨1632237254309924610026423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4352632678159798960070461 1632237254309924610026423)
      ·
        refine ⟨2448355881464886915039635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632237254309924610026423 2448355881464886915039635)
        ·
          refine ⟨3672533822197330372559453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448355881464886915039635 3672533822197330372559453)
          ·
            refine ⟨1377200183323998889709795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3672533822197330372559453 1377200183323998889709795)
            ·
              refine ⟨2065800274985998334564693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377200183323998889709795 2065800274985998334564693)
              ·
                refine ⟨6052149243123041995795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2065800274985998334564693 6052149243123041995795)
                ·
                  rfl

theorem cell23_318236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 10].length) (baseStart_318236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318236 prefixEnd_318236 := by exact prefixLift 318236
  have htrace : WordTrace (prefixWord ++ tailWord_318236) baseStart_318236 baseEnd_318236 := by
    simpa [prefixWord, tailWord_318236, baseEnd_318236] using wordTrace_append hprefix tailTrace_318236
  have hstable : (prefixWord ++ tailWord_318236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318236).length < 2 ^ (prefixWord ++ tailWord_318236).sum := by decide
  have hdescent : baseEnd_318236 < baseStart_318236 := by decide
  rcases family_descends (prefixWord ++ tailWord_318236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318240 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_318240 : Nat := 118140960795 + 318240 * 2 ^ 59
def prefixEnd_318240 : Nat := 4983230072969 + 3 ^ 40 * 318240 * 2
def baseEnd_318240 : Nat := 54470027828980039412149

theorem tailTrace_318240 : CollatzResearch.WordTrace tailWord_318240 prefixEnd_318240 54470027828980039412149 := by
  unfold tailWord_318240
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803583183539152955000087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7738110911385537273333449 5803583183539152955000087)
  ·
    refine ⟨8705374775308729432500131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803583183539152955000087 8705374775308729432500131)
    ·
      refine ⟨13058062162963094148750197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705374775308729432500131 13058062162963094148750197)
      ·
        refine ⟨1224193327777790076445331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13058062162963094148750197 1224193327777790076445331)
        ·
          refine ⟨1836289991666685114667997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224193327777790076445331 1836289991666685114667997)
          ·
            refine ⟨688608746875006918000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1836289991666685114667997 688608746875006918000499)
            ·
              refine ⟨1032913120312510377000749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688608746875006918000499 1032913120312510377000749)
              ·
                refine ⟨387342420117191391375281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032913120312510377000749 387342420117191391375281)
                ·
                  refine ⟨290506815087893543531461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387342420117191391375281 290506815087893543531461)
                  ·
                    refine ⟨54470027828980039412149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290506815087893543531461 54470027828980039412149)
                    ·
                      rfl

theorem cell23_318240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_318240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318240 prefixEnd_318240 := by exact prefixLift 318240
  have htrace : WordTrace (prefixWord ++ tailWord_318240) baseStart_318240 baseEnd_318240 := by
    simpa [prefixWord, tailWord_318240, baseEnd_318240] using wordTrace_append hprefix tailTrace_318240
  have hstable : (prefixWord ++ tailWord_318240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318240).length < 2 ^ (prefixWord ++ tailWord_318240).sum := by decide
  have hdescent : baseEnd_318240 < baseStart_318240 := by decide
  rcases family_descends (prefixWord ++ tailWord_318240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318263 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_318263 : Nat := 118140960795 + 318263 * 2 ^ 59
def prefixEnd_318263 : Nat := 4983230072969 + 3 ^ 40 * 318263 * 2
def baseEnd_318263 : Nat := 163421893541993528248841

theorem tailTrace_318263 : CollatzResearch.WordTrace tailWord_318263 prefixEnd_318263 163421893541993528248841 := by
  unfold tailWord_318263
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608005245994980838087443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7738670163996653892058295 11608005245994980838087443)
  ·
    refine ⟨17412007868992471257131165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11608005245994980838087443 17412007868992471257131165)
    ·
      refine ⟨6529502950872176721424187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17412007868992471257131165 6529502950872176721424187)
      ·
        refine ⟨9794254426308265082136281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529502950872176721424187 9794254426308265082136281)
        ·
          refine ⟨7345690819731198811602211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9794254426308265082136281 7345690819731198811602211)
          ·
            refine ⟨11018536229596798217403317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345690819731198811602211 11018536229596798217403317)
            ·
              refine ⟨1032987771524699832881561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11018536229596798217403317 1032987771524699832881561)
              ·
                refine ⟨774740828643524874661171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032987771524699832881561 774740828643524874661171)
                ·
                  refine ⟨1162111242965287311991757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774740828643524874661171 1162111242965287311991757)
                  ·
                    refine ⟨435791716111982741996909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162111242965287311991757 435791716111982741996909)
                    ·
                      refine ⟨163421893541993528248841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 435791716111982741996909 163421893541993528248841)
                      ·
                        rfl

theorem cell23_318263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_318263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318263 prefixEnd_318263 := by exact prefixLift 318263
  have htrace : WordTrace (prefixWord ++ tailWord_318263) baseStart_318263 baseEnd_318263 := by
    simpa [prefixWord, tailWord_318263, baseEnd_318263] using wordTrace_append hprefix tailTrace_318263
  have hstable : (prefixWord ++ tailWord_318263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318263).length < 2 ^ (prefixWord ++ tailWord_318263).sum := by decide
  have hdescent : baseEnd_318263 < baseStart_318263 := by decide
  rcases family_descends (prefixWord ++ tailWord_318263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318281 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 1, 2, 2]
def baseStart_318281 : Nat := 118140960795 + 318281 * 2 ^ 59
def prefixEnd_318281 : Nat := 4983230072969 + 3 ^ 40 * 318281 * 2
def baseEnd_318281 : Nat := 163431136193774457823759

theorem tailTrace_318281 : CollatzResearch.WordTrace tailWord_318281 prefixEnd_318281 163431136193774457823759 := by
  unfold tailWord_318281
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608661759929769912242697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7739107839953179941495131 11608661759929769912242697)
  ·
    refine ⟨8706496319947327434182023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11608661759929769912242697 8706496319947327434182023)
    ·
      refine ⟨13059744479920991151273035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8706496319947327434182023 13059744479920991151273035)
      ·
        refine ⟨19589616719881486726909553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13059744479920991151273035 19589616719881486726909553)
        ·
          refine ⟨14692212539911115045182165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19589616719881486726909553 14692212539911115045182165)
          ·
            refine ⟨344348731404166758871457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14692212539911115045182165 344348731404166758871457)
            ·
              refine ⟨258261548553125069153593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344348731404166758871457 258261548553125069153593)
              ·
                refine ⟨193696161414843801865195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258261548553125069153593 193696161414843801865195)
                ·
                  refine ⟨290544242122265702797793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193696161414843801865195 290544242122265702797793)
                  ·
                    refine ⟨217908181591699277098345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290544242122265702797793 217908181591699277098345)
                    ·
                      refine ⟨163431136193774457823759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217908181591699277098345 163431136193774457823759)
                      ·
                        rfl

theorem cell23_318281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 1, 2, 2].length) (baseStart_318281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318281 prefixEnd_318281 := by exact prefixLift 318281
  have htrace : WordTrace (prefixWord ++ tailWord_318281) baseStart_318281 baseEnd_318281 := by
    simpa [prefixWord, tailWord_318281, baseEnd_318281] using wordTrace_append hprefix tailTrace_318281
  have hstable : (prefixWord ++ tailWord_318281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318281).length < 2 ^ (prefixWord ++ tailWord_318281).sum := by decide
  have hdescent : baseEnd_318281 < baseStart_318281 := by decide
  rcases family_descends (prefixWord ++ tailWord_318281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318290 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_318290 : Nat := 118140960795 + 318290 * 2 ^ 59
def prefixEnd_318290 : Nat := 4983230072969 + 3 ^ 40 * 318290 * 2
def baseEnd_318290 : Nat := 163435757519664922611217

theorem tailTrace_318290 : CollatzResearch.WordTrace tailWord_318290 prefixEnd_318290 163435757519664922611217 := by
  unfold tailWord_318290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902247504224291112330081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7739326677931442966213549 2902247504224291112330081)
  ·
    refine ⟨2176685628168218334247561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2902247504224291112330081 2176685628168218334247561)
    ·
      refine ⟨1632514221126163750685671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176685628168218334247561 1632514221126163750685671)
      ·
        refine ⟨2448771331689245626028507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632514221126163750685671 2448771331689245626028507)
        ·
          refine ⟨3673156997533868439042761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448771331689245626028507 3673156997533868439042761)
          ·
            refine ⟨2754867748150401329282071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673156997533868439042761 2754867748150401329282071)
            ·
              refine ⟨4132301622225601993923107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754867748150401329282071 4132301622225601993923107)
              ·
                refine ⟨6198452433338402990884661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4132301622225601993923107 6198452433338402990884661)
                ·
                  refine ⟨581104915625475280395437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6198452433338402990884661 581104915625475280395437)
                  ·
                    refine ⟨217914343359553230148289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581104915625475280395437 217914343359553230148289)
                    ·
                      refine ⟨163435757519664922611217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217914343359553230148289 163435757519664922611217)
                      ·
                        rfl

theorem cell23_318290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_318290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318290 prefixEnd_318290 := by exact prefixLift 318290
  have htrace : WordTrace (prefixWord ++ tailWord_318290) baseStart_318290 baseEnd_318290 := by
    simpa [prefixWord, tailWord_318290, baseEnd_318290] using wordTrace_append hprefix tailTrace_318290
  have hstable : (prefixWord ++ tailWord_318290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318290).length < 2 ^ (prefixWord ++ tailWord_318290).sum := by decide
  have hdescent : baseEnd_318290 < baseStart_318290 := by decide
  rcases family_descends (prefixWord ++ tailWord_318290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318320 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2]
def baseStart_318320 : Nat := 118140960795 + 318320 * 2 ^ 59
def prefixEnd_318320 : Nat := 4983230072969 + 3 ^ 40 * 318320 * 2
def baseEnd_318320 : Nat := 163451161939299805236079

theorem tailTrace_318320 : CollatzResearch.WordTrace tailWord_318320 prefixEnd_318320 163451161939299805236079 := by
  unfold tailWord_318320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805042103394239786456207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7740056137858986381941609 5805042103394239786456207)
  ·
    refine ⟨8707563155091359679684311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805042103394239786456207 8707563155091359679684311)
    ·
      refine ⟨13061344732637039519526467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8707563155091359679684311 13061344732637039519526467)
      ·
        refine ⟨19592017098955559279289701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13061344732637039519526467 19592017098955559279289701)
        ·
          refine ⟨3673503206054167364866819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19592017098955559279289701 3673503206054167364866819)
          ·
            refine ⟨5510254809081251047300229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673503206054167364866819 5510254809081251047300229)
            ·
              refine ⟨1033172776702734571368793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5510254809081251047300229 1033172776702734571368793)
              ·
                refine ⟨774879582527050928526595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033172776702734571368793 774879582527050928526595)
                ·
                  refine ⟨1162319373790576392789893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774879582527050928526595 1162319373790576392789893)
                  ·
                    refine ⟨217934882585733073648105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162319373790576392789893 217934882585733073648105)
                    ·
                      refine ⟨163451161939299805236079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217934882585733073648105 163451161939299805236079)
                      ·
                        rfl

theorem cell23_318320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2].length) (baseStart_318320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318320 prefixEnd_318320 := by exact prefixLift 318320
  have htrace : WordTrace (prefixWord ++ tailWord_318320) baseStart_318320 baseEnd_318320 := by
    simpa [prefixWord, tailWord_318320, baseEnd_318320] using wordTrace_append hprefix tailTrace_318320
  have hstable : (prefixWord ++ tailWord_318320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318320).length < 2 ^ (prefixWord ++ tailWord_318320).sum := by decide
  have hdescent : baseEnd_318320 < baseStart_318320 := by decide
  rcases family_descends (prefixWord ++ tailWord_318320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318333 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_318333 : Nat := 118140960795 + 318333 * 2 ^ 59
def prefixEnd_318333 : Nat := 4983230072969 + 3 ^ 40 * 318333 * 2
def baseEnd_318333 : Nat := 163457837187808254373519

theorem tailTrace_318333 : CollatzResearch.WordTrace tailWord_318333 prefixEnd_318333 163457837187808254373519 := by
  unfold tailWord_318333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610558355741382793135653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7740372237160921862090435 11610558355741382793135653)
  ·
    refine ⟨2176979691701509273712935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11610558355741382793135653 2176979691701509273712935)
    ·
      refine ⟨3265469537552263910569403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176979691701509273712935 3265469537552263910569403)
      ·
        refine ⟨4898204306328395865854105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265469537552263910569403 4898204306328395865854105)
        ·
          refine ⟨3673653229746296899390579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4898204306328395865854105 3673653229746296899390579)
          ·
            refine ⟨5510479844619445349085869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673653229746296899390579 5510479844619445349085869)
            ·
              refine ⟨2066429941732292005907201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5510479844619445349085869 2066429941732292005907201)
              ·
                refine ⟨1549822456299219004430401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066429941732292005907201 1549822456299219004430401)
                ·
                  refine ⟨1162366842224414253322801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1549822456299219004430401 1162366842224414253322801)
                  ·
                    refine ⟨871775131668310689992101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1162366842224414253322801 871775131668310689992101)
                    ·
                      refine ⟨163457837187808254373519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 871775131668310689992101 163457837187808254373519)
                      ·
                        rfl

theorem cell23_318333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_318333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318333 prefixEnd_318333 := by exact prefixLift 318333
  have htrace : WordTrace (prefixWord ++ tailWord_318333) baseStart_318333 baseEnd_318333 := by
    simpa [prefixWord, tailWord_318333, baseEnd_318333] using wordTrace_append hprefix tailTrace_318333
  have hstable : (prefixWord ++ tailWord_318333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318333).length < 2 ^ (prefixWord ++ tailWord_318333).sum := by decide
  have hdescent : baseEnd_318333 < baseStart_318333 := by decide
  rcases family_descends (prefixWord ++ tailWord_318333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318336 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_318336 : Nat := 118140960795 + 318336 * 2 ^ 59
def prefixEnd_318336 : Nat := 4983230072969 + 3 ^ 40 * 318336 * 2
def baseEnd_318336 : Nat := 163459377629771742636005

theorem tailTrace_318336 : CollatzResearch.WordTrace tailWord_318336 prefixEnd_318336 163459377629771742636005 := by
  unfold tailWord_318336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805333887365257152747431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7740445183153676203663241 5805333887365257152747431)
  ·
    refine ⟨8708000831047885729121147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805333887365257152747431 8708000831047885729121147)
    ·
      refine ⟨13062001246571828593681721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8708000831047885729121147 13062001246571828593681721)
      ·
        refine ⟨9796500934928871445261291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13062001246571828593681721 9796500934928871445261291)
        ·
          refine ⟨14694751402393307167891937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9796500934928871445261291 14694751402393307167891937)
          ·
            refine ⟨11021063551794980375918953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14694751402393307167891937 11021063551794980375918953)
            ·
              refine ⟨8265797663846235281939215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11021063551794980375918953 8265797663846235281939215)
              ·
                refine ⟨12398696495769352922908823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265797663846235281939215 12398696495769352922908823)
                ·
                  refine ⟨18598044743654029384363235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12398696495769352922908823 18598044743654029384363235)
                  ·
                    refine ⟨27897067115481044076544853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18598044743654029384363235 27897067115481044076544853)
                    ·
                      refine ⟨163459377629771742636005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 27897067115481044076544853 163459377629771742636005)
                      ·
                        rfl

theorem cell23_318336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_318336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318336 prefixEnd_318336 := by exact prefixLift 318336
  have htrace : WordTrace (prefixWord ++ tailWord_318336) baseStart_318336 baseEnd_318336 := by
    simpa [prefixWord, tailWord_318336, baseEnd_318336] using wordTrace_append hprefix tailTrace_318336
  have hstable : (prefixWord ++ tailWord_318336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318336).length < 2 ^ (prefixWord ++ tailWord_318336).sum := by decide
  have hdescent : baseEnd_318336 < baseStart_318336 := by decide
  rcases family_descends (prefixWord ++ tailWord_318336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318343 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 7]
def baseStart_318343 : Nat := 118140960795 + 318343 * 2 ^ 59
def prefixEnd_318343 : Nat := 4983230072969 + 3 ^ 40 * 318343 * 2
def baseEnd_318343 : Nat := 18162552443817023916497

theorem tailTrace_318343 : CollatzResearch.WordTrace tailWord_318343 prefixEnd_318343 18162552443817023916497 := by
  unfold tailWord_318343
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610923085705154500999683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7740615390470103000666455 11610923085705154500999683)
  ·
    refine ⟨17416384628557731751499525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11610923085705154500999683 17416384628557731751499525)
    ·
      refine ⟨3265572117854574703406161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17416384628557731751499525 3265572117854574703406161)
      ·
        refine ⟨2449179088390931027554621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265572117854574703406161 2449179088390931027554621)
        ·
          refine ⟨918442158146599135332983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2449179088390931027554621 918442158146599135332983)
          ·
            refine ⟨1377663237219898702999475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918442158146599135332983 1377663237219898702999475)
            ·
              refine ⟨2066494855829848054499213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377663237219898702999475 2066494855829848054499213)
              ·
                refine ⟨774935570936193020437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066494855829848054499213 774935570936193020437205)
                ·
                  refine ⟨18162552443817023916497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 774935570936193020437205 18162552443817023916497)
                  ·
                    rfl

theorem cell23_318343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 7].length) (baseStart_318343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318343 prefixEnd_318343 := by exact prefixLift 318343
  have htrace : WordTrace (prefixWord ++ tailWord_318343) baseStart_318343 baseEnd_318343 := by
    simpa [prefixWord, tailWord_318343, baseEnd_318343] using wordTrace_append hprefix tailTrace_318343
  have hstable : (prefixWord ++ tailWord_318343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318343).length < 2 ^ (prefixWord ++ tailWord_318343).sum := by decide
  have hdescent : baseEnd_318343 < baseStart_318343 := by decide
  rcases family_descends (prefixWord ++ tailWord_318343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318358 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_318358 : Nat := 118140960795 + 318358 * 2 ^ 59
def prefixEnd_318358 : Nat := 4983230072969 + 3 ^ 40 * 318358 * 2
def baseEnd_318358 : Nat := 163470674204170656560905

theorem tailTrace_318358 : CollatzResearch.WordTrace tailWord_318358 prefixEnd_318358 163470674204170656560905 := by
  unfold tailWord_318358
  simp only [CollatzResearch.WordTrace]
  refine ⟨725716886290675753924733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7740980120433874708530485 725716886290675753924733)
  ·
    refine ⟨272143832359003407721775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 725716886290675753924733 272143832359003407721775)
    ·
      refine ⟨408215748538505111582663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272143832359003407721775 408215748538505111582663)
      ·
        refine ⟨612323622807757667373995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408215748538505111582663 612323622807757667373995)
        ·
          refine ⟨918485434211636501060993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612323622807757667373995 918485434211636501060993)
          ·
            refine ⟨688864075658727375795745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918485434211636501060993 688864075658727375795745)
            ·
              refine ⟨516648056744045531846809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688864075658727375795745 516648056744045531846809)
              ·
                refine ⟨387486042558034148885107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516648056744045531846809 387486042558034148885107)
                ·
                  refine ⟨581229063837051223327661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387486042558034148885107 581229063837051223327661)
                  ·
                    refine ⟨217960898938894208747873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581229063837051223327661 217960898938894208747873)
                    ·
                      refine ⟨163470674204170656560905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217960898938894208747873 163470674204170656560905)
                      ·
                        rfl

theorem cell23_318358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_318358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318358 prefixEnd_318358 := by exact prefixLift 318358
  have htrace : WordTrace (prefixWord ++ tailWord_318358) baseStart_318358 baseEnd_318358 := by
    simpa [prefixWord, tailWord_318358, baseEnd_318358] using wordTrace_append hprefix tailTrace_318358
  have hstable : (prefixWord ++ tailWord_318358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318358).length < 2 ^ (prefixWord ++ tailWord_318358).sum := by decide
  have hdescent : baseEnd_318358 < baseStart_318358 := by decide
  rcases family_descends (prefixWord ++ tailWord_318358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318410 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_318410 : Nat := 118140960795 + 318410 * 2 ^ 59
def prefixEnd_318410 : Nat := 4983230072969 + 3 ^ 40 * 318410 * 2
def baseEnd_318410 : Nat := 163497375198204453110665

theorem tailTrace_318410 : CollatzResearch.WordTrace tailWord_318410 prefixEnd_318410 163497375198204453110665 := by
  unfold tailWord_318410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903341694115606235922171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7742244517641616629125789 2903341694115606235922171)
  ·
    refine ⟨4355012541173409353883257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903341694115606235922171 4355012541173409353883257)
    ·
      refine ⟨3266259405880057015412443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355012541173409353883257 3266259405880057015412443)
      ·
        refine ⟨4899389108820085523118665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266259405880057015412443 4899389108820085523118665)
        ·
          refine ⟨3674541831615064142338999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899389108820085523118665 3674541831615064142338999)
          ·
            refine ⟨5511812747422596213508499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674541831615064142338999 5511812747422596213508499)
            ·
              refine ⟨8267719121133894320262749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511812747422596213508499 8267719121133894320262749)
              ·
                refine ⟨3100394670425210370098531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8267719121133894320262749 3100394670425210370098531)
                ·
                  refine ⟨4650592005637815555147797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100394670425210370098531 4650592005637815555147797)
                  ·
                    refine ⟨217996500264272604147553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4650592005637815555147797 217996500264272604147553)
                    ·
                      refine ⟨163497375198204453110665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 217996500264272604147553 163497375198204453110665)
                      ·
                        rfl

theorem cell23_318410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_318410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318410 prefixEnd_318410 := by exact prefixLift 318410
  have htrace : WordTrace (prefixWord ++ tailWord_318410) baseStart_318410 baseEnd_318410 := by
    simpa [prefixWord, tailWord_318410, baseEnd_318410] using wordTrace_append hprefix tailTrace_318410
  have hstable : (prefixWord ++ tailWord_318410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318410).length < 2 ^ (prefixWord ++ tailWord_318410).sum := by decide
  have hdescent : baseEnd_318410 < baseStart_318410 := by decide
  rcases family_descends (prefixWord ++ tailWord_318410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318497 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_318497 : Nat := 118140960795 + 318497 * 2 ^ 59
def prefixEnd_318497 : Nat := 4983230072969 + 3 ^ 40 * 318497 * 2
def baseEnd_318497 : Nat := 54514016005048537574255

theorem tailTrace_318497 : CollatzResearch.WordTrace tailWord_318497 prefixEnd_318497 54514016005048537574255 := by
  unfold tailWord_318497
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616539927147238802105745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7744359951431492534737163 11616539927147238802105745)
  ·
    refine ⟨8712404945360429101579309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11616539927147238802105745 8712404945360429101579309)
    ·
      refine ⟨3267151854510160913092241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8712404945360429101579309 3267151854510160913092241)
      ·
        refine ⟨2450363890882620684819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267151854510160913092241 2450363890882620684819181)
        ·
          refine ⟨918886459080982756807193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2450363890882620684819181 918886459080982756807193)
          ·
            refine ⟨689164844310737067605395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918886459080982756807193 689164844310737067605395)
            ·
              refine ⟨1033747266466105601408093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689164844310737067605395 1033747266466105601408093)
              ·
                refine ⟨387655224924789600528035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033747266466105601408093 387655224924789600528035)
                ·
                  refine ⟨581482837387184400792053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387655224924789600528035 581482837387184400792053)
                  ·
                    refine ⟨54514016005048537574255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 581482837387184400792053 54514016005048537574255)
                    ·
                      rfl

theorem cell23_318497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_318497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318497 prefixEnd_318497 := by exact prefixLift 318497
  have htrace : WordTrace (prefixWord ++ tailWord_318497) baseStart_318497 baseEnd_318497 := by
    simpa [prefixWord, tailWord_318497, baseEnd_318497] using wordTrace_append hprefix tailTrace_318497
  have hstable : (prefixWord ++ tailWord_318497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318497).length < 2 ^ (prefixWord ++ tailWord_318497).sum := by decide
  have hdescent : baseEnd_318497 < baseStart_318497 := by decide
  rcases family_descends (prefixWord ++ tailWord_318497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318520 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_318520 : Nat := 118140960795 + 318520 * 2 ^ 59
def prefixEnd_318520 : Nat := 4983230072969 + 3 ^ 40 * 318520 * 2
def baseEnd_318520 : Nat := 163553858070199022735159

theorem tailTrace_318520 : CollatzResearch.WordTrace tailWord_318520 prefixEnd_318520 163553858070199022735159 := by
  unfold tailWord_318520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808689403031956865096507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7744919204042609153462009 5808689403031956865096507)
  ·
    refine ⟨8713034104547935297644761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808689403031956865096507 8713034104547935297644761)
    ·
      refine ⟨6534775578410951473233571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8713034104547935297644761 6534775578410951473233571)
      ·
        refine ⟨9802163367616427209850357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534775578410951473233571 9802163367616427209850357)
        ·
          refine ⟨918952815714040050923471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9802163367616427209850357 918952815714040050923471)
          ·
            refine ⟨1378429223571060076385207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918952815714040050923471 1378429223571060076385207)
            ·
              refine ⟨2067643835356590114577811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378429223571060076385207 2067643835356590114577811)
              ·
                refine ⟨3101465753034885171866717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067643835356590114577811 3101465753034885171866717)
                ·
                  refine ⟨1163049657388081939450019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3101465753034885171866717 1163049657388081939450019)
                  ·
                    refine ⟨1744574486082122909175029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163049657388081939450019 1744574486082122909175029)
                    ·
                      refine ⟨163553858070199022735159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1744574486082122909175029 163553858070199022735159)
                      ·
                        rfl

theorem cell23_318520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_318520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318520 prefixEnd_318520 := by exact prefixLift 318520
  have htrace : WordTrace (prefixWord ++ tailWord_318520) baseStart_318520 baseEnd_318520 := by
    simpa [prefixWord, tailWord_318520, baseEnd_318520] using wordTrace_append hprefix tailTrace_318520
  have hstable : (prefixWord ++ tailWord_318520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318520).length < 2 ^ (prefixWord ++ tailWord_318520).sum := by decide
  have hdescent : baseEnd_318520 < baseStart_318520 := by decide
  rcases family_descends (prefixWord ++ tailWord_318520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318634 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_318634 : Nat := 118140960795 + 318634 * 2 ^ 59
def prefixEnd_318634 : Nat := 4983230072969 + 3 ^ 40 * 318634 * 2
def baseEnd_318634 : Nat := 54537464954937192236545

theorem tailTrace_318634 : CollatzResearch.WordTrace tailWord_318634 prefixEnd_318634 54537464954937192236545 := by
  unfold tailWord_318634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905384181912727799960739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7747691151767274133228637 2905384181912727799960739)
  ·
    refine ⟨4358076272869091699941109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2905384181912727799960739 4358076272869091699941109)
    ·
      refine ⟨408569650581477346869479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4358076272869091699941109 408569650581477346869479)
      ·
        refine ⟨612854475872216020304219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408569650581477346869479 612854475872216020304219)
        ·
          refine ⟨919281713808324030456329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612854475872216020304219 919281713808324030456329)
          ·
            refine ⟨689461285356243022842247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919281713808324030456329 689461285356243022842247)
            ·
              refine ⟨1034191928034364534263371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689461285356243022842247 1034191928034364534263371)
              ·
                refine ⟨1551287892051546801395057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034191928034364534263371 1551287892051546801395057)
                ·
                  refine ⟨1163465919038660101046293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551287892051546801395057 1163465919038660101046293)
                  ·
                    refine ⟨54537464954937192236545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1163465919038660101046293 54537464954937192236545)
                    ·
                      rfl

theorem cell23_318634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_318634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318634 prefixEnd_318634 := by exact prefixLift 318634
  have htrace : WordTrace (prefixWord ++ tailWord_318634) baseStart_318634 baseEnd_318634 := by
    simpa [prefixWord, tailWord_318634, baseEnd_318634] using wordTrace_append hprefix tailTrace_318634
  have hstable : (prefixWord ++ tailWord_318634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318634).length < 2 ^ (prefixWord ++ tailWord_318634).sum := by decide
  have hdescent : baseEnd_318634 < baseStart_318634 := by decide
  rcases family_descends (prefixWord ++ tailWord_318634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318641 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 1, 4, 2]
def baseStart_318641 : Nat := 118140960795 + 318641 * 2 ^ 59
def prefixEnd_318641 : Nat := 4983230072969 + 3 ^ 40 * 318641 * 2
def baseEnd_318641 : Nat := 163615989229393049322103

theorem tailTrace_318641 : CollatzResearch.WordTrace tailWord_318641 prefixEnd_318641 163615989229393049322103 := by
  unfold tailWord_318641
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621792038625551395347777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7747861359083700930231851 11621792038625551395347777)
  ·
    refine ⟨8716344028969163546510833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11621792038625551395347777 8716344028969163546510833)
    ·
      refine ⟨6537258021726872659883125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8716344028969163546510833 6537258021726872659883125)
      ·
        refine ⟨612867939536894311864043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6537258021726872659883125 612867939536894311864043)
        ·
          refine ⟨919301909305341467796065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612867939536894311864043 919301909305341467796065)
          ·
            refine ⟨689476431979006100847049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919301909305341467796065 689476431979006100847049)
            ·
              refine ⟨517107323984254575635287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689476431979006100847049 517107323984254575635287)
              ·
                refine ⟨775660985976381863452931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517107323984254575635287 775660985976381863452931)
                ·
                  refine ⟨1163491478964572795179397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775660985976381863452931 1163491478964572795179397)
                  ·
                    refine ⟨218154652305857399096137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163491478964572795179397 218154652305857399096137)
                    ·
                      refine ⟨163615989229393049322103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218154652305857399096137 163615989229393049322103)
                      ·
                        rfl

theorem cell23_318641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_318641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318641 prefixEnd_318641 := by exact prefixLift 318641
  have htrace : WordTrace (prefixWord ++ tailWord_318641) baseStart_318641 baseEnd_318641 := by
    simpa [prefixWord, tailWord_318641, baseEnd_318641] using wordTrace_append hprefix tailTrace_318641
  have hstable : (prefixWord ++ tailWord_318641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318641).length < 2 ^ (prefixWord ++ tailWord_318641).sum := by decide
  have hdescent : baseEnd_318641 < baseStart_318641 := by decide
  rcases family_descends (prefixWord ++ tailWord_318641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318662 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_318662 : Nat := 118140960795 + 318662 * 2 ^ 59
def prefixEnd_318662 : Nat := 4983230072969 + 3 ^ 40 * 318662 * 2
def baseEnd_318662 : Nat := 163626772323137467159507

theorem tailTrace_318662 : CollatzResearch.WordTrace tailWord_318662 prefixEnd_318662 163626772323137467159507 := by
  unfold tailWord_318662
  simp only [CollatzResearch.WordTrace]
  refine ⟨363204936610920999433195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7748371981032981321241493 363204936610920999433195)
  ·
    refine ⟨544807404916381499149793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363204936610920999433195 544807404916381499149793)
    ·
      refine ⟨408605553687286124362345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 544807404916381499149793 408605553687286124362345)
      ·
        refine ⟨306454165265464593271759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408605553687286124362345 306454165265464593271759)
        ·
          refine ⟨459681247898196889907639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306454165265464593271759 459681247898196889907639)
          ·
            refine ⟨689521871847295334861459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459681247898196889907639 689521871847295334861459)
            ·
              refine ⟨1034282807770943002292189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689521871847295334861459 1034282807770943002292189)
              ·
                refine ⟨387856052914103625859571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034282807770943002292189 387856052914103625859571)
                ·
                  refine ⟨581784079371155438789357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387856052914103625859571 581784079371155438789357)
                  ·
                    refine ⟨218169029764183289546009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 581784079371155438789357 218169029764183289546009)
                    ·
                      refine ⟨163626772323137467159507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218169029764183289546009 163626772323137467159507)
                      ·
                        rfl

theorem cell23_318662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_318662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318662 prefixEnd_318662 := by exact prefixLift 318662
  have htrace : WordTrace (prefixWord ++ tailWord_318662) baseStart_318662 baseEnd_318662 := by
    simpa [prefixWord, tailWord_318662, baseEnd_318662] using wordTrace_append hprefix tailTrace_318662
  have hstable : (prefixWord ++ tailWord_318662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318662).length < 2 ^ (prefixWord ++ tailWord_318662).sum := by decide
  have hdescent : baseEnd_318662 < baseStart_318662 := by decide
  rcases family_descends (prefixWord ++ tailWord_318662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318667 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 7, 2]
def baseStart_318667 : Nat := 118140960795 + 318667 * 2 ^ 59
def prefixEnd_318667 : Nat := 4983230072969 + 3 ^ 40 * 318667 * 2
def baseEnd_318667 : Nat := 163629339726409947596983

theorem tailTrace_318667 : CollatzResearch.WordTrace tailWord_318667 prefixEnd_318667 163629339726409947596983 := by
  unfold tailWord_318667
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622740336531357835794255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7748493557687571890529503 11622740336531357835794255)
  ·
    refine ⟨17434110504797036753691383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11622740336531357835794255 17434110504797036753691383)
    ·
      refine ⟨26151165757195555130537075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434110504797036753691383 26151165757195555130537075)
      ·
        refine ⟨39226748635793332695805613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26151165757195555130537075 39226748635793332695805613)
        ·
          refine ⟨14710030738422499760927105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39226748635793332695805613 14710030738422499760927105)
          ·
            refine ⟨11032523053816874820695329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14710030738422499760927105 11032523053816874820695329)
            ·
              refine ⟨8274392290362656115521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11032523053816874820695329 8274392290362656115521497)
              ·
                refine ⟨6205794217771992086641123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8274392290362656115521497 6205794217771992086641123)
                ·
                  refine ⟨9308691326657988129961685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205794217771992086641123 9308691326657988129961685)
                  ·
                    refine ⟨218172452968546596795977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9308691326657988129961685 218172452968546596795977)
                    ·
                      refine ⟨163629339726409947596983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218172452968546596795977 163629339726409947596983)
                      ·
                        rfl

theorem cell23_318667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7, 2].length) (baseStart_318667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318667 prefixEnd_318667 := by exact prefixLift 318667
  have htrace : WordTrace (prefixWord ++ tailWord_318667) baseStart_318667 baseEnd_318667 := by
    simpa [prefixWord, tailWord_318667, baseEnd_318667] using wordTrace_append hprefix tailTrace_318667
  have hstable : (prefixWord ++ tailWord_318667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318667).length < 2 ^ (prefixWord ++ tailWord_318667).sum := by decide
  have hdescent : baseEnd_318667 < baseStart_318667 := by decide
  rcases family_descends (prefixWord ++ tailWord_318667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318734 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_318734 : Nat := 118140960795 + 318734 * 2 ^ 59
def prefixEnd_318734 : Nat := 4983230072969 + 3 ^ 40 * 318734 * 2
def baseEnd_318734 : Nat := 163663742930261185459175

theorem tailTrace_318734 : CollatzResearch.WordTrace tailWord_318734 prefixEnd_318734 163663742930261185459175 := by
  unfold tailWord_318734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453148003411078534810407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7750122684859085518988837 1453148003411078534810407)
  ·
    refine ⟨2179722005116617802215611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453148003411078534810407 2179722005116617802215611)
    ·
      refine ⟨3269583007674926703323417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179722005116617802215611 3269583007674926703323417)
      ·
        refine ⟨2452187255756195027492563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269583007674926703323417 2452187255756195027492563)
        ·
          refine ⟨3678280883634292541238845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452187255756195027492563 3678280883634292541238845)
          ·
            refine ⟨1379355331362859702964567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678280883634292541238845 1379355331362859702964567)
            ·
              refine ⟨2069032997044289554446851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379355331362859702964567 2069032997044289554446851)
              ·
                refine ⟨3103549495566434331670277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069032997044289554446851 3103549495566434331670277)
                ·
                  refine ⟨581915530418706437188177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3103549495566434331670277 581915530418706437188177)
                  ·
                    refine ⟨436436647814029827891133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581915530418706437188177 436436647814029827891133)
                    ·
                      refine ⟨163663742930261185459175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 436436647814029827891133 163663742930261185459175)
                      ·
                        rfl

theorem cell23_318734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_318734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318734 prefixEnd_318734 := by exact prefixLift 318734
  have htrace : WordTrace (prefixWord ++ tailWord_318734) baseStart_318734 baseEnd_318734 := by
    simpa [prefixWord, tailWord_318734, baseEnd_318734] using wordTrace_append hprefix tailTrace_318734
  have hstable : (prefixWord ++ tailWord_318734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318734).length < 2 ^ (prefixWord ++ tailWord_318734).sum := by decide
  have hdescent : baseEnd_318734 < baseStart_318734 := by decide
  rcases family_descends (prefixWord ++ tailWord_318734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318737 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 6]
def baseStart_318737 : Nat := 118140960795 + 318737 * 2 ^ 59
def prefixEnd_318737 : Nat := 4983230072969 + 3 ^ 40 * 318737 * 2
def baseEnd_318737 : Nat := 18185031485802741524629

theorem tailTrace_318737 : CollatzResearch.WordTrace tailWord_318737 prefixEnd_318737 18185031485802741524629 := by
  unfold tailWord_318737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625293446277759790842465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7750195630851839860561643 11625293446277759790842465)
  ·
    refine ⟨8718970084708319843131849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11625293446277759790842465 8718970084708319843131849)
    ·
      refine ⟨6539227563531239882348887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8718970084708319843131849 6539227563531239882348887)
      ·
        refine ⟨9808841345296859823523331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539227563531239882348887 9808841345296859823523331)
        ·
          refine ⟨14713262017945289735284997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808841345296859823523331 14713262017945289735284997)
          ·
            refine ⟨2758736628364741825365937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14713262017945289735284997 2758736628364741825365937)
            ·
              refine ⟨2069052471273556369024453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758736628364741825365937 2069052471273556369024453)
              ·
                refine ⟨387947338363791819192085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2069052471273556369024453 387947338363791819192085)
                ·
                  refine ⟨18185031485802741524629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 387947338363791819192085 18185031485802741524629)
                  ·
                    rfl

theorem cell23_318737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_318737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318737 prefixEnd_318737 := by exact prefixLift 318737
  have htrace : WordTrace (prefixWord ++ tailWord_318737) baseStart_318737 baseEnd_318737 := by
    simpa [prefixWord, tailWord_318737, baseEnd_318737] using wordTrace_append hprefix tailTrace_318737
  have hstable : (prefixWord ++ tailWord_318737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318737).length < 2 ^ (prefixWord ++ tailWord_318737).sum := by decide
  have hdescent : baseEnd_318737 < baseStart_318737 := by decide
  rcases family_descends (prefixWord ++ tailWord_318737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318764 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_318764 : Nat := 118140960795 + 318764 * 2 ^ 59
def prefixEnd_318764 : Nat := 4983230072969 + 3 ^ 40 * 318764 * 2
def baseEnd_318764 : Nat := 163679147349896068084037

theorem tailTrace_318764 : CollatzResearch.WordTrace tailWord_318764 prefixEnd_318764 163679147349896068084037 := by
  unfold tailWord_318764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813139108589971701037673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7750852144786628934716897 5813139108589971701037673)
  ·
    refine ⟨4359854331442478775778255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5813139108589971701037673 4359854331442478775778255)
    ·
      refine ⟨6539781497163718163667383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359854331442478775778255 6539781497163718163667383)
      ·
        refine ⟨9809672245745577245501075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539781497163718163667383 9809672245745577245501075)
        ·
          refine ⟨14714508368618365868251613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809672245745577245501075 14714508368618365868251613)
          ·
            refine ⟨5517940638231887200594355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14714508368618365868251613 5517940638231887200594355)
            ·
              refine ⟨8276910957347830800891533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517940638231887200594355 8276910957347830800891533)
              ·
                refine ⟨3103841609005436550334325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8276910957347830800891533 3103841609005436550334325)
                ·
                  refine ⟨290985150844259676593843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3103841609005436550334325 290985150844259676593843)
                  ·
                    refine ⟨436477726266389514890765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290985150844259676593843 436477726266389514890765)
                    ·
                      refine ⟨163679147349896068084037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 436477726266389514890765 163679147349896068084037)
                      ·
                        rfl

theorem cell23_318764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_318764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318764 prefixEnd_318764 := by exact prefixLift 318764
  have htrace : WordTrace (prefixWord ++ tailWord_318764) baseStart_318764 baseEnd_318764 := by
    simpa [prefixWord, tailWord_318764, baseEnd_318764] using wordTrace_append hprefix tailTrace_318764
  have hstable : (prefixWord ++ tailWord_318764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318764).length < 2 ^ (prefixWord ++ tailWord_318764).sum := by decide
  have hdescent : baseEnd_318764 < baseStart_318764 := by decide
  rcases family_descends (prefixWord ++ tailWord_318764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318791 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_318791 : Nat := 118140960795 + 318791 * 2 ^ 59
def prefixEnd_318791 : Nat := 4983230072969 + 3 ^ 40 * 318791 * 2
def baseEnd_318791 : Nat := 163693011327567462446413

theorem tailTrace_318791 : CollatzResearch.WordTrace tailWord_318791 prefixEnd_318791 163693011327567462446413 := by
  unfold tailWord_318791
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627262988082127013308227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7751508658721418008872151 11627262988082127013308227)
  ·
    refine ⟨17440894482123190519962341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11627262988082127013308227 17440894482123190519962341)
    ·
      refine ⟨3270167715398098222492939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17440894482123190519962341 3270167715398098222492939)
      ·
        refine ⟨4905251573097147333739409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270167715398098222492939 4905251573097147333739409)
        ·
          refine ⟨3678938679822860500304557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4905251573097147333739409 3678938679822860500304557)
          ·
            refine ⟨1379602004933572687614209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678938679822860500304557 1379602004933572687614209)
            ·
              refine ⟨1034701503700179515710657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379602004933572687614209 1034701503700179515710657)
              ·
                refine ⟨776026127775134636782993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034701503700179515710657 776026127775134636782993)
                ·
                  refine ⟨582019595831350977587245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 776026127775134636782993 582019595831350977587245)
                  ·
                    refine ⟨218257348436756616595217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582019595831350977587245 218257348436756616595217)
                    ·
                      refine ⟨163693011327567462446413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218257348436756616595217 163693011327567462446413)
                      ·
                        rfl

theorem cell23_318791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_318791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318791 prefixEnd_318791 := by exact prefixLift 318791
  have htrace : WordTrace (prefixWord ++ tailWord_318791) baseStart_318791 baseEnd_318791 := by
    simpa [prefixWord, tailWord_318791, baseEnd_318791] using wordTrace_append hprefix tailTrace_318791
  have hstable : (prefixWord ++ tailWord_318791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318791).length < 2 ^ (prefixWord ++ tailWord_318791).sum := by decide
  have hdescent : baseEnd_318791 < baseStart_318791 := by decide
  rcases family_descends (prefixWord ++ tailWord_318791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318798 : List Nat := [4, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_318798 : Nat := 118140960795 + 318798 * 2 ^ 59
def prefixEnd_318798 : Nat := 4983230072969 + 3 ^ 40 * 318798 * 2
def baseEnd_318798 : Nat := 163696605692148935058881

theorem tailTrace_318798 : CollatzResearch.WordTrace tailWord_318798 prefixEnd_318798 163696605692148935058881 := by
  unfold tailWord_318798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453439787382095901101631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7751678866037844805875365 1453439787382095901101631)
  ·
    refine ⟨2180159681073143851652447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453439787382095901101631 2180159681073143851652447)
    ·
      refine ⟨3270239521609715777478671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180159681073143851652447 3270239521609715777478671)
      ·
        refine ⟨4905359282414573666218007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270239521609715777478671 4905359282414573666218007)
        ·
          refine ⟨7358038923621860499327011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905359282414573666218007 7358038923621860499327011)
          ·
            refine ⟨11037058385432790748990517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358038923621860499327011 11037058385432790748990517)
            ·
              refine ⟨1034724223634324132717861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11037058385432790748990517 1034724223634324132717861)
              ·
                refine ⟨194010791931435774884599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1034724223634324132717861 194010791931435774884599)
                ·
                  refine ⟨291016187897153662326899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194010791931435774884599 291016187897153662326899)
                  ·
                    refine ⟨436524281845730493490349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291016187897153662326899 436524281845730493490349)
                    ·
                      refine ⟨163696605692148935058881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 436524281845730493490349 163696605692148935058881)
                      ·
                        rfl

theorem cell23_318798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_318798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318798 prefixEnd_318798 := by exact prefixLift 318798
  have htrace : WordTrace (prefixWord ++ tailWord_318798) baseStart_318798 baseEnd_318798 := by
    simpa [prefixWord, tailWord_318798, baseEnd_318798] using wordTrace_append hprefix tailTrace_318798
  have hstable : (prefixWord ++ tailWord_318798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318798).length < 2 ^ (prefixWord ++ tailWord_318798).sum := by decide
  have hdescent : baseEnd_318798 < baseStart_318798 := by decide
  rcases family_descends (prefixWord ++ tailWord_318798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318804 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_318804 : Nat := 118140960795 + 318804 * 2 ^ 59
def prefixEnd_318804 : Nat := 4983230072969 + 3 ^ 40 * 318804 * 2
def baseEnd_318804 : Nat := 163699686576075911583853

theorem tailTrace_318804 : CollatzResearch.WordTrace tailWord_318804 prefixEnd_318804 163699686576075911583853 := by
  unfold tailWord_318804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813868568517515116765733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7751824758023353489020977 5813868568517515116765733)
  ·
    refine ⟨1090100356597034084393575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5813868568517515116765733 1090100356597034084393575)
    ·
      refine ⟨1635150534895551126590363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090100356597034084393575 1635150534895551126590363)
      ·
        refine ⟨2452725802343326689885545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635150534895551126590363 2452725802343326689885545)
        ·
          refine ⟨1839544351757495017414159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2452725802343326689885545 1839544351757495017414159)
          ·
            refine ⟨2759316527636242526121239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839544351757495017414159 2759316527636242526121239)
            ·
              refine ⟨4138974791454363789181859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2759316527636242526121239 4138974791454363789181859)
              ·
                refine ⟨6208462187181545683772789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138974791454363789181859 6208462187181545683772789)
                ·
                  refine ⟨582043330048269907853699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6208462187181545683772789 582043330048269907853699)
                  ·
                    refine ⟨873064995072404861780549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 582043330048269907853699 873064995072404861780549)
                    ·
                      refine ⟨163699686576075911583853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 873064995072404861780549 163699686576075911583853)
                      ·
                        rfl

theorem cell23_318804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_318804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318804 prefixEnd_318804 := by exact prefixLift 318804
  have htrace : WordTrace (prefixWord ++ tailWord_318804) baseStart_318804 baseEnd_318804 := by
    simpa [prefixWord, tailWord_318804, baseEnd_318804] using wordTrace_append hprefix tailTrace_318804
  have hstable : (prefixWord ++ tailWord_318804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318804).length < 2 ^ (prefixWord ++ tailWord_318804).sum := by decide
  have hdescent : baseEnd_318804 < baseStart_318804 := by decide
  rcases family_descends (prefixWord ++ tailWord_318804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318817 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_318817 : Nat := 118140960795 + 318817 * 2 ^ 59
def prefixEnd_318817 : Nat := 4983230072969 + 3 ^ 40 * 318817 * 2
def baseEnd_318817 : Nat := 163706361824584360721293

theorem tailTrace_318817 : CollatzResearch.WordTrace tailWord_318817 prefixEnd_318817 163706361824584360721293 := by
  unfold tailWord_318817
  simp only [CollatzResearch.WordTrace]
  refine ⟨11628211285987933453754705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7752140857325288969169803 11628211285987933453754705)
  ·
    refine ⟨8721158464490950090316029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11628211285987933453754705 8721158464490950090316029)
    ·
      refine ⟨3270434424184106283868511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8721158464490950090316029 3270434424184106283868511)
      ·
        refine ⟨4905651636276159425802767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270434424184106283868511 4905651636276159425802767)
        ·
          refine ⟨7358477454414239138704151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905651636276159425802767 7358477454414239138704151)
          ·
            refine ⟨11037716181621358708056227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358477454414239138704151 11037716181621358708056227)
            ·
              refine ⟨16556574272432038062084341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037716181621358708056227 16556574272432038062084341)
              ·
                refine ⟨1552178838040503568320407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16556574272432038062084341 1552178838040503568320407)
                ·
                  refine ⟨2328268257060755352480611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552178838040503568320407 2328268257060755352480611)
                  ·
                    refine ⟨3492402385591133028720917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328268257060755352480611 3492402385591133028720917)
                    ·
                      refine ⟨163706361824584360721293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3492402385591133028720917 163706361824584360721293)
                      ·
                        rfl

theorem cell23_318817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_318817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318817 prefixEnd_318817 := by exact prefixLift 318817
  have htrace : WordTrace (prefixWord ++ tailWord_318817) baseStart_318817 baseEnd_318817 := by
    simpa [prefixWord, tailWord_318817, baseEnd_318817] using wordTrace_append hprefix tailTrace_318817
  have hstable : (prefixWord ++ tailWord_318817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318817).length < 2 ^ (prefixWord ++ tailWord_318817).sum := by decide
  have hdescent : baseEnd_318817 < baseStart_318817 := by decide
  rcases family_descends (prefixWord ++ tailWord_318817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318834 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_318834 : Nat := 118140960795 + 318834 * 2 ^ 59
def prefixEnd_318834 : Nat := 4983230072969 + 3 ^ 40 * 318834 * 2
def baseEnd_318834 : Nat := 163715090995710794208715

theorem tailTrace_318834 : CollatzResearch.WordTrace tailWord_318834 prefixEnd_318834 163715090995710794208715 := by
  unfold tailWord_318834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907207831731586339280889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7752554217950896904749037 2907207831731586339280889)
  ·
    refine ⟨2180405873798689754460667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907207831731586339280889 2180405873798689754460667)
    ·
      refine ⟨3270608810698034631691001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180405873798689754460667 3270608810698034631691001)
      ·
        refine ⟨2452956608023525973768251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3270608810698034631691001 2452956608023525973768251)
        ·
          refine ⟨3679434912035288960652377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452956608023525973768251 3679434912035288960652377)
          ·
            refine ⟨2759576184026466720489283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3679434912035288960652377 2759576184026466720489283)
            ·
              refine ⟨4139364276039700080733925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2759576184026466720489283 4139364276039700080733925)
              ·
                refine ⟨776130801757443765137611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4139364276039700080733925 776130801757443765137611)
                ·
                  refine ⟨1164196202636165647706417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776130801757443765137611 1164196202636165647706417)
                  ·
                    refine ⟨873147151977124235779813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1164196202636165647706417 873147151977124235779813)
                    ·
                      refine ⟨163715090995710794208715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 873147151977124235779813 163715090995710794208715)
                      ·
                        rfl

theorem cell23_318834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_318834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318834 prefixEnd_318834 := by exact prefixLift 318834
  have htrace : WordTrace (prefixWord ++ tailWord_318834) baseStart_318834 baseEnd_318834 := by
    simpa [prefixWord, tailWord_318834, baseEnd_318834] using wordTrace_append hprefix tailTrace_318834
  have hstable : (prefixWord ++ tailWord_318834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318834).length < 2 ^ (prefixWord ++ tailWord_318834).sum := by decide
  have hdescent : baseEnd_318834 < baseStart_318834 := by decide
  rcases family_descends (prefixWord ++ tailWord_318834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318855 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_318855 : Nat := 118140960795 + 318855 * 2 ^ 59
def prefixEnd_318855 : Nat := 4983230072969 + 3 ^ 40 * 318855 * 2
def baseEnd_318855 : Nat := 163725874089455212046119

theorem tailTrace_318855 : CollatzResearch.WordTrace tailWord_318855 prefixEnd_318855 163725874089455212046119 := by
  unfold tailWord_318855
  simp only [CollatzResearch.WordTrace]
  refine ⟨11629597259850265943638019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7753064839900177295758679 11629597259850265943638019)
  ·
    refine ⟨17444395889775398915457029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11629597259850265943638019 17444395889775398915457029)
    ·
      refine ⟨3270824229332887296648193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17444395889775398915457029 3270824229332887296648193)
      ·
        refine ⟨2453118171999665472486145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3270824229332887296648193 2453118171999665472486145)
        ·
          refine ⟨1839838628999749104364609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453118171999665472486145 1839838628999749104364609)
          ·
            refine ⟨1379878971749811828273457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839838628999749104364609 1379878971749811828273457)
            ·
              refine ⟨1034909228812358871205093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379878971749811828273457 1034909228812358871205093)
              ·
                refine ⟨194045480402317288350955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1034909228812358871205093 194045480402317288350955)
                ·
                  refine ⟨291068220603475932526433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194045480402317288350955 291068220603475932526433)
                  ·
                    refine ⟨218301165452606949394825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291068220603475932526433 218301165452606949394825)
                    ·
                      refine ⟨163725874089455212046119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218301165452606949394825 163725874089455212046119)
                      ·
                        rfl

theorem cell23_318855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_318855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318855 prefixEnd_318855 := by exact prefixLift 318855
  have htrace : WordTrace (prefixWord ++ tailWord_318855) baseStart_318855 baseEnd_318855 := by
    simpa [prefixWord, tailWord_318855, baseEnd_318855] using wordTrace_append hprefix tailTrace_318855
  have hstable : (prefixWord ++ tailWord_318855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318855).length < 2 ^ (prefixWord ++ tailWord_318855).sum := by decide
  have hdescent : baseEnd_318855 < baseStart_318855 := by decide
  rcases family_descends (prefixWord ++ tailWord_318855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_318867 : Nat := 118140960795 + 318867 * 2 ^ 59
def prefixEnd_318867 : Nat := 4983230072969 + 3 ^ 40 * 318867 * 2
def baseEnd_318867 : Nat := 163732035857309165096063

theorem tailTrace_318867 : CollatzResearch.WordTrace tailWord_318867 prefixEnd_318867 163732035857309165096063 := by
  unfold tailWord_318867
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630034935806791993074855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7753356623871194662049903 11630034935806791993074855)
  ·
    refine ⟨17445052403710187989612283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11630034935806791993074855 17445052403710187989612283)
    ·
      refine ⟨26167578605565281984418425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445052403710187989612283 26167578605565281984418425)
      ·
        refine ⟨19625683954173961488313819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26167578605565281984418425 19625683954173961488313819)
        ·
          refine ⟨29438525931260942232470729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625683954173961488313819 29438525931260942232470729)
          ·
            refine ⟨22078894448445706674353047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29438525931260942232470729 22078894448445706674353047)
            ·
              refine ⟨33118341672668560011529571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22078894448445706674353047 33118341672668560011529571)
              ·
                refine ⟨49677512509002840017294357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33118341672668560011529571 49677512509002840017294357)
                ·
                  refine ⟨2328633398859508125810673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49677512509002840017294357 2328633398859508125810673)
                  ·
                    refine ⟨1746475049144631094358005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328633398859508125810673 1746475049144631094358005)
                    ·
                      refine ⟨163732035857309165096063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1746475049144631094358005 163732035857309165096063)
                      ·
                        rfl

theorem cell23_318867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_318867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318867 prefixEnd_318867 := by exact prefixLift 318867
  have htrace : WordTrace (prefixWord ++ tailWord_318867) baseStart_318867 baseEnd_318867 := by
    simpa [prefixWord, tailWord_318867, baseEnd_318867] using wordTrace_append hprefix tailTrace_318867
  have hstable : (prefixWord ++ tailWord_318867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318867).length < 2 ^ (prefixWord ++ tailWord_318867).sum := by decide
  have hdescent : baseEnd_318867 < baseStart_318867 := by decide
  rcases family_descends (prefixWord ++ tailWord_318867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318868 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_318868 : Nat := 118140960795 + 318868 * 2 ^ 59
def prefixEnd_318868 : Nat := 4983230072969 + 3 ^ 40 * 318868 * 2
def baseEnd_318868 : Nat := 163732549337963661183559

theorem tailTrace_318868 : CollatzResearch.WordTrace tailWord_318868 prefixEnd_318868 163732549337963661183559 := by
  unfold tailWord_318868
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815035704401584581930629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7753380939202112775907505 5815035704401584581930629)
  ·
    refine ⟨1090319194575297109111993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5815035704401584581930629 1090319194575297109111993)
    ·
      refine ⟨817739395931472831833995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090319194575297109111993 817739395931472831833995)
      ·
        refine ⟨1226609093897209247750993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817739395931472831833995 1226609093897209247750993)
        ·
          refine ⟨919956820422906935813245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1226609093897209247750993 919956820422906935813245)
          ·
            refine ⟨344983807658590100929967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919956820422906935813245 344983807658590100929967)
            ·
              refine ⟨517475711487885151394951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344983807658590100929967 517475711487885151394951)
              ·
                refine ⟨776213567231827727092427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517475711487885151394951 776213567231827727092427)
                ·
                  refine ⟨1164320350847741590638641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776213567231827727092427 1164320350847741590638641)
                  ·
                    refine ⟨873240263135806192978981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1164320350847741590638641 873240263135806192978981)
                    ·
                      refine ⟨163732549337963661183559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 873240263135806192978981 163732549337963661183559)
                      ·
                        rfl

theorem cell23_318868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_318868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318868 prefixEnd_318868 := by exact prefixLift 318868
  have htrace : WordTrace (prefixWord ++ tailWord_318868) baseStart_318868 baseEnd_318868 := by
    simpa [prefixWord, tailWord_318868, baseEnd_318868] using wordTrace_append hprefix tailTrace_318868
  have hstable : (prefixWord ++ tailWord_318868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318868).length < 2 ^ (prefixWord ++ tailWord_318868).sum := by decide
  have hdescent : baseEnd_318868 < baseStart_318868 := by decide
  rcases family_descends (prefixWord ++ tailWord_318868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318928 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2]
def baseStart_318928 : Nat := 118140960795 + 318928 * 2 ^ 59
def prefixEnd_318928 : Nat := 4983230072969 + 3 ^ 40 * 318928 * 2
def baseEnd_318928 : Nat := 163763358177233426433283

theorem tailTrace_318928 : CollatzResearch.WordTrace tailWord_318928 prefixEnd_318928 163763358177233426433283 := by
  unfold tailWord_318928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816129894292899705522719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7754839859057199607363625 5816129894292899705522719)
  ·
    refine ⟨8724194841439349558284079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816129894292899705522719 8724194841439349558284079)
    ·
      refine ⟨13086292262159024337426119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724194841439349558284079 13086292262159024337426119)
      ·
        refine ⟨19629438393238536506139179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086292262159024337426119 19629438393238536506139179)
        ·
          refine ⟨29444157589857804759208769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19629438393238536506139179 29444157589857804759208769)
          ·
            refine ⟨22083118192393353569406577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29444157589857804759208769 22083118192393353569406577)
            ·
              refine ⟨16562338644295015177054933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22083118192393353569406577 16562338644295015177054933)
              ·
                refine ⟨388179811975664418212225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16562338644295015177054933 388179811975664418212225)
                ·
                  refine ⟨291134858981748313659169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388179811975664418212225 291134858981748313659169)
                  ·
                    refine ⟨218351144236311235244377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291134858981748313659169 218351144236311235244377)
                    ·
                      refine ⟨163763358177233426433283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218351144236311235244377 163763358177233426433283)
                      ·
                        rfl

theorem cell23_318928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2].length) (baseStart_318928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318928 prefixEnd_318928 := by exact prefixLift 318928
  have htrace : WordTrace (prefixWord ++ tailWord_318928) baseStart_318928 baseEnd_318928 := by
    simpa [prefixWord, tailWord_318928, baseEnd_318928] using wordTrace_append hprefix tailTrace_318928
  have hstable : (prefixWord ++ tailWord_318928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318928).length < 2 ^ (prefixWord ++ tailWord_318928).sum := by decide
  have hdescent : baseEnd_318928 < baseStart_318928 := by decide
  rcases family_descends (prefixWord ++ tailWord_318928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318932 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_318932 : Nat := 118140960795 + 318932 * 2 ^ 59
def prefixEnd_318932 : Nat := 4983230072969 + 3 ^ 40 * 318932 * 2
def baseEnd_318932 : Nat := 163765412099851410783265

theorem tailTrace_318932 : CollatzResearch.WordTrace tailWord_318932 prefixEnd_318932 163765412099851410783265 := by
  unfold tailWord_318932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816202840285654047095525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7754937120380872062794033 5816202840285654047095525)
  ·
    refine ⟨1090538032553560133830411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5816202840285654047095525 1090538032553560133830411)
    ·
      refine ⟨1635807048830340200745617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090538032553560133830411 1635807048830340200745617)
      ·
        refine ⟨1226855286622755150559213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1635807048830340200745617 1226855286622755150559213)
        ·
          refine ⟨460070732483533181459705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1226855286622755150559213 460070732483533181459705)
          ·
            refine ⟨345053049362649886094779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460070732483533181459705 345053049362649886094779)
            ·
              refine ⟨517579574043974829142169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345053049362649886094779 517579574043974829142169)
              ·
                refine ⟨388184680532981121856627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517579574043974829142169 388184680532981121856627)
                ·
                  refine ⟨582277020799471682784941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388184680532981121856627 582277020799471682784941)
                  ·
                    refine ⟨218353882799801881044353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 582277020799471682784941 218353882799801881044353)
                    ·
                      refine ⟨163765412099851410783265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218353882799801881044353 163765412099851410783265)
                      ·
                        rfl

theorem cell23_318932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_318932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318932 prefixEnd_318932 := by exact prefixLift 318932
  have htrace : WordTrace (prefixWord ++ tailWord_318932) baseStart_318932 baseEnd_318932 := by
    simpa [prefixWord, tailWord_318932, baseEnd_318932] using wordTrace_append hprefix tailTrace_318932
  have hstable : (prefixWord ++ tailWord_318932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318932).length < 2 ^ (prefixWord ++ tailWord_318932).sum := by decide
  have hdescent : baseEnd_318932 < baseStart_318932 := by decide
  rcases family_descends (prefixWord ++ tailWord_318932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318944 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_318944 : Nat := 118140960795 + 318944 * 2 ^ 59
def prefixEnd_318944 : Nat := 4983230072969 + 3 ^ 40 * 318944 * 2
def baseEnd_318944 : Nat := 163771573867705363833209

theorem tailTrace_318944 : CollatzResearch.WordTrace tailWord_318944 prefixEnd_318944 163771573867705363833209 := by
  unfold tailWord_318944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816421678263917071813943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7755228904351889429085257 5816421678263917071813943)
  ·
    refine ⟨8724632517395875607720915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816421678263917071813943 8724632517395875607720915)
    ·
      refine ⟨13086948776093813411581373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724632517395875607720915 13086948776093813411581373)
      ·
        refine ⟨4907605791035180029343015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13086948776093813411581373 4907605791035180029343015)
        ·
          refine ⟨7361408686552770044014523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907605791035180029343015 7361408686552770044014523)
          ·
            refine ⟨11042113029829155066021785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361408686552770044014523 11042113029829155066021785)
            ·
              refine ⟨8281584772371866299516339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11042113029829155066021785 8281584772371866299516339)
              ·
                refine ⟨12422377158557799449274509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281584772371866299516339 12422377158557799449274509)
                ·
                  refine ⟨4658391434459174793477941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12422377158557799449274509 4658391434459174793477941)
                  ·
                    refine ⟨436724196980547636888557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4658391434459174793477941 436724196980547636888557)
                    ·
                      refine ⟨163771573867705363833209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 436724196980547636888557 163771573867705363833209)
                      ·
                        rfl

theorem cell23_318944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_318944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318944 prefixEnd_318944 := by exact prefixLift 318944
  have htrace : WordTrace (prefixWord ++ tailWord_318944) baseStart_318944 baseEnd_318944 := by
    simpa [prefixWord, tailWord_318944, baseEnd_318944] using wordTrace_append hprefix tailTrace_318944
  have hstable : (prefixWord ++ tailWord_318944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318944).length < 2 ^ (prefixWord ++ tailWord_318944).sum := by decide
  have hdescent : baseEnd_318944 < baseStart_318944 := by decide
  rcases family_descends (prefixWord ++ tailWord_318944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318962 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_318962 : Nat := 118140960795 + 318962 * 2 ^ 59
def prefixEnd_318962 : Nat := 4983230072969 + 3 ^ 40 * 318962 * 2
def baseEnd_318962 : Nat := 163780816519486293408127

theorem tailTrace_318962 : CollatzResearch.WordTrace tailWord_318962 prefixEnd_318962 163780816519486293408127 := by
  unfold tailWord_318962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908374967615655804445785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7755666580308415478522093 2908374967615655804445785)
  ·
    refine ⟨2181281225711741853334339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2908374967615655804445785 2181281225711741853334339)
    ·
      refine ⟨3271921838567612780001509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181281225711741853334339 3271921838567612780001509)
      ·
        refine ⟨613485344731427396250283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3271921838567612780001509 613485344731427396250283)
        ·
          refine ⟨920228017097141094375425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613485344731427396250283 920228017097141094375425)
          ·
            refine ⟨690171012822855820781569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 920228017097141094375425 690171012822855820781569)
            ·
              refine ⟨517628259617141865586177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690171012822855820781569 517628259617141865586177)
              ·
                refine ⟨388221194712856399189633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517628259617141865586177 388221194712856399189633)
                ·
                  refine ⟨291165896034642299392225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388221194712856399189633 291165896034642299392225)
                  ·
                    refine ⟨218374422025981724544169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 291165896034642299392225 218374422025981724544169)
                    ·
                      refine ⟨163780816519486293408127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218374422025981724544169 163780816519486293408127)
                      ·
                        rfl

theorem cell23_318962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_318962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318962 prefixEnd_318962 := by exact prefixLift 318962
  have htrace : WordTrace (prefixWord ++ tailWord_318962) baseStart_318962 baseEnd_318962 := by
    simpa [prefixWord, tailWord_318962, baseEnd_318962] using wordTrace_append hprefix tailTrace_318962
  have hstable : (prefixWord ++ tailWord_318962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318962).length < 2 ^ (prefixWord ++ tailWord_318962).sum := by decide
  have hdescent : baseEnd_318962 < baseStart_318962 := by decide
  rcases family_descends (prefixWord ++ tailWord_318962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318968 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 5]
def baseStart_318968 : Nat := 118140960795 + 318968 * 2 ^ 59
def prefixEnd_318968 : Nat := 4983230072969 + 3 ^ 40 * 318968 * 2
def baseEnd_318968 : Nat := 18198210822601474437011

theorem tailTrace_318968 : CollatzResearch.WordTrace tailWord_318968 prefixEnd_318968 18198210822601474437011 := by
  unfold tailWord_318968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816859354220443121250779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7755812472293924161667705 5816859354220443121250779)
  ·
    refine ⟨8725289031330664681876169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816859354220443121250779 8725289031330664681876169)
    ·
      refine ⟨6543966773497998511407127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8725289031330664681876169 6543966773497998511407127)
      ·
        refine ⟨9815950160246997767110691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6543966773497998511407127 9815950160246997767110691)
        ·
          refine ⟨14723925240370496650666037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9815950160246997767110691 14723925240370496650666037)
          ·
            refine ⟨1380367991284734060999941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14723925240370496650666037 1380367991284734060999941)
            ·
              refine ⟨258818998365887636437489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1380367991284734060999941 258818998365887636437489)
              ·
                refine ⟨194114248774415727328117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258818998365887636437489 194114248774415727328117)
                ·
                  refine ⟨18198210822601474437011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194114248774415727328117 18198210822601474437011)
                  ·
                    rfl

theorem cell23_318968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 5].length) (baseStart_318968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318968 prefixEnd_318968 := by exact prefixLift 318968
  have htrace : WordTrace (prefixWord ++ tailWord_318968) baseStart_318968 baseEnd_318968 := by
    simpa [prefixWord, tailWord_318968, baseEnd_318968] using wordTrace_append hprefix tailTrace_318968
  have hstable : (prefixWord ++ tailWord_318968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318968).length < 2 ^ (prefixWord ++ tailWord_318968).sum := by decide
  have hdescent : baseEnd_318968 < baseStart_318968 := by decide
  rcases family_descends (prefixWord ++ tailWord_318968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318978 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_318978 : Nat := 118140960795 + 318978 * 2 ^ 59
def prefixEnd_318978 : Nat := 4983230072969 + 3 ^ 40 * 318978 * 2
def baseEnd_318978 : Nat := 163789032209958230808053

theorem tailTrace_318978 : CollatzResearch.WordTrace tailWord_318978 prefixEnd_318978 163789032209958230808053 := by
  unfold tailWord_318978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908520859601164487591397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7756055625603105300243725 2908520859601164487591397)
  ·
    refine ⟨545347661175218341423387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2908520859601164487591397 545347661175218341423387)
    ·
      refine ⟨818021491762827512135081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545347661175218341423387 818021491762827512135081)
      ·
        refine ⟨613516118822120634101311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 818021491762827512135081 613516118822120634101311)
        ·
          refine ⟨920274178233180951151967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613516118822120634101311 920274178233180951151967)
          ·
            refine ⟨1380411267349771426727951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920274178233180951151967 1380411267349771426727951)
            ·
              refine ⟨2070616901024657140091927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380411267349771426727951 2070616901024657140091927)
              ·
                refine ⟨3105925351536985710137891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070616901024657140091927 3105925351536985710137891)
                ·
                  refine ⟨4658888027305478565206837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105925351536985710137891 4658888027305478565206837)
                  ·
                    refine ⟨436770752559888615488141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4658888027305478565206837 436770752559888615488141)
                    ·
                      refine ⟨163789032209958230808053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 436770752559888615488141 163789032209958230808053)
                      ·
                        rfl

theorem cell23_318978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_318978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_318978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_318978 prefixEnd_318978 := by exact prefixLift 318978
  have htrace : WordTrace (prefixWord ++ tailWord_318978) baseStart_318978 baseEnd_318978 := by
    simpa [prefixWord, tailWord_318978, baseEnd_318978] using wordTrace_append hprefix tailTrace_318978
  have hstable : (prefixWord ++ tailWord_318978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318978).length < 2 ^ (prefixWord ++ tailWord_318978).sum := by decide
  have hdescent : baseEnd_318978 < baseStart_318978 := by decide
  rcases family_descends (prefixWord ++ tailWord_318978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319001 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 4, 2]
def baseStart_319001 : Nat := 118140960795 + 319001 * 2 ^ 59
def prefixEnd_319001 : Nat := 4983230072969 + 3 ^ 40 * 319001 * 2
def baseEnd_319001 : Nat := 163800842265011640820447

theorem tailTrace_319001 : CollatzResearch.WordTrace tailWord_319001 prefixEnd_319001 163800842265011640820447 := by
  unfold tailWord_319001
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634922317321332878452857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7756614878214221918968571 11634922317321332878452857)
  ·
    refine ⟨8726191737990999658839643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11634922317321332878452857 8726191737990999658839643)
    ·
      refine ⟨13089287606986499488259465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8726191737990999658839643 13089287606986499488259465)
      ·
        refine ⟨9816965705239874616194599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13089287606986499488259465 9816965705239874616194599)
        ·
          refine ⟨14725448557859811924291899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816965705239874616194599 14725448557859811924291899)
          ·
            refine ⟨22088172836789717886437849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725448557859811924291899 22088172836789717886437849)
            ·
              refine ⟨16566129627592288414828387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22088172836789717886437849 16566129627592288414828387)
              ·
                refine ⟨24849194441388432622242581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16566129627592288414828387 24849194441388432622242581)
                ·
                  refine ⟨1164805989440082779167621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24849194441388432622242581 1164805989440082779167621)
                  ·
                    refine ⟨218401123020015521093929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164805989440082779167621 218401123020015521093929)
                    ·
                      refine ⟨163800842265011640820447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218401123020015521093929 163800842265011640820447)
                      ·
                        rfl

theorem cell23_319001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_319001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319001 prefixEnd_319001 := by exact prefixLift 319001
  have htrace : WordTrace (prefixWord ++ tailWord_319001) baseStart_319001 baseEnd_319001 := by
    simpa [prefixWord, tailWord_319001, baseEnd_319001] using wordTrace_append hprefix tailTrace_319001
  have hstable : (prefixWord ++ tailWord_319001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319001).length < 2 ^ (prefixWord ++ tailWord_319001).sum := by decide
  have hdescent : baseEnd_319001 < baseStart_319001 := by decide
  rcases family_descends (prefixWord ++ tailWord_319001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319018 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_319018 : Nat := 118140960795 + 319018 * 2 ^ 59
def prefixEnd_319018 : Nat := 4983230072969 + 3 ^ 40 * 319018 * 2
def baseEnd_319018 : Nat := 163809571436138074307869

theorem tailTrace_319018 : CollatzResearch.WordTrace tailWord_319018 prefixEnd_319018 163809571436138074307869 := by
  unfold tailWord_319018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908885589564936195455427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7757028238839829854547805 2908885589564936195455427)
  ·
    refine ⟨4363328384347404293183141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908885589564936195455427 4363328384347404293183141)
    ·
      refine ⟨818124072065138304971839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4363328384347404293183141 818124072065138304971839)
      ·
        refine ⟨1227186108097707457457759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818124072065138304971839 1227186108097707457457759)
        ·
          refine ⟨1840779162146561186186639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227186108097707457457759 1840779162146561186186639)
          ·
            refine ⟨2761168743219841779279959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840779162146561186186639 2761168743219841779279959)
            ·
              refine ⟨4141753114829762668919939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761168743219841779279959 4141753114829762668919939)
              ·
                refine ⟨6212629672244644003379909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141753114829762668919939 6212629672244644003379909)
                ·
                  refine ⟨1164868063545870750633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6212629672244644003379909 1164868063545870750633733)
                  ·
                    refine ⟨218412761914850765743825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164868063545870750633733 218412761914850765743825)
                    ·
                      refine ⟨163809571436138074307869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 218412761914850765743825 163809571436138074307869)
                      ·
                        rfl

theorem cell23_319018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_319018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319018 prefixEnd_319018 := by exact prefixLift 319018
  have htrace : WordTrace (prefixWord ++ tailWord_319018) baseStart_319018 baseEnd_319018 := by
    simpa [prefixWord, tailWord_319018, baseEnd_319018] using wordTrace_append hprefix tailTrace_319018
  have hstable : (prefixWord ++ tailWord_319018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319018).length < 2 ^ (prefixWord ++ tailWord_319018).sum := by decide
  have hdescent : baseEnd_319018 < baseStart_319018 := by decide
  rcases family_descends (prefixWord ++ tailWord_319018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319105 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_319105 : Nat := 118140960795 + 319105 * 2 ^ 59
def prefixEnd_319105 : Nat := 4983230072969 + 3 ^ 40 * 319105 * 2
def baseEnd_319105 : Nat := 54618081417693077973323

theorem tailTrace_319105 : CollatzResearch.WordTrace tailWord_319105 prefixEnd_319105 54618081417693077973323 := by
  unfold tailWord_319105
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638715508944558640238769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7759143672629705760159179 11638715508944558640238769)
  ·
    refine ⟨8729036631708418980179077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11638715508944558640238769 8729036631708418980179077)
    ·
      refine ⟨1636694368445328558783577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8729036631708418980179077 1636694368445328558783577)
      ·
        refine ⟨1227520776333996419087683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636694368445328558783577 1227520776333996419087683)
        ·
          refine ⟨1841281164500994628631525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227520776333996419087683 1841281164500994628631525)
          ·
            refine ⟨345240218343936492868411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1841281164500994628631525 345240218343936492868411)
            ·
              refine ⟨517860327515904739302617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345240218343936492868411 517860327515904739302617)
              ·
                refine ⟨388395245636928554476963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517860327515904739302617 388395245636928554476963)
                ·
                  refine ⟨582592868455392831715445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388395245636928554476963 582592868455392831715445)
                  ·
                    refine ⟨54618081417693077973323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 582592868455392831715445 54618081417693077973323)
                    ·
                      rfl

theorem cell23_319105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_319105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319105 prefixEnd_319105 := by exact prefixLift 319105
  have htrace : WordTrace (prefixWord ++ tailWord_319105) baseStart_319105 baseEnd_319105 := by
    simpa [prefixWord, tailWord_319105, baseEnd_319105] using wordTrace_append hprefix tailTrace_319105
  have hstable : (prefixWord ++ tailWord_319105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319105).length < 2 ^ (prefixWord ++ tailWord_319105).sum := by decide
  have hdescent : baseEnd_319105 < baseStart_319105 := by decide
  rcases family_descends (prefixWord ++ tailWord_319105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319118 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_319118 : Nat := 118140960795 + 319118 * 2 ^ 59
def prefixEnd_319118 : Nat := 4983230072969 + 3 ^ 40 * 319118 * 2
def baseEnd_319118 : Nat := 54620306500529227685803

theorem tailTrace_319118 : CollatzResearch.WordTrace tailWord_319118 prefixEnd_319118 54620306500529227685803 := by
  unfold tailWord_319118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454898707237182732557751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7759459771931641240308005 1454898707237182732557751)
  ·
    refine ⟨2182348060855774098836627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1454898707237182732557751 2182348060855774098836627)
    ·
      refine ⟨3273522091283661148254941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182348060855774098836627 3273522091283661148254941)
      ·
        refine ⟨1227570784231372930595603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3273522091283661148254941 1227570784231372930595603)
        ·
          refine ⟨1841356176347059395893405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227570784231372930595603 1841356176347059395893405)
          ·
            refine ⟨690508566130147273460027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1841356176347059395893405 690508566130147273460027)
            ·
              refine ⟨1035762849195220910190041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690508566130147273460027 1035762849195220910190041)
              ·
                refine ⟨776822136896415682642531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035762849195220910190041 776822136896415682642531)
                ·
                  refine ⟨1165233205344623523963797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776822136896415682642531 1165233205344623523963797)
                  ·
                    refine ⟨54620306500529227685803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1165233205344623523963797 54620306500529227685803)
                    ·
                      rfl

theorem cell23_319118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_319118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319118 prefixEnd_319118 := by exact prefixLift 319118
  have htrace : WordTrace (prefixWord ++ tailWord_319118) baseStart_319118 baseEnd_319118 := by
    simpa [prefixWord, tailWord_319118, baseEnd_319118] using wordTrace_append hprefix tailTrace_319118
  have hstable : (prefixWord ++ tailWord_319118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319118).length < 2 ^ (prefixWord ++ tailWord_319118).sum := by decide
  have hdescent : baseEnd_319118 < baseStart_319118 := by decide
  rcases family_descends (prefixWord ++ tailWord_319118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319122 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_319122 : Nat := 118140960795 + 319122 * 2 ^ 59
def prefixEnd_319122 : Nat := 4983230072969 + 3 ^ 40 * 319122 * 2
def baseEnd_319122 : Nat := 54620991141401889135797

theorem tailTrace_319122 : CollatzResearch.WordTrace tailWord_319122 prefixEnd_319122 54620991141401889135797 := by
  unfold tailWord_319122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909833887470742635901905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7759557033255313695738413 2909833887470742635901905)
  ·
    refine ⟨2182375415603056976926429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2909833887470742635901905 2182375415603056976926429)
    ·
      refine ⟨818390780851146366347411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2182375415603056976926429 818390780851146366347411)
      ·
        refine ⟨1227586171276719549521117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818390780851146366347411 1227586171276719549521117)
        ·
          refine ⟨460344814228769831070419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1227586171276719549521117 460344814228769831070419)
          ·
            refine ⟨690517221343154746605629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460344814228769831070419 690517221343154746605629)
            ·
              refine ⟨258943958003683029977111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690517221343154746605629 258943958003683029977111)
              ·
                refine ⟨388415937005524544965667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258943958003683029977111 388415937005524544965667)
                ·
                  refine ⟨582623905508286817448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388415937005524544965667 582623905508286817448501)
                  ·
                    refine ⟨54620991141401889135797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 582623905508286817448501 54620991141401889135797)
                    ·
                      rfl

theorem cell23_319122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_319122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319122 prefixEnd_319122 := by exact prefixLift 319122
  have htrace : WordTrace (prefixWord ++ tailWord_319122) baseStart_319122 baseEnd_319122 := by
    simpa [prefixWord, tailWord_319122, baseEnd_319122] using wordTrace_append hprefix tailTrace_319122
  have hstable : (prefixWord ++ tailWord_319122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319122).length < 2 ^ (prefixWord ++ tailWord_319122).sum := by decide
  have hdescent : baseEnd_319122 < baseStart_319122 := by decide
  rcases family_descends (prefixWord ++ tailWord_319122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319128 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_319128 : Nat := 118140960795 + 319128 * 2 ^ 59
def prefixEnd_319128 : Nat := 4983230072969 + 3 ^ 40 * 319128 * 2
def baseEnd_319128 : Nat := 163866054308132643932363

theorem tailTrace_319128 : CollatzResearch.WordTrace tailWord_319128 prefixEnd_319128 163866054308132643932363 := by
  unfold tailWord_319128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819777193930616784163019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7759702925240822378884025 5819777193930616784163019)
  ·
    refine ⟨8729665790895925176244529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5819777193930616784163019 8729665790895925176244529)
    ·
      refine ⟨6547249343171943882183397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8729665790895925176244529 6547249343171943882183397)
      ·
        refine ⟨1227609251844739477909387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6547249343171943882183397 1227609251844739477909387)
        ·
          refine ⟨1841413877767109216864081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227609251844739477909387 1841413877767109216864081)
          ·
            refine ⟨1381060408325331912648061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841413877767109216864081 1381060408325331912648061)
            ·
              refine ⟨517897653121999467243023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1381060408325331912648061 517897653121999467243023)
              ·
                refine ⟨776846479682999200864535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517897653121999467243023 776846479682999200864535)
                ·
                  refine ⟨1165269719524498801296803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776846479682999200864535 1165269719524498801296803)
                  ·
                    refine ⟨1747904579286748201945205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165269719524498801296803 1747904579286748201945205)
                    ·
                      refine ⟨163866054308132643932363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1747904579286748201945205 163866054308132643932363)
                      ·
                        rfl

theorem cell23_319128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_319128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319128 prefixEnd_319128 := by exact prefixLift 319128
  have htrace : WordTrace (prefixWord ++ tailWord_319128) baseStart_319128 baseEnd_319128 := by
    simpa [prefixWord, tailWord_319128, baseEnd_319128] using wordTrace_append hprefix tailTrace_319128
  have hstable : (prefixWord ++ tailWord_319128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319128).length < 2 ^ (prefixWord ++ tailWord_319128).sum := by decide
  have hdescent : baseEnd_319128 < baseStart_319128 := by decide
  rcases family_descends (prefixWord ++ tailWord_319128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319191 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 6]
def baseStart_319191 : Nat := 118140960795 + 319191 * 2 ^ 59
def prefixEnd_319191 : Nat := 4983230072969 + 3 ^ 40 * 319191 * 2
def baseEnd_319191 : Nat := 54632801196455299148191

theorem tailTrace_319191 : CollatzResearch.WordTrace tailWord_319191 prefixEnd_319191 54632801196455299148191 := by
  unfold tailWord_319191
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641852186632995327869427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7761234791088663551912951 11641852186632995327869427)
  ·
    refine ⟨17462778279949492991804141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641852186632995327869427 17462778279949492991804141)
    ·
      refine ⟨6548541854981059871926553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17462778279949492991804141 6548541854981059871926553)
      ·
        refine ⟨4911406391235794903944915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548541854981059871926553 4911406391235794903944915)
        ·
          refine ⟨7367109586853692355917373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911406391235794903944915 7367109586853692355917373)
          ·
            refine ⟨2762666095070134633469015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7367109586853692355917373 2762666095070134633469015)
            ·
              refine ⟨4143999142605201950203523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762666095070134633469015 4143999142605201950203523)
              ·
                refine ⟨6215998713907802925305285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143999142605201950203523 6215998713907802925305285)
                ·
                  refine ⟨1165499758857713048494741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6215998713907802925305285 1165499758857713048494741)
                  ·
                    refine ⟨54632801196455299148191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1165499758857713048494741 54632801196455299148191)
                    ·
                      rfl

theorem cell23_319191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_319191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319191 prefixEnd_319191 := by exact prefixLift 319191
  have htrace : WordTrace (prefixWord ++ tailWord_319191) baseStart_319191 baseEnd_319191 := by
    simpa [prefixWord, tailWord_319191, baseEnd_319191] using wordTrace_append hprefix tailTrace_319191
  have hstable : (prefixWord ++ tailWord_319191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319191).length < 2 ^ (prefixWord ++ tailWord_319191).sum := by decide
  have hdescent : baseEnd_319191 < baseStart_319191 := by decide
  rcases family_descends (prefixWord ++ tailWord_319191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319208 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_319208 : Nat := 118140960795 + 319208 * 2 ^ 59
def prefixEnd_319208 : Nat := 4983230072969 + 3 ^ 40 * 319208 * 2
def baseEnd_319208 : Nat := 54635710920164110310665

theorem tailTrace_319208 : CollatzResearch.WordTrace tailWord_319208 prefixEnd_319208 54635710920164110310665 := by
  unfold tailWord_319208
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821236113785703615619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7761648151714271487492185 5821236113785703615619139)
  ·
    refine ⟨8731854170678555423428709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5821236113785703615619139 8731854170678555423428709)
    ·
      refine ⟨1637222657002229141892883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8731854170678555423428709 1637222657002229141892883)
      ·
        refine ⟨2455833985503343712839325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637222657002229141892883 2455833985503343712839325)
        ·
          refine ⟨920937744563753892314747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2455833985503343712839325 920937744563753892314747)
          ·
            refine ⟨1381406616845630838472121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920937744563753892314747 1381406616845630838472121)
            ·
              refine ⟨1036054962634223128854091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381406616845630838472121 1036054962634223128854091)
              ·
                refine ⟨1554082443951334693281137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036054962634223128854091 1554082443951334693281137)
                ·
                  refine ⟨1165561832963501019960853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554082443951334693281137 1165561832963501019960853)
                  ·
                    refine ⟨54635710920164110310665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1165561832963501019960853 54635710920164110310665)
                    ·
                      rfl

theorem cell23_319208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_319208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319208 prefixEnd_319208 := by exact prefixLift 319208
  have htrace : WordTrace (prefixWord ++ tailWord_319208) baseStart_319208 baseEnd_319208 := by
    simpa [prefixWord, tailWord_319208, baseEnd_319208] using wordTrace_append hprefix tailTrace_319208
  have hstable : (prefixWord ++ tailWord_319208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319208).length < 2 ^ (prefixWord ++ tailWord_319208).sum := by decide
  have hdescent : baseEnd_319208 < baseStart_319208 := by decide
  rcases family_descends (prefixWord ++ tailWord_319208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319218 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_319218 : Nat := 118140960795 + 319218 * 2 ^ 59
def prefixEnd_319218 : Nat := 4983230072969 + 3 ^ 40 * 319218 * 2
def baseEnd_319218 : Nat := 163912267567037291806949

theorem tailTrace_319218 : CollatzResearch.WordTrace tailWord_319218 prefixEnd_319218 163912267567037291806949 := by
  unfold tailWord_319218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910709239383794734775577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7761891305023452626068205 2910709239383794734775577)
  ·
    refine ⟨2183031929537846051081683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2910709239383794734775577 2183031929537846051081683)
    ·
      refine ⟨3274547894306769076622525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2183031929537846051081683 3274547894306769076622525)
      ·
        refine ⟨1227955460365038403733447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3274547894306769076622525 1227955460365038403733447)
        ·
          refine ⟨1841933190547557605600171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227955460365038403733447 1841933190547557605600171)
          ·
            refine ⟨2762899785821336408400257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841933190547557605600171 2762899785821336408400257)
            ·
              refine ⟨2072174839366002306300193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762899785821336408400257 2072174839366002306300193)
              ·
                refine ⟨1554131129524501729725145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072174839366002306300193 1554131129524501729725145)
                ·
                  refine ⟨1165598347143376297293859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554131129524501729725145 1165598347143376297293859)
                  ·
                    refine ⟨1748397520715064445940789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165598347143376297293859 1748397520715064445940789)
                    ·
                      refine ⟨163912267567037291806949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1748397520715064445940789 163912267567037291806949)
                      ·
                        rfl

theorem cell23_319218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_319218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319218 prefixEnd_319218 := by exact prefixLift 319218
  have htrace : WordTrace (prefixWord ++ tailWord_319218) baseStart_319218 baseEnd_319218 := by
    simpa [prefixWord, tailWord_319218, baseEnd_319218] using wordTrace_append hprefix tailTrace_319218
  have hstable : (prefixWord ++ tailWord_319218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319218).length < 2 ^ (prefixWord ++ tailWord_319218).sum := by decide
  have hdescent : baseEnd_319218 < baseStart_319218 := by decide
  rcases family_descends (prefixWord ++ tailWord_319218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319251 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 7]
def baseStart_319251 : Nat := 118140960795 + 319251 * 2 ^ 59
def prefixEnd_319251 : Nat := 4983230072969 + 3 ^ 40 * 319251 * 2
def baseEnd_319251 : Nat := 54643070809545220898099

theorem tailTrace_319251 : CollatzResearch.WordTrace tailWord_319251 prefixEnd_319251 54643070809545220898099 := by
  unfold tailWord_319251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644040566415625575053607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7762693710943750383369071 11644040566415625575053607)
  ·
    refine ⟨17466060849623438362580411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644040566415625575053607 17466060849623438362580411)
    ·
      refine ⟨26199091274435157543870617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17466060849623438362580411 26199091274435157543870617)
      ·
        refine ⟨19649318455826368157902963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26199091274435157543870617 19649318455826368157902963)
        ·
          refine ⟨29473977683739552236854445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19649318455826368157902963 29473977683739552236854445)
          ·
            refine ⟨11052741631402332088820417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29473977683739552236854445 11052741631402332088820417)
            ·
              refine ⟨8289556223551749066615313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11052741631402332088820417 8289556223551749066615313)
              ·
                refine ⟨6217167167663811799961485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289556223551749066615313 6217167167663811799961485)
                ·
                  refine ⟨2331437687873929424985557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217167167663811799961485 2331437687873929424985557)
                  ·
                    refine ⟨54643070809545220898099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2331437687873929424985557 54643070809545220898099)
                    ·
                      rfl

theorem cell23_319251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_319251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_319251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_319251 prefixEnd_319251 := by exact prefixLift 319251
  have htrace : WordTrace (prefixWord ++ tailWord_319251) baseStart_319251 baseEnd_319251 := by
    simpa [prefixWord, tailWord_319251, baseEnd_319251] using wordTrace_append hprefix tailTrace_319251
  have hstable : (prefixWord ++ tailWord_319251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319251).length < 2 ^ (prefixWord ++ tailWord_319251).sum := by decide
  have hdescent : baseEnd_319251 < baseStart_319251 := by decide
  rcases family_descends (prefixWord ++ tailWord_319251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
