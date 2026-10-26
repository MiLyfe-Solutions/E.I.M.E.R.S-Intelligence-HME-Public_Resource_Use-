import V185TrunkScan23Chunk0197

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1171992 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 6]
def baseStart_1171992 : Nat := 118140960795 + 1171992 * 2 ^ 59
def prefixEnd_1171992 : Nat := 4983230072969 + 3 ^ 40 * 1171992 * 2
def baseEnd_1171992 : Nat := 66866135469364867734457

theorem tailTrace_1171992 : CollatzResearch.WordTrace tailWord_1171992 prefixEnd_1171992 66866135469364867734457 := by
  unfold tailWord_1171992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21373029985040309571567115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28497373313387079428756153 21373029985040309571567115)
  ·
    refine ⟨32059544977560464357350673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21373029985040309571567115 32059544977560464357350673)
    ·
      refine ⟨24044658733170348268013005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32059544977560464357350673 24044658733170348268013005)
      ·
        refine ⟨9016747024938880600504877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24044658733170348268013005 9016747024938880600504877)
        ·
          refine ⟨3381280134352080225189329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9016747024938880600504877 3381280134352080225189329)
          ·
            refine ⟨2535960100764060168891997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381280134352080225189329 2535960100764060168891997)
            ·
              refine ⟨950985037786522563334499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2535960100764060168891997 950985037786522563334499)
              ·
                refine ⟨1426477556679783845001749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950985037786522563334499 1426477556679783845001749)
                ·
                  refine ⟨66866135469364867734457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1426477556679783845001749 66866135469364867734457)
                  ·
                    rfl

theorem cell23_1171992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_1171992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1171992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1171992 prefixEnd_1171992 := by exact prefixLift 1171992
  have htrace : WordTrace (prefixWord ++ tailWord_1171992) baseStart_1171992 baseEnd_1171992 := by
    simpa [prefixWord, tailWord_1171992, baseEnd_1171992] using wordTrace_append hprefix tailTrace_1171992
  have hstable : (prefixWord ++ tailWord_1171992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171992).length < 2 ^ (prefixWord ++ tailWord_1171992).sum := by decide
  have hdescent : baseEnd_1171992 < baseStart_1171992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172005 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_1172005 : Nat := 118140960795 + 1172005 * 2 ^ 59
def prefixEnd_1172005 : Nat := 4983230072969 + 3 ^ 40 * 1172005 * 2
def baseEnd_1172005 : Nat := 200600631490930752915851

theorem tailTrace_1172005 : CollatzResearch.WordTrace tailWord_1172005 prefixEnd_1172005 200600631490930752915851 := by
  unfold tailWord_1172005
  simp only [CollatzResearch.WordTrace]
  refine ⟨42746534119033522363357469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28497689412689014908904979 42746534119033522363357469)
  ·
    refine ⟨16029950294637570886259051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42746534119033522363357469 16029950294637570886259051)
    ·
      refine ⟨24044925441956356329388577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16029950294637570886259051 24044925441956356329388577)
      ·
        refine ⟨18033694081467267247041433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24044925441956356329388577 18033694081467267247041433)
        ·
          refine ⟨13525270561100450435281075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18033694081467267247041433 13525270561100450435281075)
          ·
            refine ⟨20287905841650675652921613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13525270561100450435281075 20287905841650675652921613)
            ·
              refine ⟨7607964690619003369845605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20287905841650675652921613 7607964690619003369845605)
              ·
                refine ⟨1426493379491063131846051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7607964690619003369845605 1426493379491063131846051)
                ·
                  refine ⟨2139740069236594697769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426493379491063131846051 2139740069236594697769077)
                  ·
                    refine ⟨200600631490930752915851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2139740069236594697769077 200600631490930752915851)
                    ·
                      rfl

theorem cell23_1172005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_1172005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172005 prefixEnd_1172005 := by exact prefixLift 1172005
  have htrace : WordTrace (prefixWord ++ tailWord_1172005) baseStart_1172005 baseEnd_1172005 := by
    simpa [prefixWord, tailWord_1172005, baseEnd_1172005] using wordTrace_append hprefix tailTrace_1172005
  have hstable : (prefixWord ++ tailWord_1172005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172005).length < 2 ^ (prefixWord ++ tailWord_1172005).sum := by decide
  have hdescent : baseEnd_1172005 < baseStart_1172005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172029 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1172029 : Nat := 118140960795 + 1172029 * 2 ^ 59
def prefixEnd_1172029 : Nat := 4983230072969 + 3 ^ 40 * 1172029 * 2
def baseEnd_1172029 : Nat := 601814218008500164847443

theorem tailTrace_1172029 : CollatzResearch.WordTrace tailWord_1172029 prefixEnd_1172029 601814218008500164847443 := by
  unfold tailWord_1172029
  simp only [CollatzResearch.WordTrace]
  refine ⟨42747409470946574462231141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28498272980631049641487427 42747409470946574462231141)
  ·
    refine ⟨8015139275802482711668339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42747409470946574462231141 8015139275802482711668339)
    ·
      refine ⟨12022708913703724067502509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015139275802482711668339 12022708913703724067502509)
      ·
        refine ⟨4508515842638896525313441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12022708913703724067502509 4508515842638896525313441)
        ·
          refine ⟨3381386881979172393985081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4508515842638896525313441 3381386881979172393985081)
          ·
            refine ⟨2536040161484379295488811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381386881979172393985081 2536040161484379295488811)
            ·
              refine ⟨3804060242226568943233217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536040161484379295488811 3804060242226568943233217)
              ·
                refine ⟨2853045181669926707424913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3804060242226568943233217 2853045181669926707424913)
                ·
                  refine ⟨2139783886252445030568685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853045181669926707424913 2139783886252445030568685)
                  ·
                    refine ⟨802418957344666886463257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139783886252445030568685 802418957344666886463257)
                    ·
                      refine ⟨601814218008500164847443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802418957344666886463257 601814218008500164847443)
                      ·
                        rfl

theorem cell23_1172029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1172029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172029 prefixEnd_1172029 := by exact prefixLift 1172029
  have htrace : WordTrace (prefixWord ++ tailWord_1172029) baseStart_1172029 baseEnd_1172029 := by
    simpa [prefixWord, tailWord_1172029, baseEnd_1172029] using wordTrace_append hprefix tailTrace_1172029
  have hstable : (prefixWord ++ tailWord_1172029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172029).length < 2 ^ (prefixWord ++ tailWord_1172029).sum := by decide
  have hdescent : baseEnd_1172029 < baseStart_1172029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172055 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1172055 : Nat := 118140960795 + 1172055 * 2 ^ 59
def prefixEnd_1172055 : Nat := 4983230072969 + 3 ^ 40 * 1172055 * 2
def baseEnd_1172055 : Nat := 601827568505517063122323

theorem tailTrace_1172055 : CollatzResearch.WordTrace tailWord_1172055 prefixEnd_1172055 601827568505517063122323 := by
  unfold tailWord_1172055
  simp only [CollatzResearch.WordTrace]
  refine ⟨42748357768852380902677619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28498905179234920601785079 42748357768852380902677619)
  ·
    refine ⟨64122536653278571354016429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42748357768852380902677619 64122536653278571354016429)
    ·
      refine ⟨24045951244979464257756161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64122536653278571354016429 24045951244979464257756161)
      ·
        refine ⟨18034463433734598193317121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24045951244979464257756161 18034463433734598193317121)
        ·
          refine ⟨13525847575300948644987841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18034463433734598193317121 13525847575300948644987841)
          ·
            refine ⟨10144385681475711483740881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13525847575300948644987841 10144385681475711483740881)
            ·
              refine ⟨7608289261106783612805661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10144385681475711483740881 7608289261106783612805661)
              ·
                refine ⟨2853108472915043854802123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7608289261106783612805661 2853108472915043854802123)
                ·
                  refine ⟨4279662709372565782203185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853108472915043854802123 4279662709372565782203185)
                  ·
                    refine ⟨3209747032029424336652389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4279662709372565782203185 3209747032029424336652389)
                    ·
                      refine ⟨601827568505517063122323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3209747032029424336652389 601827568505517063122323)
                      ·
                        rfl

theorem cell23_1172055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1172055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172055 prefixEnd_1172055 := by exact prefixLift 1172055
  have htrace : WordTrace (prefixWord ++ tailWord_1172055) baseStart_1172055 baseEnd_1172055 := by
    simpa [prefixWord, tailWord_1172055, baseEnd_1172055] using wordTrace_append hprefix tailTrace_1172055
  have hstable : (prefixWord ++ tailWord_1172055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172055).length < 2 ^ (prefixWord ++ tailWord_1172055).sum := by decide
  have hdescent : baseEnd_1172055 < baseStart_1172055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172086 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1172086 : Nat := 118140960795 + 1172086 * 2 ^ 59
def prefixEnd_1172086 : Nat := 4983230072969 + 3 ^ 40 * 1172086 * 2
def baseEnd_1172086 : Nat := 200614495468602147278227

theorem tailTrace_1172086 : CollatzResearch.WordTrace tailWord_1172086 prefixEnd_1172086 200614495468602147278227 := by
  unfold tailWord_1172086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671843026983754574816007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28499658954493382131370741 2671843026983754574816007)
  ·
    refine ⟨4007764540475631862224011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671843026983754574816007 4007764540475631862224011)
    ·
      refine ⟨6011646810713447793336017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007764540475631862224011 6011646810713447793336017)
      ·
        refine ⟨4508735108035085845002013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6011646810713447793336017 4508735108035085845002013)
        ·
          refine ⟨1690775665513157191875755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4508735108035085845002013 1690775665513157191875755)
          ·
            refine ⟨2536163498269735787813633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690775665513157191875755 2536163498269735787813633)
            ·
              refine ⟨1902122623702301840860225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536163498269735787813633 1902122623702301840860225)
              ·
                refine ⟨1426591967776726380645169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902122623702301840860225 1426591967776726380645169)
                ·
                  refine ⟨1069943975832544785483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426591967776726380645169 1069943975832544785483877)
                  ·
                    refine ⟨200614495468602147278227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1069943975832544785483877 200614495468602147278227)
                    ·
                      rfl

theorem cell23_1172086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1172086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172086 prefixEnd_1172086 := by exact prefixLift 1172086
  have htrace : WordTrace (prefixWord ++ tailWord_1172086) baseStart_1172086 baseEnd_1172086 := by
    simpa [prefixWord, tailWord_1172086, baseEnd_1172086] using wordTrace_append hprefix tailTrace_1172086
  have hstable : (prefixWord ++ tailWord_1172086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172086).length < 2 ^ (prefixWord ++ tailWord_1172086).sum := by decide
  have hdescent : baseEnd_1172086 < baseStart_1172086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172092 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_1172092 : Nat := 118140960795 + 1172092 * 2 ^ 59
def prefixEnd_1172092 : Nat := 4983230072969 + 3 ^ 40 * 1172092 * 2
def baseEnd_1172092 : Nat := 601846567289733418359653

theorem tailTrace_1172092 : CollatzResearch.WordTrace tailWord_1172092 prefixEnd_1172092 601846567289733418359653 := by
  unfold tailWord_1172092
  simp only [CollatzResearch.WordTrace]
  refine ⟨21374853634859168110887265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28499804846478890814516353 21374853634859168110887265)
  ·
    refine ⟨16031140226144376083165449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21374853634859168110887265 16031140226144376083165449)
    ·
      refine ⟨12023355169608282062374087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16031140226144376083165449 12023355169608282062374087)
      ·
        refine ⟨18035032754412423093561131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12023355169608282062374087 18035032754412423093561131)
        ·
          refine ⟨27052549131618634640341697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18035032754412423093561131 27052549131618634640341697)
          ·
            refine ⟨20289411848713975980256273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27052549131618634640341697 20289411848713975980256273)
            ·
              refine ⟨15217058886535481985192205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20289411848713975980256273 15217058886535481985192205)
              ·
                refine ⟨5706397082450805744447077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15217058886535481985192205 5706397082450805744447077)
                ·
                  refine ⟨1069949452959526077083827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5706397082450805744447077 1069949452959526077083827)
                  ·
                    refine ⟨1604924179439289115625741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1069949452959526077083827 1604924179439289115625741)
                    ·
                      refine ⟨601846567289733418359653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1604924179439289115625741 601846567289733418359653)
                      ·
                        rfl

theorem cell23_1172092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_1172092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172092 prefixEnd_1172092 := by exact prefixLift 1172092
  have htrace : WordTrace (prefixWord ++ tailWord_1172092) baseStart_1172092 baseEnd_1172092 := by
    simpa [prefixWord, tailWord_1172092, baseEnd_1172092] using wordTrace_append hprefix tailTrace_1172092
  have hstable : (prefixWord ++ tailWord_1172092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172092).length < 2 ^ (prefixWord ++ tailWord_1172092).sum := by decide
  have hdescent : baseEnd_1172092 < baseStart_1172092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172093 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_1172093 : Nat := 118140960795 + 1172093 * 2 ^ 59
def prefixEnd_1172093 : Nat := 4983230072969 + 3 ^ 40 * 1172093 * 2
def baseEnd_1172093 : Nat := 601847080770387914447149

theorem tailTrace_1172093 : CollatzResearch.WordTrace tailWord_1172093 prefixEnd_1172093 601847080770387914447149 := by
  unfold tailWord_1172093
  simp only [CollatzResearch.WordTrace]
  refine ⟨42749743742714713392560933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28499829161809808928373955 42749743742714713392560933)
  ·
    refine ⟨8015576951759008761105175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42749743742714713392560933 8015576951759008761105175)
    ·
      refine ⟨12023365427638513141657763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015576951759008761105175 12023365427638513141657763)
      ·
        refine ⟨18035048141457769712486645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12023365427638513141657763 18035048141457769712486645)
        ·
          refine ⟨1690785763261665910545623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18035048141457769712486645 1690785763261665910545623)
          ·
            refine ⟨2536178644892498865818435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690785763261665910545623 2536178644892498865818435)
            ·
              refine ⟨3804267967338748298727653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536178644892498865818435 3804267967338748298727653)
              ·
                refine ⟨713300243876015306011435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3804267967338748298727653 713300243876015306011435)
                ·
                  refine ⟨1069950365814022959017153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713300243876015306011435 1069950365814022959017153)
                  ·
                    refine ⟨802462774360517219262865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1069950365814022959017153 802462774360517219262865)
                    ·
                      refine ⟨601847080770387914447149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802462774360517219262865 601847080770387914447149)
                      ·
                        rfl

theorem cell23_1172093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_1172093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172093 prefixEnd_1172093 := by exact prefixLift 1172093
  have htrace : WordTrace (prefixWord ++ tailWord_1172093) baseStart_1172093 baseEnd_1172093 := by
    simpa [prefixWord, tailWord_1172093, baseEnd_1172093] using wordTrace_append hprefix tailTrace_1172093
  have hstable : (prefixWord ++ tailWord_1172093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172093).length < 2 ^ (prefixWord ++ tailWord_1172093).sum := by decide
  have hdescent : baseEnd_1172093 < baseStart_1172093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172119 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_1172119 : Nat := 118140960795 + 1172119 * 2 ^ 59
def prefixEnd_1172119 : Nat := 4983230072969 + 3 ^ 40 * 1172119 * 2
def baseEnd_1172119 : Nat := 601860431267404812722029

theorem tailTrace_1172119 : CollatzResearch.WordTrace tailWord_1172119 prefixEnd_1172119 601860431267404812722029 := by
  unfold tailWord_1172119
  simp only [CollatzResearch.WordTrace]
  refine ⟨42750692040620519833007411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28500461360413679888671607 42750692040620519833007411)
  ·
    refine ⟨64126038060930779749511117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42750692040620519833007411 64126038060930779749511117)
    ·
      refine ⟨24047264272849042406066669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64126038060930779749511117 24047264272849042406066669)
      ·
        refine ⟨9017724102318390902275001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24047264272849042406066669 9017724102318390902275001)
        ·
          refine ⟨6763293076738793176706251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9017724102318390902275001 6763293076738793176706251)
          ·
            refine ⟨10144939615108189765059377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6763293076738793176706251 10144939615108189765059377)
            ·
              refine ⟨7608704711331142323794533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10144939615108189765059377 7608704711331142323794533)
              ·
                refine ⟨1426632133374589185711475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7608704711331142323794533 1426632133374589185711475)
                ·
                  refine ⟨2139948200061883778567213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426632133374589185711475 2139948200061883778567213)
                  ·
                    refine ⟨802480575023206416962705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139948200061883778567213 802480575023206416962705)
                    ·
                      refine ⟨601860431267404812722029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802480575023206416962705 601860431267404812722029)
                      ·
                        rfl

theorem cell23_1172119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_1172119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172119 prefixEnd_1172119 := by exact prefixLift 1172119
  have htrace : WordTrace (prefixWord ++ tailWord_1172119) baseStart_1172119 baseEnd_1172119 := by
    simpa [prefixWord, tailWord_1172119, baseEnd_1172119] using wordTrace_append hprefix tailTrace_1172119
  have hstable : (prefixWord ++ tailWord_1172119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172119).length < 2 ^ (prefixWord ++ tailWord_1172119).sum := by decide
  have hdescent : baseEnd_1172119 < baseStart_1172119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172172 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 7]
def baseStart_1172172 : Nat := 118140960795 + 1172172 * 2 ^ 59
def prefixEnd_1172172 : Nat := 4983230072969 + 3 ^ 40 * 1172172 * 2
def baseEnd_1172172 : Nat := 66876405082454789484365

theorem tailTrace_1172172 : CollatzResearch.WordTrace tailWord_1172172 prefixEnd_1172172 66876405082454789484365 := by
  unfold tailWord_1172172
  simp only [CollatzResearch.WordTrace]
  refine ⟨21376312554714254942343385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28501750072952339923124513 21376312554714254942343385)
  ·
    refine ⟨16032234416035691206757539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21376312554714254942343385 16032234416035691206757539)
    ·
      refine ⟨24048351624053536810136309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16032234416035691206757539 24048351624053536810136309)
      ·
        refine ⟨2254532964755019075950279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24048351624053536810136309 2254532964755019075950279)
        ·
          refine ⟨3381799447132528613925419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254532964755019075950279 3381799447132528613925419)
          ·
            refine ⟨5072699170698792920888129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381799447132528613925419 5072699170698792920888129)
            ·
              refine ⟨3804524378024094690666097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5072699170698792920888129 3804524378024094690666097)
              ·
                refine ⟨2853393283518071017999573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3804524378024094690666097 2853393283518071017999573)
                ·
                  refine ⟨66876405082454789484365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2853393283518071017999573 66876405082454789484365)
                  ·
                    rfl

theorem cell23_1172172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_1172172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172172 prefixEnd_1172172 := by exact prefixLift 1172172
  have htrace : WordTrace (prefixWord ++ tailWord_1172172) baseStart_1172172 baseEnd_1172172 := by
    simpa [prefixWord, tailWord_1172172, baseEnd_1172172] using wordTrace_append hprefix tailTrace_1172172
  have hstable : (prefixWord ++ tailWord_1172172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172172).length < 2 ^ (prefixWord ++ tailWord_1172172).sum := by decide
  have hdescent : baseEnd_1172172 < baseStart_1172172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172185 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_1172185 : Nat := 118140960795 + 1172185 * 2 ^ 59
def prefixEnd_1172185 : Nat := 4983230072969 + 3 ^ 40 * 1172185 * 2
def baseEnd_1172185 : Nat := 200631440330200518165575

theorem tailTrace_1172185 : CollatzResearch.WordTrace tailWord_1172185 prefixEnd_1172185 200631440330200518165575 := by
  unfold tailWord_1172185
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753099258381413104910009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28502066172254275403273339 42753099258381413104910009)
  ·
    refine ⟨32064824443786059828682507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42753099258381413104910009 32064824443786059828682507)
    ·
      refine ⟨48097236665679089743023761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32064824443786059828682507 48097236665679089743023761)
      ·
        refine ⟨36072927499259317307267821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48097236665679089743023761 36072927499259317307267821)
        ·
          refine ⟨13527347812222243990225433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36072927499259317307267821 13527347812222243990225433)
          ·
            refine ⟨10145510859166682992669075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13527347812222243990225433 10145510859166682992669075)
            ·
              refine ⟨15218266288750024489003613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145510859166682992669075 15218266288750024489003613)
              ·
                refine ⟨5706849858281259183376355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15218266288750024489003613 5706849858281259183376355)
                ·
                  refine ⟨8560274787421888775064533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706849858281259183376355 8560274787421888775064533)
                  ·
                    refine ⟨200631440330200518165575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8560274787421888775064533 200631440330200518165575)
                    ·
                      rfl

theorem cell23_1172185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_1172185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172185 prefixEnd_1172185 := by exact prefixLift 1172185
  have htrace : WordTrace (prefixWord ++ tailWord_1172185) baseStart_1172185 baseEnd_1172185 := by
    simpa [prefixWord, tailWord_1172185, baseEnd_1172185] using wordTrace_append hprefix tailTrace_1172185
  have hstable : (prefixWord ++ tailWord_1172185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172185).length < 2 ^ (prefixWord ++ tailWord_1172185).sum := by decide
  have hdescent : baseEnd_1172185 < baseStart_1172185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172192 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2]
def baseStart_1172192 : Nat := 118140960795 + 1172192 * 2 ^ 59
def prefixEnd_1172192 : Nat := 4983230072969 + 3 ^ 40 * 1172192 * 2
def baseEnd_1172192 : Nat := 601897915355183027109193

theorem tailTrace_1172192 : CollatzResearch.WordTrace tailWord_1172192 prefixEnd_1172192 601897915355183027109193 := by
  unfold tailWord_1172192
  simp only [CollatzResearch.WordTrace]
  refine ⟨21376677284678026650207415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28502236379570702200276553 21376677284678026650207415)
  ·
    refine ⟨32065015927017039975311123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21376677284678026650207415 32065015927017039975311123)
    ·
      refine ⟨48097523890525559962966685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32065015927017039975311123 48097523890525559962966685)
      ·
        refine ⟨18036571458947084986112507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48097523890525559962966685 18036571458947084986112507)
        ·
          refine ⟨27054857188420627479168761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18036571458947084986112507 27054857188420627479168761)
          ·
            refine ⟨20291142891315470609376571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27054857188420627479168761 20291142891315470609376571)
            ·
              refine ⟨30436714336973205914064857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291142891315470609376571 30436714336973205914064857)
              ·
                refine ⟨22827535752729904435548643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30436714336973205914064857 22827535752729904435548643)
                ·
                  refine ⟨34241303629094856653322965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22827535752729904435548643 34241303629094856653322965)
                  ·
                    refine ⟨802530553806910702812257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34241303629094856653322965 802530553806910702812257)
                    ·
                      refine ⟨601897915355183027109193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802530553806910702812257 601897915355183027109193)
                      ·
                        rfl

theorem cell23_1172192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_1172192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172192 prefixEnd_1172192 := by exact prefixLift 1172192
  have htrace : WordTrace (prefixWord ++ tailWord_1172192) baseStart_1172192 baseEnd_1172192 := by
    simpa [prefixWord, tailWord_1172192, baseEnd_1172192] using wordTrace_append hprefix tailTrace_1172192
  have hstable : (prefixWord ++ tailWord_1172192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172192).length < 2 ^ (prefixWord ++ tailWord_1172192).sum := by decide
  have hdescent : baseEnd_1172192 < baseStart_1172192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172206 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_1172206 : Nat := 118140960795 + 1172206 * 2 ^ 59
def prefixEnd_1172206 : Nat := 4983230072969 + 3 ^ 40 * 1172206 * 2
def baseEnd_1172206 : Nat := 66878344898260663592681

theorem tailTrace_1172206 : CollatzResearch.WordTrace tailWord_1172206 prefixEnd_1172206 66878344898260663592681 := by
  unfold tailWord_1172206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344233148913166711428059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28502576794203555794282981 5344233148913166711428059)
  ·
    refine ⟨8016349723369750067142089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344233148913166711428059 8016349723369750067142089)
    ·
      refine ⟨6012262292527312550356567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8016349723369750067142089 6012262292527312550356567)
      ·
        refine ⟨9018393438790968825534851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012262292527312550356567 9018393438790968825534851)
        ·
          refine ⟨13527590158186453238302277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018393438790968825534851 13527590158186453238302277)
          ·
            refine ⟨2536423154659959982181677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13527590158186453238302277 2536423154659959982181677)
            ·
              refine ⟨951158682997484993318129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2536423154659959982181677 951158682997484993318129)
              ·
                refine ⟨713369012248113744988597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951158682997484993318129 713369012248113744988597)
                ·
                  refine ⟨66878344898260663592681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 713369012248113744988597 66878344898260663592681)
                  ·
                    rfl

theorem cell23_1172206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_1172206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172206 prefixEnd_1172206 := by exact prefixLift 1172206
  have htrace : WordTrace (prefixWord ++ tailWord_1172206) baseStart_1172206 baseEnd_1172206 := by
    simpa [prefixWord, tailWord_1172206, baseEnd_1172206] using wordTrace_append hprefix tailTrace_1172206
  have hstable : (prefixWord ++ tailWord_1172206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172206).length < 2 ^ (prefixWord ++ tailWord_1172206).sum := by decide
  have hdescent : baseEnd_1172206 < baseStart_1172206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172235 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_1172235 : Nat := 118140960795 + 1172235 * 2 ^ 59
def prefixEnd_1172235 : Nat := 4983230072969 + 3 ^ 40 * 1172235 * 2
def baseEnd_1172235 : Nat := 601919995023326358871495

theorem tailTrace_1172235 : CollatzResearch.WordTrace tailWord_1172235 prefixEnd_1172235 601919995023326358871495 := by
  unfold tailWord_1172235
  simp only [CollatzResearch.WordTrace]
  refine ⟨42754922908200271644230159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28503281938800181096153439 42754922908200271644230159)
  ·
    refine ⟨64132384362300407466345239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42754922908200271644230159 64132384362300407466345239)
    ·
      refine ⟨96198576543450611199517859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64132384362300407466345239 96198576543450611199517859)
      ·
        refine ⟨144297864815175916799276789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96198576543450611199517859 144297864815175916799276789)
        ·
          refine ⟨13527924826422742199932199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144297864815175916799276789 13527924826422742199932199)
          ·
            refine ⟨20291887239634113299898299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13527924826422742199932199 20291887239634113299898299)
            ·
              refine ⟨30437830859451169949847449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20291887239634113299898299 30437830859451169949847449)
              ·
                refine ⟨22828373144588377462385587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30437830859451169949847449 22828373144588377462385587)
                ·
                  refine ⟨34242559716882566193578381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22828373144588377462385587 34242559716882566193578381)
                  ·
                    refine ⟨12840959893830962322591893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34242559716882566193578381 12840959893830962322591893)
                    ·
                      refine ⟨601919995023326358871495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12840959893830962322591893 601919995023326358871495)
                      ·
                        rfl

theorem cell23_1172235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_1172235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172235 prefixEnd_1172235 := by exact prefixLift 1172235
  have htrace : WordTrace (prefixWord ++ tailWord_1172235) baseStart_1172235 baseEnd_1172235 := by
    simpa [prefixWord, tailWord_1172235, baseEnd_1172235] using wordTrace_append hprefix tailTrace_1172235
  have hstable : (prefixWord ++ tailWord_1172235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172235).length < 2 ^ (prefixWord ++ tailWord_1172235).sum := by decide
  have hdescent : baseEnd_1172235 < baseStart_1172235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172265 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_1172265 : Nat := 118140960795 + 1172265 * 2 ^ 59
def prefixEnd_1172265 : Nat := 4983230072969 + 3 ^ 40 * 1172265 * 2
def baseEnd_1172265 : Nat := 601935399442961241496357

theorem tailTrace_1172265 : CollatzResearch.WordTrace tailWord_1172265 prefixEnd_1172265 601935399442961241496357 := by
  unfold tailWord_1172265
  simp only [CollatzResearch.WordTrace]
  refine ⟨42756017098091586767822249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28504011398727724511881499 42756017098091586767822249)
  ·
    refine ⟨32067012823568690075866687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42756017098091586767822249 32067012823568690075866687)
    ·
      refine ⟨48100519235353035113800031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32067012823568690075866687 48100519235353035113800031)
      ·
        refine ⟨72150778853029552670700047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48100519235353035113800031 72150778853029552670700047)
        ·
          refine ⟨108226168279544329006050071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72150778853029552670700047 108226168279544329006050071)
          ·
            refine ⟨162339252419316493509075107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108226168279544329006050071 162339252419316493509075107)
            ·
              refine ⟨243508878628974740263612661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162339252419316493509075107 243508878628974740263612661)
              ·
                refine ⟨22828957371466381899713687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 243508878628974740263612661 22828957371466381899713687)
                ·
                  refine ⟨34243436057199572849570531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22828957371466381899713687 34243436057199572849570531)
                  ·
                    refine ⟨51365154085799359274355797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34243436057199572849570531 51365154085799359274355797)
                    ·
                      refine ⟨601935399442961241496357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 51365154085799359274355797 601935399442961241496357)
                      ·
                        rfl

theorem cell23_1172265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_1172265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172265 prefixEnd_1172265 := by exact prefixLift 1172265
  have htrace : WordTrace (prefixWord ++ tailWord_1172265) baseStart_1172265 baseEnd_1172265 := by
    simpa [prefixWord, tailWord_1172265, baseEnd_1172265] using wordTrace_append hprefix tailTrace_1172265
  have hstable : (prefixWord ++ tailWord_1172265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172265).length < 2 ^ (prefixWord ++ tailWord_1172265).sum := by decide
  have hdescent : baseEnd_1172265 < baseStart_1172265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172309 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1172309 : Nat := 118140960795 + 1172309 * 2 ^ 59
def prefixEnd_1172309 : Nat := 4983230072969 + 3 ^ 40 * 1172309 * 2
def baseEnd_1172309 : Nat := 200652664197253023115385

theorem tailTrace_1172309 : CollatzResearch.WordTrace tailWord_1172309 prefixEnd_1172309 200652664197253023115385 := by
  unfold tailWord_1172309
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757621909932182282423981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28505081273288121521615987 42757621909932182282423981)
  ·
    refine ⟨16034108216224568355908993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42757621909932182282423981 16034108216224568355908993)
    ·
      refine ⟨12025581162168426266931745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16034108216224568355908993 12025581162168426266931745)
      ·
        refine ⟨9019185871626319700198809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12025581162168426266931745 9019185871626319700198809)
        ·
          refine ⟨6764389403719739775149107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9019185871626319700198809 6764389403719739775149107)
          ·
            refine ⟨10146584105579609662723661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6764389403719739775149107 10146584105579609662723661)
            ·
              refine ⟨3804969039592353623521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10146584105579609662723661 3804969039592353623521373)
              ·
                refine ⟨1426863389847132608820515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3804969039592353623521373 1426863389847132608820515)
                ·
                  refine ⟨2140295084770698913230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426863389847132608820515 2140295084770698913230773)
                  ·
                    refine ⟨200652664197253023115385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2140295084770698913230773 200652664197253023115385)
                    ·
                      rfl

theorem cell23_1172309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1172309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172309 prefixEnd_1172309 := by exact prefixLift 1172309
  have htrace : WordTrace (prefixWord ++ tailWord_1172309) baseStart_1172309 baseEnd_1172309 := by
    simpa [prefixWord, tailWord_1172309, baseEnd_1172309] using wordTrace_append hprefix tailTrace_1172309
  have hstable : (prefixWord ++ tailWord_1172309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172309).length < 2 ^ (prefixWord ++ tailWord_1172309).sum := by decide
  have hdescent : baseEnd_1172309 < baseStart_1172309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172323 : List Nat := [1, 1, 1, 5, 3, 1, 2, 4, 1, 1, 3]
def baseStart_1172323 : Nat := 118140960795 + 1172323 * 2 ^ 59
def prefixEnd_1172323 : Nat := 4983230072969 + 3 ^ 40 * 1172323 * 2
def baseEnd_1172323 : Nat := 601965181320922014571091

theorem tailTrace_1172323 : CollatzResearch.WordTrace tailWord_1172323 prefixEnd_1172323 601965181320922014571091 := by
  unfold tailWord_1172323
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758132531881462673433623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28505421687920975115622415 42758132531881462673433623)
  ·
    refine ⟨64137198797822194010150435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42758132531881462673433623 64137198797822194010150435)
    ·
      refine ⟨96205798196733291015225653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64137198797822194010150435 96205798196733291015225653)
      ·
        refine ⟨9019293580943746032677405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96205798196733291015225653 9019293580943746032677405)
        ·
          refine ⟨3382235092853904762254027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9019293580943746032677405 3382235092853904762254027)
          ·
            refine ⟨5073352639280857143381041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382235092853904762254027 5073352639280857143381041)
            ·
              refine ⟨3805014479460642857535781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073352639280857143381041 3805014479460642857535781)
              ·
                refine ⟨713440214898870535787959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3805014479460642857535781 713440214898870535787959)
                ·
                  refine ⟨1070160322348305803681939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713440214898870535787959 1070160322348305803681939)
                  ·
                    refine ⟨1605240483522458705522909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070160322348305803681939 1605240483522458705522909)
                    ·
                      refine ⟨601965181320922014571091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1605240483522458705522909 601965181320922014571091)
                      ·
                        rfl

theorem cell23_1172323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_1172323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172323 prefixEnd_1172323 := by exact prefixLift 1172323
  have htrace : WordTrace (prefixWord ++ tailWord_1172323) baseStart_1172323 baseEnd_1172323 := by
    simpa [prefixWord, tailWord_1172323, baseEnd_1172323] using wordTrace_append hprefix tailTrace_1172323
  have hstable : (prefixWord ++ tailWord_1172323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172323).length < 2 ^ (prefixWord ++ tailWord_1172323).sum := by decide
  have hdescent : baseEnd_1172323 < baseStart_1172323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172339 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 2, 4]
def baseStart_1172339 : Nat := 118140960795 + 1172339 * 2 ^ 59
def prefixEnd_1172339 : Nat := 4983230072969 + 3 ^ 40 * 1172339 * 2
def baseEnd_1172339 : Nat := 200657799003797983990339

theorem tailTrace_1172339 : CollatzResearch.WordTrace tailWord_1172339 prefixEnd_1172339 200657799003797983990339 := by
  unfold tailWord_1172339
  simp only [CollatzResearch.WordTrace]
  refine ⟨42758716099823497406016071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28505810733215664937344047 42758716099823497406016071)
  ·
    refine ⟨64138074149735246109024107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42758716099823497406016071 64138074149735246109024107)
    ·
      refine ⟨96207111224602869163536161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64138074149735246109024107 96207111224602869163536161)
      ·
        refine ⟨72155333418452151872652121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96207111224602869163536161 72155333418452151872652121)
        ·
          refine ⟨54116500063839113904489091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72155333418452151872652121 54116500063839113904489091)
          ·
            refine ⟨81174750095758670856733637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54116500063839113904489091 81174750095758670856733637)
            ·
              refine ⟨15220265642954750785637557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81174750095758670856733637 15220265642954750785637557)
              ·
                refine ⟨1426899904027007886153521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15220265642954750785637557 1426899904027007886153521)
                ·
                  refine ⟨1070174928020255914615141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426899904027007886153521 1070174928020255914615141)
                  ·
                    refine ⟨200657799003797983990339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070174928020255914615141 200657799003797983990339)
                    ·
                      rfl

theorem cell23_1172339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 4].length) (baseStart_1172339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172339 prefixEnd_1172339 := by exact prefixLift 1172339
  have htrace : WordTrace (prefixWord ++ tailWord_1172339) baseStart_1172339 baseEnd_1172339 := by
    simpa [prefixWord, tailWord_1172339, baseEnd_1172339] using wordTrace_append hprefix tailTrace_1172339
  have hstable : (prefixWord ++ tailWord_1172339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172339).length < 2 ^ (prefixWord ++ tailWord_1172339).sum := by decide
  have hdescent : baseEnd_1172339 < baseStart_1172339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172349 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1172349 : Nat := 118140960795 + 1172349 * 2 ^ 59
def prefixEnd_1172349 : Nat := 4983230072969 + 3 ^ 40 * 1172349 * 2
def baseEnd_1172349 : Nat := 601978531817938912845971

theorem tailTrace_1172349 : CollatzResearch.WordTrace tailWord_1172349 prefixEnd_1172349 601978531817938912845971 := by
  unfold tailWord_1172349
  simp only [CollatzResearch.WordTrace]
  refine ⟨42759080829787269113880101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28506053886524846075920067 42759080829787269113880101)
  ·
    refine ⟨8017327655585112958852519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42759080829787269113880101 8017327655585112958852519)
    ·
      refine ⟨12025991483377669438278779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017327655585112958852519 12025991483377669438278779)
      ·
        refine ⟨18038987225066504157418169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025991483377669438278779 18038987225066504157418169)
        ·
          refine ⟨13529240418799878118063627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18038987225066504157418169 13529240418799878118063627)
          ·
            refine ⟨20293860628199817177095441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13529240418799878118063627 20293860628199817177095441)
            ·
              refine ⟨15220395471149862882821581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20293860628199817177095441 15220395471149862882821581)
              ·
                refine ⟨5707648301681198581058093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15220395471149862882821581 5707648301681198581058093)
                ·
                  refine ⟨2140368113130449467896785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5707648301681198581058093 2140368113130449467896785)
                  ·
                    refine ⟨1605276084847837100922589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140368113130449467896785 1605276084847837100922589)
                    ·
                      refine ⟨601978531817938912845971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1605276084847837100922589 601978531817938912845971)
                      ·
                        rfl

theorem cell23_1172349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1172349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172349 prefixEnd_1172349 := by exact prefixLift 1172349
  have htrace : WordTrace (prefixWord ++ tailWord_1172349) baseStart_1172349 baseEnd_1172349 := by
    simpa [prefixWord, tailWord_1172349, baseEnd_1172349] using wordTrace_append hprefix tailTrace_1172349
  have hstable : (prefixWord ++ tailWord_1172349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172349).length < 2 ^ (prefixWord ++ tailWord_1172349).sum := by decide
  have hdescent : baseEnd_1172349 < baseStart_1172349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172389 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_1172389 : Nat := 118140960795 + 1172389 * 2 ^ 59
def prefixEnd_1172389 : Nat := 4983230072969 + 3 ^ 40 * 1172389 * 2
def baseEnd_1172389 : Nat := 601999071044118756345787

theorem tailTrace_1172389 : CollatzResearch.WordTrace tailWord_1172389 prefixEnd_1172389 601999071044118756345787 := by
  unfold tailWord_1172389
  simp only [CollatzResearch.WordTrace]
  refine ⟨42760539749642355945336221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28507026499761570630224147 42760539749642355945336221)
  ·
    refine ⟨16035202406115883479501083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42760539749642355945336221 16035202406115883479501083)
    ·
      refine ⟨24052803609173825219251625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035202406115883479501083 24052803609173825219251625)
      ·
        refine ⟨18039602706880368914438719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24052803609173825219251625 18039602706880368914438719)
        ·
          refine ⟨27059404060320553371658079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18039602706880368914438719 27059404060320553371658079)
          ·
            refine ⟨40589106090480830057487119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27059404060320553371658079 40589106090480830057487119)
            ·
              refine ⟨60883659135721245086230679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40589106090480830057487119 60883659135721245086230679)
              ·
                refine ⟨91325488703581867629346019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60883659135721245086230679 91325488703581867629346019)
                ·
                  refine ⟨136988233055372801444019029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91325488703581867629346019 136988233055372801444019029)
                  ·
                    refine ⟨802665428058825008461049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 136988233055372801444019029 802665428058825008461049)
                    ·
                      refine ⟨601999071044118756345787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802665428058825008461049 601999071044118756345787)
                      ·
                        rfl

theorem cell23_1172389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_1172389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172389 prefixEnd_1172389 := by exact prefixLift 1172389
  have htrace : WordTrace (prefixWord ++ tailWord_1172389) baseStart_1172389 baseEnd_1172389 := by
    simpa [prefixWord, tailWord_1172389, baseEnd_1172389] using wordTrace_append hprefix tailTrace_1172389
  have hstable : (prefixWord ++ tailWord_1172389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172389).length < 2 ^ (prefixWord ++ tailWord_1172389).sum := by decide
  have hdescent : baseEnd_1172389 < baseStart_1172389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172396 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_1172396 : Nat := 118140960795 + 1172396 * 2 ^ 59
def prefixEnd_1172396 : Nat := 4983230072969 + 3 ^ 40 * 1172396 * 2
def baseEnd_1172396 : Nat := 602002665408700228958255

theorem tailTrace_1172396 : CollatzResearch.WordTrace tailWord_1172396 prefixEnd_1172396 602002665408700228958255 := by
  unfold tailWord_1172396
  simp only [CollatzResearch.WordTrace]
  refine ⟨21380397530308498070420521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28507196707077997427227361 21380397530308498070420521)
  ·
    refine ⟨16035298147731373552815391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21380397530308498070420521 16035298147731373552815391)
    ·
      refine ⟨24052947221597060329223087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035298147731373552815391 24052947221597060329223087)
      ·
        refine ⟨36079420832395590493834631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24052947221597060329223087 36079420832395590493834631)
        ·
          refine ⟨54119131248593385740751947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36079420832395590493834631 54119131248593385740751947)
          ·
            refine ⟨81178696872890078611127921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54119131248593385740751947 81178696872890078611127921)
            ·
              refine ⟨60884022654667558958345941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81178696872890078611127921 60884022654667558958345941)
              ·
                refine ⟨1426969280968770913086233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60884022654667558958345941 1426969280968770913086233)
                ·
                  refine ⟨1070226960726578184814675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426969280968770913086233 1070226960726578184814675)
                  ·
                    refine ⟨1605340441089867277222013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070226960726578184814675 1605340441089867277222013)
                    ·
                      refine ⟨602002665408700228958255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1605340441089867277222013 602002665408700228958255)
                      ·
                        rfl

theorem cell23_1172396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_1172396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172396 prefixEnd_1172396 := by exact prefixLift 1172396
  have htrace : WordTrace (prefixWord ++ tailWord_1172396) baseStart_1172396 baseEnd_1172396 := by
    simpa [prefixWord, tailWord_1172396, baseEnd_1172396] using wordTrace_append hprefix tailTrace_1172396
  have hstable : (prefixWord ++ tailWord_1172396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172396).length < 2 ^ (prefixWord ++ tailWord_1172396).sum := by decide
  have hdescent : baseEnd_1172396 < baseStart_1172396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172397 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1172397 : Nat := 118140960795 + 1172397 * 2 ^ 59
def prefixEnd_1172397 : Nat := 4983230072969 + 3 ^ 40 * 1172397 * 2
def baseEnd_1172397 : Nat := 602003178889354725045751

theorem tailTrace_1172397 : CollatzResearch.WordTrace tailWord_1172397 prefixEnd_1172397 602003178889354725045751 := by
  unfold tailWord_1172397
  simp only [CollatzResearch.WordTrace]
  refine ⟨42760831533613373311627445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28507221022408915541084963 42760831533613373311627445)
  ·
    refine ⟨4008827956276253747965073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42760831533613373311627445 4008827956276253747965073)
    ·
      refine ⟨3006620967207190310973805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008827956276253747965073 3006620967207190310973805)
      ·
        refine ⟨1127482862702696366615177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3006620967207190310973805 1127482862702696366615177)
        ·
          refine ⟨845612147027022274961383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127482862702696366615177 845612147027022274961383)
          ·
            refine ⟨1268418220540533412442075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845612147027022274961383 1268418220540533412442075)
            ·
              refine ⟨1902627330810800118663113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268418220540533412442075 1902627330810800118663113)
              ·
                refine ⟨1426970498108100088997335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902627330810800118663113 1426970498108100088997335)
                ·
                  refine ⟨2140455747162150133496003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426970498108100088997335 2140455747162150133496003)
                  ·
                    refine ⟨3210683620743225200244005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2140455747162150133496003 3210683620743225200244005)
                    ·
                      refine ⟨602003178889354725045751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3210683620743225200244005 602003178889354725045751)
                      ·
                        rfl

theorem cell23_1172397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1172397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172397 prefixEnd_1172397 := by exact prefixLift 1172397
  have htrace : WordTrace (prefixWord ++ tailWord_1172397) baseStart_1172397 baseEnd_1172397 := by
    simpa [prefixWord, tailWord_1172397, baseEnd_1172397] using wordTrace_append hprefix tailTrace_1172397
  have hstable : (prefixWord ++ tailWord_1172397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172397).length < 2 ^ (prefixWord ++ tailWord_1172397).sum := by decide
  have hdescent : baseEnd_1172397 < baseStart_1172397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172402 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1172402 : Nat := 118140960795 + 1172402 * 2 ^ 59
def prefixEnd_1172402 : Nat := 4983230072969 + 3 ^ 40 * 1172402 * 2
def baseEnd_1172402 : Nat := 602005746292627205483227

theorem tailTrace_1172402 : CollatzResearch.WordTrace tailWord_1172402 prefixEnd_1172402 602005746292627205483227 := by
  unfold tailWord_1172402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10690253474648814791389865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28507342599063506110372973 10690253474648814791389865)
  ·
    refine ⟨8017690105986611093542399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10690253474648814791389865 8017690105986611093542399)
    ·
      refine ⟨12026535158979916640313599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017690105986611093542399 12026535158979916640313599)
      ·
        refine ⟨18039802738469874960470399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12026535158979916640313599 18039802738469874960470399)
        ·
          refine ⟨27059704107704812440705599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18039802738469874960470399 27059704107704812440705599)
          ·
            refine ⟨40589556161557218661058399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27059704107704812440705599 40589556161557218661058399)
            ·
              refine ⟨60884334242335827991587599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40589556161557218661058399 60884334242335827991587599)
              ·
                refine ⟨91326501363503741987381399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60884334242335827991587599 91326501363503741987381399)
                ·
                  refine ⟨136989752045255612981072099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91326501363503741987381399 136989752045255612981072099)
                  ·
                    refine ⟨205484628067883419471608149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136989752045255612981072099 205484628067883419471608149)
                    ·
                      refine ⟨602005746292627205483227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 205484628067883419471608149 602005746292627205483227)
                      ·
                        rfl

theorem cell23_1172402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1172402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172402 prefixEnd_1172402 := by exact prefixLift 1172402
  have htrace : WordTrace (prefixWord ++ tailWord_1172402) baseStart_1172402 baseEnd_1172402 := by
    simpa [prefixWord, tailWord_1172402, baseEnd_1172402] using wordTrace_append hprefix tailTrace_1172402
  have hstable : (prefixWord ++ tailWord_1172402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172402).length < 2 ^ (prefixWord ++ tailWord_1172402).sum := by decide
  have hdescent : baseEnd_1172402 < baseStart_1172402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172432 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1172432 : Nat := 118140960795 + 1172432 * 2 ^ 59
def prefixEnd_1172432 : Nat := 4983230072969 + 3 ^ 40 * 1172432 * 2
def baseEnd_1172432 : Nat := 602021150712262088108089

theorem tailTrace_1172432 : CollatzResearch.WordTrace tailWord_1172432 prefixEnd_1172432 602021150712262088108089 := by
  unfold tailWord_1172432
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381054044243287144575775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28508072058991049526101033 21381054044243287144575775)
  ·
    refine ⟨32071581066364930716863663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21381054044243287144575775 32071581066364930716863663)
    ·
      refine ⟨48107371599547396075295495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32071581066364930716863663 48107371599547396075295495)
      ·
        refine ⟨72161057399321094112943243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48107371599547396075295495 72161057399321094112943243)
        ·
          refine ⟨108241586098981641169414865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72161057399321094112943243 108241586098981641169414865)
          ·
            refine ⟨81181189574236230877061149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108241586098981641169414865 81181189574236230877061149)
            ·
              refine ⟨30442946090338586578897931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81181189574236230877061149 30442946090338586578897931)
              ·
                refine ⟨45664419135507879868346897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30442946090338586578897931 45664419135507879868346897)
                ·
                  refine ⟨34248314351630909901260173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45664419135507879868346897 34248314351630909901260173)
                  ·
                    refine ⟨12843117881861591212972565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34248314351630909901260173 12843117881861591212972565)
                    ·
                      refine ⟨602021150712262088108089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12843117881861591212972565 602021150712262088108089)
                      ·
                        rfl

theorem cell23_1172432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1172432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172432 prefixEnd_1172432 := by exact prefixLift 1172432
  have htrace : WordTrace (prefixWord ++ tailWord_1172432) baseStart_1172432 baseEnd_1172432 := by
    simpa [prefixWord, tailWord_1172432, baseEnd_1172432] using wordTrace_append hprefix tailTrace_1172432
  have hstable : (prefixWord ++ tailWord_1172432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172432).length < 2 ^ (prefixWord ++ tailWord_1172432).sum := by decide
  have hdescent : baseEnd_1172432 < baseStart_1172432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172468 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1172468 : Nat := 118140960795 + 1172468 * 2 ^ 59
def prefixEnd_1172468 : Nat := 4983230072969 + 3 ^ 40 * 1172468 * 2
def baseEnd_1172468 : Nat := 602039636015823947257925

theorem tailTrace_1172468 : CollatzResearch.WordTrace tailWord_1172468 prefixEnd_1172468 602039636015823947257925 := by
  unfold tailWord_1172468
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381710558178076218731029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28508947410904101624974705 21381710558178076218731029)
  ·
    refine ⟨1002267682414597322753017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21381710558178076218731029 1002267682414597322753017)
    ·
      refine ⟨751700761810947992064763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002267682414597322753017 751700761810947992064763)
      ·
        refine ⟨1127551142716421988097145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751700761810947992064763 1127551142716421988097145)
        ·
          refine ⟨845663357037316491072859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127551142716421988097145 845663357037316491072859)
          ·
            refine ⟨1268495035555974736609289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845663357037316491072859 1268495035555974736609289)
            ·
              refine ⟨951371276666981052456967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268495035555974736609289 951371276666981052456967)
              ·
                refine ⟨1427056915000471578685451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951371276666981052456967 1427056915000471578685451)
                ·
                  refine ⟨2140585372500707368028177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427056915000471578685451 2140585372500707368028177)
                  ·
                    refine ⟨1605439029375530526021133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2140585372500707368028177 1605439029375530526021133)
                    ·
                      refine ⟨602039636015823947257925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1605439029375530526021133 602039636015823947257925)
                      ·
                        rfl

theorem cell23_1172468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1172468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172468 prefixEnd_1172468 := by exact prefixLift 1172468
  have htrace : WordTrace (prefixWord ++ tailWord_1172468) baseStart_1172468 baseEnd_1172468 := by
    simpa [prefixWord, tailWord_1172468, baseEnd_1172468] using wordTrace_append hprefix tailTrace_1172468
  have hstable : (prefixWord ++ tailWord_1172468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172468).length < 2 ^ (prefixWord ++ tailWord_1172468).sum := by decide
  have hdescent : baseEnd_1172468 < baseStart_1172468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172476 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 5]
def baseStart_1172476 : Nat := 118140960795 + 1172476 * 2 ^ 59
def prefixEnd_1172476 : Nat := 4983230072969 + 3 ^ 40 * 1172476 * 2
def baseEnd_1172476 : Nat := 66893749317895546217543

theorem tailTrace_1172476 : CollatzResearch.WordTrace tailWord_1172476 prefixEnd_1172476 66893749317895546217543 := by
  unfold tailWord_1172476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21381856450163584901876641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28509141933551446535835521 21381856450163584901876641)
  ·
    refine ⟨16036392337622688676407481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21381856450163584901876641 16036392337622688676407481)
    ·
      refine ⟨12027294253217016507305611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16036392337622688676407481 12027294253217016507305611)
      ·
        refine ⟨18040941379825524760958417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12027294253217016507305611 18040941379825524760958417)
        ·
          refine ⟨13530706034869143570718813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18040941379825524760958417 13530706034869143570718813)
          ·
            refine ⟨5074014763075928839019555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13530706034869143570718813 5074014763075928839019555)
            ·
              refine ⟨7611022144613893258529333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074014763075928839019555 7611022144613893258529333)
              ·
                refine ⟨713533326057552492987125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7611022144613893258529333 713533326057552492987125)
                ·
                  refine ⟨66893749317895546217543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 713533326057552492987125 66893749317895546217543)
                  ·
                    rfl

theorem cell23_1172476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_1172476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172476 prefixEnd_1172476 := by exact prefixLift 1172476
  have htrace : WordTrace (prefixWord ++ tailWord_1172476) baseStart_1172476 baseEnd_1172476 := by
    simpa [prefixWord, tailWord_1172476, baseEnd_1172476] using wordTrace_append hprefix tailTrace_1172476
  have hstable : (prefixWord ++ tailWord_1172476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172476).length < 2 ^ (prefixWord ++ tailWord_1172476).sum := by decide
  have hdescent : baseEnd_1172476 < baseStart_1172476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172489 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_1172489 : Nat := 118140960795 + 1172489 * 2 ^ 59
def prefixEnd_1172489 : Nat := 4983230072969 + 3 ^ 40 * 1172489 * 2
def baseEnd_1172489 : Nat := 200683473036522788365109

theorem tailTrace_1172489 : CollatzResearch.WordTrace tailWord_1172489 prefixEnd_1172489 200683473036522788365109 := by
  unfold tailWord_1172489
  simp only [CollatzResearch.WordTrace]
  refine ⟨42764187049280073023976521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28509458032853382015984347 42764187049280073023976521)
  ·
    refine ⟨32073140286960054767982391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42764187049280073023976521 32073140286960054767982391)
    ·
      refine ⟨48109710430440082151973587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32073140286960054767982391 48109710430440082151973587)
      ·
        refine ⟨72164565645660123227960381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48109710430440082151973587 72164565645660123227960381)
        ·
          refine ⟨27061712117122546210485143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72164565645660123227960381 27061712117122546210485143)
          ·
            refine ⟨40592568175683819315727715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27061712117122546210485143 40592568175683819315727715)
            ·
              refine ⟨60888852263525728973591573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40592568175683819315727715 60888852263525728973591573)
              ·
                refine ⟨2854164949852768545637105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60888852263525728973591573 2854164949852768545637105)
                ·
                  refine ⟨2140623712389576409227829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854164949852768545637105 2140623712389576409227829)
                  ·
                    refine ⟨200683473036522788365109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2140623712389576409227829 200683473036522788365109)
                    ·
                      rfl

theorem cell23_1172489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_1172489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172489 prefixEnd_1172489 := by exact prefixLift 1172489
  have htrace : WordTrace (prefixWord ++ tailWord_1172489) baseStart_1172489 baseEnd_1172489 := by
    simpa [prefixWord, tailWord_1172489, baseEnd_1172489] using wordTrace_append hprefix tailTrace_1172489
  have hstable : (prefixWord ++ tailWord_1172489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172489).length < 2 ^ (prefixWord ++ tailWord_1172489).sum := by decide
  have hdescent : baseEnd_1172489 < baseStart_1172489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172526 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1172526 : Nat := 118140960795 + 1172526 * 2 ^ 59
def prefixEnd_1172526 : Nat := 4983230072969 + 3 ^ 40 * 1172526 * 2
def baseEnd_1172526 : Nat := 602069417893784720332657

theorem tailTrace_1172526 : CollatzResearch.WordTrace tailWord_1172526 prefixEnd_1172526 602069417893784720332657 := by
  unfold tailWord_1172526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345692068768253542884179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28510357700097352228715621 5345692068768253542884179)
  ·
    refine ⟨8018538103152380314326269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345692068768253542884179 8018538103152380314326269)
    ·
      refine ⟨3006951788682142617872351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8018538103152380314326269 3006951788682142617872351)
      ·
        refine ⟨4510427683023213926808527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006951788682142617872351 4510427683023213926808527)
        ·
          refine ⟨6765641524534820890212791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4510427683023213926808527 6765641524534820890212791)
          ·
            refine ⟨10148462286802231335319187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765641524534820890212791 10148462286802231335319187)
            ·
              refine ⟨15222693430203347002978781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10148462286802231335319187 15222693430203347002978781)
              ·
                refine ⟨5708510036326255126117043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15222693430203347002978781 5708510036326255126117043)
                ·
                  refine ⟨8562765054489382689175565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708510036326255126117043 8562765054489382689175565)
                  ·
                    refine ⟨3211036895433518508440837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8562765054489382689175565 3211036895433518508440837)
                    ·
                      refine ⟨602069417893784720332657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3211036895433518508440837 602069417893784720332657)
                      ·
                        rfl

theorem cell23_1172526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1172526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172526 prefixEnd_1172526 := by exact prefixLift 1172526
  have htrace : WordTrace (prefixWord ++ tailWord_1172526) baseStart_1172526 baseEnd_1172526 := by
    simpa [prefixWord, tailWord_1172526, baseEnd_1172526] using wordTrace_append hprefix tailTrace_1172526
  have hstable : (prefixWord ++ tailWord_1172526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172526).length < 2 ^ (prefixWord ++ tailWord_1172526).sum := by decide
  have hdescent : baseEnd_1172526 < baseStart_1172526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172549 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 8]
def baseStart_1172549 : Nat := 118140960795 + 1172549 * 2 ^ 59
def prefixEnd_1172549 : Nat := 4983230072969 + 3 ^ 40 * 1172549 * 2
def baseEnd_1172549 : Nat := 66897914216537570038339

theorem tailTrace_1172549 : CollatzResearch.WordTrace tailWord_1172549 prefixEnd_1172549 66897914216537570038339 := by
  unfold tailWord_1172549
  simp only [CollatzResearch.WordTrace]
  refine ⟨42766375429062703271160701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28510916952708468847440467 42766375429062703271160701)
  ·
    refine ⟨16037390785898513726685263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42766375429062703271160701 16037390785898513726685263)
    ·
      refine ⟨24056086178847770590027895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16037390785898513726685263 24056086178847770590027895)
      ·
        refine ⟨36084129268271655885041843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24056086178847770590027895 36084129268271655885041843)
        ·
          refine ⟨54126193902407483827562765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36084129268271655885041843 54126193902407483827562765)
          ·
            refine ⟨20297322713402806435336037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54126193902407483827562765 20297322713402806435336037)
            ·
              refine ⟨3805748008763026206625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20297322713402806435336037 3805748008763026206625507)
              ·
                refine ⟨5708622013144539309938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805748008763026206625507 5708622013144539309938261)
                ·
                  refine ⟨66897914216537570038339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5708622013144539309938261 66897914216537570038339)
                  ·
                    rfl

theorem cell23_1172549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_1172549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172549 prefixEnd_1172549 := by exact prefixLift 1172549
  have htrace : WordTrace (prefixWord ++ tailWord_1172549) baseStart_1172549 baseEnd_1172549 := by
    simpa [prefixWord, tailWord_1172549, baseEnd_1172549] using wordTrace_append hprefix tailTrace_1172549
  have hstable : (prefixWord ++ tailWord_1172549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172549).length < 2 ^ (prefixWord ++ tailWord_1172549).sum := by decide
  have hdescent : baseEnd_1172549 < baseStart_1172549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172647 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1172647 : Nat := 118140960795 + 1172647 * 2 ^ 59
def prefixEnd_1172647 : Nat := 4983230072969 + 3 ^ 40 * 1172647 * 2
def baseEnd_1172647 : Nat := 200710516350992915639867

theorem tailTrace_1172647 : CollatzResearch.WordTrace tailWord_1172647 prefixEnd_1172647 200710516350992915639867 := by
  unfold tailWord_1172647
  simp only [CollatzResearch.WordTrace]
  refine ⟨42769949782707666008228195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28513299855138444005485463 42769949782707666008228195)
  ·
    refine ⟨64154924674061499012342293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42769949782707666008228195 64154924674061499012342293)
    ·
      refine ⟨3007262094096632766203545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64154924674061499012342293 3007262094096632766203545)
      ·
        refine ⟨2255446570572474574652659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007262094096632766203545 2255446570572474574652659)
        ·
          refine ⟨3383169855858711861978989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255446570572474574652659 3383169855858711861978989)
          ·
            refine ⟨1268688695947016948242121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3383169855858711861978989 1268688695947016948242121)
            ·
              refine ⟨951516521960262711181591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1268688695947016948242121 951516521960262711181591)
              ·
                refine ⟨1427274782940394066772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951516521960262711181591 1427274782940394066772387)
                ·
                  refine ⟨2140912174410591100158581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427274782940394066772387 2140912174410591100158581)
                  ·
                    refine ⟨200710516350992915639867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2140912174410591100158581 200710516350992915639867)
                    ·
                      rfl

theorem cell23_1172647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1172647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172647 prefixEnd_1172647 := by exact prefixLift 1172647
  have htrace : WordTrace (prefixWord ++ tailWord_1172647) baseStart_1172647 baseEnd_1172647 := by
    simpa [prefixWord, tailWord_1172647, baseEnd_1172647] using wordTrace_append hprefix tailTrace_1172647
  have hstable : (prefixWord ++ tailWord_1172647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172647).length < 2 ^ (prefixWord ++ tailWord_1172647).sum := by decide
  have hdescent : baseEnd_1172647 < baseStart_1172647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172734 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_1172734 : Nat := 118140960795 + 1172734 * 2 ^ 59
def prefixEnd_1172734 : Nat := 4983230072969 + 3 ^ 40 * 1172734 * 2
def baseEnd_1172734 : Nat := 602176221869919906531701

theorem tailTrace_1172734 : CollatzResearch.WordTrace tailWord_1172734 prefixEnd_1172734 602176221869919906531701 := by
  unfold tailWord_1172734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346640366674059983330657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28515415288928319911096837 5346640366674059983330657)
  ·
    refine ⟨4009980275005544987497993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5346640366674059983330657 4009980275005544987497993)
    ·
      refine ⟨3007485206254158740623495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4009980275005544987497993 3007485206254158740623495)
      ·
        refine ⟨4511227809381238110935243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007485206254158740623495 4511227809381238110935243)
        ·
          refine ⟨6766841714071857166402865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511227809381238110935243 6766841714071857166402865)
          ·
            refine ⟨5075131285553892874802149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766841714071857166402865 5075131285553892874802149)
            ·
              refine ⟨951587116041354914025403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5075131285553892874802149 951587116041354914025403)
              ·
                refine ⟨1427380674062032371038105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951587116041354914025403 1427380674062032371038105)
                ·
                  refine ⟨1070535505546524278278579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1427380674062032371038105 1070535505546524278278579)
                  ·
                    refine ⟨1605803258319786417417869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070535505546524278278579 1605803258319786417417869)
                    ·
                      refine ⟨602176221869919906531701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1605803258319786417417869 602176221869919906531701)
                      ·
                        rfl

theorem cell23_1172734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_1172734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172734 prefixEnd_1172734 := by exact prefixLift 1172734
  have htrace : WordTrace (prefixWord ++ tailWord_1172734) baseStart_1172734 baseEnd_1172734 := by
    simpa [prefixWord, tailWord_1172734, baseEnd_1172734] using wordTrace_append hprefix tailTrace_1172734
  have hstable : (prefixWord ++ tailWord_1172734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172734).length < 2 ^ (prefixWord ++ tailWord_1172734).sum := by decide
  have hdescent : baseEnd_1172734 < baseStart_1172734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172736 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1172736 : Nat := 118140960795 + 1172736 * 2 ^ 59
def prefixEnd_1172736 : Nat := 4983230072969 + 3 ^ 40 * 1172736 * 2
def baseEnd_1172736 : Nat := 602177248831228898706691

theorem tailTrace_1172736 : CollatzResearch.WordTrace tailWord_1172736 prefixEnd_1172736 602177248831228898706691 := by
  unfold tailWord_1172736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386597939692617104109031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28515463919590156138812041 21386597939692617104109031)
  ·
    refine ⟨32079896909538925656163547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386597939692617104109031 32079896909538925656163547)
    ·
      refine ⟨48119845364308388484245321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32079896909538925656163547 48119845364308388484245321)
      ·
        refine ⟨36089884023231291363183991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48119845364308388484245321 36089884023231291363183991)
        ·
          refine ⟨54134826034846937044775987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36089884023231291363183991 54134826034846937044775987)
          ·
            refine ⟨81202239052270405567163981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54134826034846937044775987 81202239052270405567163981)
            ·
              refine ⟨30450839644601402087686493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81202239052270405567163981 30450839644601402087686493)
              ·
                refine ⟨11419064866725525782882435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30450839644601402087686493 11419064866725525782882435)
                ·
                  refine ⟨17128597300088288674323653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11419064866725525782882435 17128597300088288674323653)
                  ·
                    refine ⟨3211611993766554126435685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17128597300088288674323653 3211611993766554126435685)
                    ·
                      refine ⟨602177248831228898706691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3211611993766554126435685 602177248831228898706691)
                      ·
                        rfl

theorem cell23_1172736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1172736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172736 prefixEnd_1172736 := by exact prefixLift 1172736
  have htrace : WordTrace (prefixWord ++ tailWord_1172736) baseStart_1172736 baseEnd_1172736 := by
    simpa [prefixWord, tailWord_1172736, baseEnd_1172736] using wordTrace_append hprefix tailTrace_1172736
  have hstable : (prefixWord ++ tailWord_1172736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172736).length < 2 ^ (prefixWord ++ tailWord_1172736).sum := by decide
  have hdescent : baseEnd_1172736 < baseStart_1172736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172744 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_1172744 : Nat := 118140960795 + 1172744 * 2 ^ 59
def prefixEnd_1172744 : Nat := 4983230072969 + 3 ^ 40 * 1172744 * 2
def baseEnd_1172744 : Nat := 602181356676464867406655

theorem tailTrace_1172744 : CollatzResearch.WordTrace tailWord_1172744 prefixEnd_1172744 602181356676464867406655 := by
  unfold tailWord_1172744
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386743831678125787254643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28515658442237501049672857 21386743831678125787254643)
  ·
    refine ⟨32080115747517188680881965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386743831678125787254643 32080115747517188680881965)
    ·
      refine ⟨12030043405318945755330737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32080115747517188680881965 12030043405318945755330737)
      ·
        refine ⟨9022532553989209316498053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12030043405318945755330737 9022532553989209316498053)
        ·
          refine ⟨1691724853872976746843385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9022532553989209316498053 1691724853872976746843385)
          ·
            refine ⟨1268793640404732560132539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691724853872976746843385 1268793640404732560132539)
            ·
              refine ⟨1903190460607098840198809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268793640404732560132539 1903190460607098840198809)
              ·
                refine ⟨1427392845455324130149107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903190460607098840198809 1427392845455324130149107)
                ·
                  refine ⟨2141089268182986195223661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427392845455324130149107 2141089268182986195223661)
                  ·
                    refine ⟨802908475568619823208873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141089268182986195223661 802908475568619823208873)
                    ·
                      refine ⟨602181356676464867406655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 802908475568619823208873 602181356676464867406655)
                      ·
                        rfl

theorem cell23_1172744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_1172744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172744 prefixEnd_1172744 := by exact prefixLift 1172744
  have htrace : WordTrace (prefixWord ++ tailWord_1172744) baseStart_1172744 baseEnd_1172744 := by
    simpa [prefixWord, tailWord_1172744, baseEnd_1172744] using wordTrace_append hprefix tailTrace_1172744
  have hstable : (prefixWord ++ tailWord_1172744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172744).length < 2 ^ (prefixWord ++ tailWord_1172744).sum := by decide
  have hdescent : baseEnd_1172744 < baseStart_1172744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172746 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_1172746 : Nat := 118140960795 + 1172746 * 2 ^ 59
def prefixEnd_1172746 : Nat := 4983230072969 + 3 ^ 40 * 1172746 * 2
def baseEnd_1172746 : Nat := 66909153737530428842405

theorem tailTrace_1172746 : CollatzResearch.WordTrace tailWord_1172746 prefixEnd_1172746 66909153737530428842405 := by
  unfold tailWord_1172746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693390152337251479020523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28515707072899337277388061 10693390152337251479020523)
  ·
    refine ⟨16040085228505877218530785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10693390152337251479020523 16040085228505877218530785)
    ·
      refine ⟨12030063921379407913898089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16040085228505877218530785 12030063921379407913898089)
      ·
        refine ⟨9022547941034555935423567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12030063921379407913898089 9022547941034555935423567)
        ·
          refine ⟨13533821911551833903135351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022547941034555935423567 13533821911551833903135351)
          ·
            refine ⟨20300732867327750854703027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13533821911551833903135351 20300732867327750854703027)
            ·
              refine ⟨30451099300991626282054541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300732867327750854703027 30451099300991626282054541)
              ·
                refine ⟨11419162237871859855770453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30451099300991626282054541 11419162237871859855770453)
                ·
                  refine ⟨66909153737530428842405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11419162237871859855770453 66909153737530428842405)
                  ·
                    rfl

theorem cell23_1172746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_1172746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172746 prefixEnd_1172746 := by exact prefixLift 1172746
  have htrace : WordTrace (prefixWord ++ tailWord_1172746) baseStart_1172746 baseEnd_1172746 := by
    simpa [prefixWord, tailWord_1172746, baseEnd_1172746] using wordTrace_append hprefix tailTrace_1172746
  have hstable : (prefixWord ++ tailWord_1172746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172746).length < 2 ^ (prefixWord ++ tailWord_1172746).sum := by decide
  have hdescent : baseEnd_1172746 < baseStart_1172746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172763 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 5]
def baseStart_1172763 : Nat := 118140960795 + 1172763 * 2 ^ 59
def prefixEnd_1172763 : Nat := 4983230072969 + 3 ^ 40 * 1172763 * 2
def baseEnd_1172763 : Nat := 66910123645433365896563

theorem tailTrace_1172763 : CollatzResearch.WordTrace tailWord_1172763 prefixEnd_1172763 66910123645433365896563 := by
  unfold tailWord_1172763
  simp only [CollatzResearch.WordTrace]
  refine ⟨42774180650287417819450943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28516120433524945212967295 42774180650287417819450943)
  ·
    refine ⟨64161270975431126729176415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42774180650287417819450943 64161270975431126729176415)
    ·
      refine ⟨96241906463146690093764623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64161270975431126729176415 96241906463146690093764623)
      ·
        refine ⟨144362859694720035140646935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96241906463146690093764623 144362859694720035140646935)
        ·
          refine ⟨216544289542080052710970403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144362859694720035140646935 216544289542080052710970403)
          ·
            refine ⟨324816434313120079066455605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216544289542080052710970403 324816434313120079066455605)
            ·
              refine ⟨30451540716855007412480213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324816434313120079066455605 30451540716855007412480213)
              ·
                refine ⟨713707985551289236230005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30451540716855007412480213 713707985551289236230005)
                ·
                  refine ⟨66910123645433365896563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 713707985551289236230005 66910123645433365896563)
                  ·
                    rfl

theorem cell23_1172763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 5].length) (baseStart_1172763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172763 prefixEnd_1172763 := by exact prefixLift 1172763
  have htrace : WordTrace (prefixWord ++ tailWord_1172763) baseStart_1172763 baseEnd_1172763 := by
    simpa [prefixWord, tailWord_1172763, baseEnd_1172763] using wordTrace_append hprefix tailTrace_1172763
  have hstable : (prefixWord ++ tailWord_1172763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172763).length < 2 ^ (prefixWord ++ tailWord_1172763).sum := by decide
  have hdescent : baseEnd_1172763 < baseStart_1172763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172917 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1172917 : Nat := 118140960795 + 1172917 * 2 ^ 59
def prefixEnd_1172917 : Nat := 4983230072969 + 3 ^ 40 * 1172917 * 2
def baseEnd_1172917 : Nat := 200756729609897563514453

theorem tailTrace_1172917 : CollatzResearch.WordTrace tailWord_1172917 prefixEnd_1172917 200756729609897563514453 := by
  unfold tailWord_1172917
  simp only [CollatzResearch.WordTrace]
  refine ⟨42779797491729502120557005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28519864994486334747038003 42779797491729502120557005)
  ·
    refine ⟨16042424059398563295208877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42779797491729502120557005 16042424059398563295208877)
    ·
      refine ⟨6015909022274461235703329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16042424059398563295208877 6015909022274461235703329)
      ·
        refine ⟨4511931766705845926777497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6015909022274461235703329 4511931766705845926777497)
        ·
          refine ⟨3383948825029384445083123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4511931766705845926777497 3383948825029384445083123)
          ·
            refine ⟨5075923237544076667624685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383948825029384445083123 5075923237544076667624685)
            ·
              refine ⟨1903471214079028750359257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5075923237544076667624685 1903471214079028750359257)
              ·
                refine ⟨1427603410559271562769443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903471214079028750359257 1427603410559271562769443)
                ·
                  refine ⟨2141405115838907344154165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427603410559271562769443 2141405115838907344154165)
                  ·
                    refine ⟨200756729609897563514453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2141405115838907344154165 200756729609897563514453)
                    ·
                      rfl

theorem cell23_1172917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1172917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172917 prefixEnd_1172917 := by exact prefixLift 1172917
  have htrace : WordTrace (prefixWord ++ tailWord_1172917) baseStart_1172917 baseEnd_1172917 := by
    simpa [prefixWord, tailWord_1172917, baseEnd_1172917] using wordTrace_append hprefix tailTrace_1172917
  have hstable : (prefixWord ++ tailWord_1172917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172917).length < 2 ^ (prefixWord ++ tailWord_1172917).sum := by decide
  have hdescent : baseEnd_1172917 < baseStart_1172917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172920 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_1172920 : Nat := 118140960795 + 1172920 * 2 ^ 59
def prefixEnd_1172920 : Nat := 4983230072969 + 3 ^ 40 * 1172920 * 2
def baseEnd_1172920 : Nat := 602271729271656178805845

theorem tailTrace_1172920 : CollatzResearch.WordTrace tailWord_1172920 prefixEnd_1172920 602271729271656178805845 := by
  unfold tailWord_1172920
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389953455359316816458107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28519937940479089088610809 21389953455359316816458107)
  ·
    refine ⟨32084930183038975224687161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21389953455359316816458107 32084930183038975224687161)
    ·
      refine ⟨24063697637279231418515371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32084930183038975224687161 24063697637279231418515371)
      ·
        refine ⟨36095546455918847127773057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24063697637279231418515371 36095546455918847127773057)
        ·
          refine ⟨27071659841939135345829793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36095546455918847127773057 27071659841939135345829793)
          ·
            refine ⟨20303744881454351509372345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27071659841939135345829793 20303744881454351509372345)
            ·
              refine ⟨15227808661090763632029259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20303744881454351509372345 15227808661090763632029259)
              ·
                refine ⟨22841712991636145448043889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15227808661090763632029259 22841712991636145448043889)
                ·
                  refine ⟨17131284743727109086032917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22841712991636145448043889 17131284743727109086032917)
                  ·
                    refine ⟨803028972362208238407793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17131284743727109086032917 803028972362208238407793)
                    ·
                      refine ⟨602271729271656178805845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803028972362208238407793 602271729271656178805845)
                      ·
                        rfl

theorem cell23_1172920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_1172920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172920 prefixEnd_1172920 := by exact prefixLift 1172920
  have htrace : WordTrace (prefixWord ++ tailWord_1172920) baseStart_1172920 baseEnd_1172920 := by
    simpa [prefixWord, tailWord_1172920, baseEnd_1172920] using wordTrace_append hprefix tailTrace_1172920
  have hstable : (prefixWord ++ tailWord_1172920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172920).length < 2 ^ (prefixWord ++ tailWord_1172920).sum := by decide
  have hdescent : baseEnd_1172920 < baseStart_1172920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172957 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1172957 : Nat := 118140960795 + 1172957 * 2 ^ 59
def prefixEnd_1172957 : Nat := 4983230072969 + 3 ^ 40 * 1172957 * 2
def baseEnd_1172957 : Nat := 602290728055872534043175

theorem tailTrace_1172957 : CollatzResearch.WordTrace tailWord_1172957 prefixEnd_1172957 602290728055872534043175 := by
  unfold tailWord_1172957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42781256411584588952013125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28520837607723059301342083 42781256411584588952013125)
  ·
    refine ⟨8021485577172110428502461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42781256411584588952013125 8021485577172110428502461)
    ·
      refine ⟨3008057091439541410688423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8021485577172110428502461 3008057091439541410688423)
      ·
        refine ⟨4512085637159312116032635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3008057091439541410688423 4512085637159312116032635)
        ·
          refine ⟨6768128455738968174048953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512085637159312116032635 6768128455738968174048953)
          ·
            refine ⟨5076096341804226130536715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6768128455738968174048953 5076096341804226130536715)
            ·
              refine ⟨7614144512706339195805073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076096341804226130536715 7614144512706339195805073)
              ·
                refine ⟨5710608384529754396853805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7614144512706339195805073 5710608384529754396853805)
                ·
                  refine ⟨2141478144198657898820177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5710608384529754396853805 2141478144198657898820177)
                  ·
                    refine ⟨1606108608148993424115133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2141478144198657898820177 1606108608148993424115133)
                    ·
                      refine ⟨602290728055872534043175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606108608148993424115133 602290728055872534043175)
                      ·
                        rfl

theorem cell23_1172957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1172957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172957 prefixEnd_1172957 := by exact prefixLift 1172957
  have htrace : WordTrace (prefixWord ++ tailWord_1172957) baseStart_1172957 baseEnd_1172957 := by
    simpa [prefixWord, tailWord_1172957, baseEnd_1172957] using wordTrace_append hprefix tailTrace_1172957
  have hstable : (prefixWord ++ tailWord_1172957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172957).length < 2 ^ (prefixWord ++ tailWord_1172957).sum := by decide
  have hdescent : baseEnd_1172957 < baseStart_1172957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172967 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1172967 : Nat := 118140960795 + 1172967 * 2 ^ 59
def prefixEnd_1172967 : Nat := 4983230072969 + 3 ^ 40 * 1172967 * 2
def baseEnd_1172967 : Nat := 602295862862417494918129

theorem tailTrace_1172967 : CollatzResearch.WordTrace tailWord_1172967 prefixEnd_1172967 602295862862417494918129 := by
  unfold tailWord_1172967
  simp only [CollatzResearch.WordTrace]
  refine ⟨42781621141548360659877155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28521080761032240439918103 42781621141548360659877155)
  ·
    refine ⟨64172431712322540989815733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42781621141548360659877155 64172431712322540989815733)
    ·
      refine ⟨6016165473030238217795225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64172431712322540989815733 6016165473030238217795225)
      ·
        refine ⟨4512124104772678663346419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6016165473030238217795225 4512124104772678663346419)
        ·
          refine ⟨6768186157159017995019629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512124104772678663346419 6768186157159017995019629)
          ·
            refine ⟨2538069808934631748132361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6768186157159017995019629 2538069808934631748132361)
            ·
              refine ⟨1903552356700973811099271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538069808934631748132361 1903552356700973811099271)
              ·
                refine ⟨2855328535051460716648907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903552356700973811099271 2855328535051460716648907)
                ·
                  refine ⟨4282992802577191074973361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855328535051460716648907 4282992802577191074973361)
                  ·
                    refine ⟨3212244601932893306230021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282992802577191074973361 3212244601932893306230021)
                    ·
                      refine ⟨602295862862417494918129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3212244601932893306230021 602295862862417494918129)
                      ·
                        rfl

theorem cell23_1172967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1172967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172967 prefixEnd_1172967 := by exact prefixLift 1172967
  have htrace : WordTrace (prefixWord ++ tailWord_1172967) baseStart_1172967 baseEnd_1172967 := by
    simpa [prefixWord, tailWord_1172967, baseEnd_1172967] using wordTrace_append hprefix tailTrace_1172967
  have hstable : (prefixWord ++ tailWord_1172967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172967).length < 2 ^ (prefixWord ++ tailWord_1172967).sum := by decide
  have hdescent : baseEnd_1172967 < baseStart_1172967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1172998 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1172998 : Nat := 118140960795 + 1172998 * 2 ^ 59
def prefixEnd_1172998 : Nat := 4983230072969 + 3 ^ 40 * 1172998 * 2
def baseEnd_1172998 : Nat := 200770593587568957876829

theorem tailTrace_1172998 : CollatzResearch.WordTrace tailWord_1172998 prefixEnd_1172998 200770593587568957876829 := by
  unfold tailWord_1172998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336960993888626654820489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28521834536290701969503765 1336960993888626654820489)
  ·
    refine ⟨1002720745416469991115367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1336960993888626654820489 1002720745416469991115367)
    ·
      refine ⟨1504081118124704986673051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002720745416469991115367 1504081118124704986673051)
      ·
        refine ⟨2256121677187057480009577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504081118124704986673051 2256121677187057480009577)
        ·
          refine ⟨1692091257890293110007183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256121677187057480009577 1692091257890293110007183)
          ·
            refine ⟨2538136886835439665010775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692091257890293110007183 2538136886835439665010775)
            ·
              refine ⟨3807205330253159497516163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538136886835439665010775 3807205330253159497516163)
              ·
                refine ⟨5710807995379739246274245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807205330253159497516163 5710807995379739246274245)
                ·
                  refine ⟨1070776499133701108676421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5710807995379739246274245 1070776499133701108676421)
                  ·
                    refine ⟨200770593587568957876829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070776499133701108676421 200770593587568957876829)
                    ·
                      rfl

theorem cell23_1172998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1172998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1172998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1172998 prefixEnd_1172998 := by exact prefixLift 1172998
  have htrace : WordTrace (prefixWord ++ tailWord_1172998) baseStart_1172998 baseEnd_1172998 := by
    simpa [prefixWord, tailWord_1172998, baseEnd_1172998] using wordTrace_append hprefix tailTrace_1172998
  have hstable : (prefixWord ++ tailWord_1172998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1172998).length < 2 ^ (prefixWord ++ tailWord_1172998).sum := by decide
  have hdescent : baseEnd_1172998 < baseStart_1172998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1172998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173004 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1173004 : Nat := 118140960795 + 1173004 * 2 ^ 59
def prefixEnd_1173004 : Nat := 4983230072969 + 3 ^ 40 * 1173004 * 2
def baseEnd_1173004 : Nat := 602314861646633850155459

theorem tailTrace_1173004 : CollatzResearch.WordTrace tailWord_1173004 prefixEnd_1173004 602314861646633850155459 := by
  unfold tailWord_1173004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391485321207157989487033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28521980428276210652649377 21391485321207157989487033)
  ·
    refine ⟨16043613990905368492115275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21391485321207157989487033 16043613990905368492115275)
    ·
      refine ⟨24065420986358052738172913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16043613990905368492115275 24065420986358052738172913)
      ·
        refine ⟨18049065739768539553629685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24065420986358052738172913 18049065739768539553629685)
        ·
          refine ⟨1692099913103300583152783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18049065739768539553629685 1692099913103300583152783)
          ·
            refine ⟨2538149869654950874729175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692099913103300583152783 2538149869654950874729175)
            ·
              refine ⟨3807224804482426312093763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538149869654950874729175 3807224804482426312093763)
              ·
                refine ⟨5710837206723639468140645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807224804482426312093763 5710837206723639468140645)
                ·
                  refine ⟨1070781976260682400276371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5710837206723639468140645 1070781976260682400276371)
                  ·
                    refine ⟨1606172964391023600414557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070781976260682400276371 1606172964391023600414557)
                    ·
                      refine ⟨602314861646633850155459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606172964391023600414557 602314861646633850155459)
                      ·
                        rfl

theorem cell23_1173004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1173004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173004 prefixEnd_1173004 := by exact prefixLift 1173004
  have htrace : WordTrace (prefixWord ++ tailWord_1173004) baseStart_1173004 baseEnd_1173004 := by
    simpa [prefixWord, tailWord_1173004, baseEnd_1173004] using wordTrace_append hprefix tailTrace_1173004
  have hstable : (prefixWord ++ tailWord_1173004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173004).length < 2 ^ (prefixWord ++ tailWord_1173004).sum := by decide
  have hdescent : baseEnd_1173004 < baseStart_1173004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173005 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1173005 : Nat := 118140960795 + 1173005 * 2 ^ 59
def prefixEnd_1173005 : Nat := 4983230072969 + 3 ^ 40 * 1173005 * 2
def baseEnd_1173005 : Nat := 602315375127288346242955

theorem tailTrace_1173005 : CollatzResearch.WordTrace tailWord_1173005 prefixEnd_1173005 602315375127288346242955 := by
  unfold tailWord_1173005
  simp only [CollatzResearch.WordTrace]
  refine ⟨42783007115410693149760469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28522004743607128766506979 42783007115410693149760469)
  ·
    refine ⟨1002726729267438120697511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42783007115410693149760469 1002726729267438120697511)
    ·
      refine ⟨1504090093901157181046267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002726729267438120697511 1504090093901157181046267)
      ·
        refine ⟨2256135140851735771569401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504090093901157181046267 2256135140851735771569401)
        ·
          refine ⟨1692101355638801828677051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2256135140851735771569401 1692101355638801828677051)
          ·
            refine ⟨2538152033458202743015577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692101355638801828677051 2538152033458202743015577)
            ·
              refine ⟨1903614025093652057261683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538152033458202743015577 1903614025093652057261683)
              ·
                refine ⟨2855421037640478085892525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903614025093652057261683 2855421037640478085892525)
                ·
                  refine ⟨1070782889115179282209697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2855421037640478085892525 1070782889115179282209697)
                  ·
                    refine ⟨803087166836384461657273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1070782889115179282209697 803087166836384461657273)
                    ·
                      refine ⟨602315375127288346242955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803087166836384461657273 602315375127288346242955)
                      ·
                        rfl

theorem cell23_1173005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1173005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173005 prefixEnd_1173005 := by exact prefixLift 1173005
  have htrace : WordTrace (prefixWord ++ tailWord_1173005) baseStart_1173005 baseEnd_1173005 := by
    simpa [prefixWord, tailWord_1173005, baseEnd_1173005] using wordTrace_append hprefix tailTrace_1173005
  have hstable : (prefixWord ++ tailWord_1173005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173005).length < 2 ^ (prefixWord ++ tailWord_1173005).sum := by decide
  have hdescent : baseEnd_1173005 < baseStart_1173005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173020 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1173020 : Nat := 118140960795 + 1173020 * 2 ^ 59
def prefixEnd_1173020 : Nat := 4983230072969 + 3 ^ 40 * 1173020 * 2
def baseEnd_1173020 : Nat := 200774359112368595851795

theorem tailTrace_1173020 : CollatzResearch.WordTrace tailWord_1173020 prefixEnd_1173020 200774359112368595851795 := by
  unfold tailWord_1173020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391777105178175355778257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28522369473570900474371009 21391777105178175355778257)
  ·
    refine ⟨16043832828883631516833693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21391777105178175355778257 16043832828883631516833693)
    ·
      refine ⟨6016437310831361818812635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16043832828883631516833693 6016437310831361818812635)
      ·
        refine ⟨9024655966247042728218953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016437310831361818812635 9024655966247042728218953)
        ·
          refine ⟨6768491974685282046164215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9024655966247042728218953 6768491974685282046164215)
          ·
            refine ⟨10152737962027923069246323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768491974685282046164215 10152737962027923069246323)
            ·
              refine ⟨15229106943041884603869485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152737962027923069246323 15229106943041884603869485)
              ·
                refine ⟨5710915103640706726451057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15229106943041884603869485 5710915103640706726451057)
                ·
                  refine ⟨4283186327730530044838293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5710915103640706726451057 4283186327730530044838293)
                  ·
                    refine ⟨200774359112368595851795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4283186327730530044838293 200774359112368595851795)
                    ·
                      rfl

theorem cell23_1173020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1173020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173020 prefixEnd_1173020 := by exact prefixLift 1173020
  have htrace : WordTrace (prefixWord ++ tailWord_1173020) baseStart_1173020 baseEnd_1173020 := by
    simpa [prefixWord, tailWord_1173020, baseEnd_1173020] using wordTrace_append hprefix tailTrace_1173020
  have hstable : (prefixWord ++ tailWord_1173020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173020).length < 2 ^ (prefixWord ++ tailWord_1173020).sum := by decide
  have hdescent : baseEnd_1173020 < baseStart_1173020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173021 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1173021 : Nat := 118140960795 + 1173021 * 2 ^ 59
def prefixEnd_1173021 : Nat := 4983230072969 + 3 ^ 40 * 1173021 * 2
def baseEnd_1173021 : Nat := 602323590817760283642881

theorem tailTrace_1173021 : CollatzResearch.WordTrace tailWord_1173021 prefixEnd_1173021 602323590817760283642881 := by
  unfold tailWord_1173021
  simp only [CollatzResearch.WordTrace]
  refine ⟨42783590683352727882342917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28522393788901818588228611 42783590683352727882342917)
  ·
    refine ⟨8021923253128636477939297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42783590683352727882342917 8021923253128636477939297)
    ·
      refine ⟨6016442439846477358454473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8021923253128636477939297 6016442439846477358454473)
      ·
        refine ⟨4512331829884858018840855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6016442439846477358454473 4512331829884858018840855)
        ·
          refine ⟨6768497744827287028261283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512331829884858018840855 6768497744827287028261283)
          ·
            refine ⟨10152746617240930542391925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768497744827287028261283 10152746617240930542391925)
            ·
              refine ⟨951819995366337238349243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10152746617240930542391925 951819995366337238349243)
              ·
                refine ⟨1427729993049505857523865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951819995366337238349243 1427729993049505857523865)
                ·
                  refine ⟨1070797494787129393142899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1427729993049505857523865 1070797494787129393142899)
                  ·
                    refine ⟨1606196242180694089714349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1070797494787129393142899 1606196242180694089714349)
                    ·
                      refine ⟨602323590817760283642881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606196242180694089714349 602323590817760283642881)
                      ·
                        rfl

theorem cell23_1173021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1173021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173021 prefixEnd_1173021 := by exact prefixLift 1173021
  have htrace : WordTrace (prefixWord ++ tailWord_1173021) baseStart_1173021 baseEnd_1173021 := by
    simpa [prefixWord, tailWord_1173021, baseEnd_1173021] using wordTrace_append hprefix tailTrace_1173021
  have hstable : (prefixWord ++ tailWord_1173021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173021).length < 2 ^ (prefixWord ++ tailWord_1173021).sum := by decide
  have hdescent : baseEnd_1173021 < baseStart_1173021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173080 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1173080 : Nat := 118140960795 + 1173080 * 2 ^ 59
def prefixEnd_1173080 : Nat := 4983230072969 + 3 ^ 40 * 1173080 * 2
def baseEnd_1173080 : Nat := 200784628725458517601703

theorem tailTrace_1173080 : CollatzResearch.WordTrace tailWord_1173080 prefixEnd_1173080 200784628725458517601703 := by
  unfold tailWord_1173080
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392871295069490479370347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28523828393425987305827129 21392871295069490479370347)
  ·
    refine ⟨32089306942604235719055521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21392871295069490479370347 32089306942604235719055521)
    ·
      refine ⟨24066980206953176789291641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32089306942604235719055521 24066980206953176789291641)
      ·
        refine ⟨18050235155214882591968731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24066980206953176789291641 18050235155214882591968731)
        ·
          refine ⟨27075352732822323887953097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18050235155214882591968731 27075352732822323887953097)
          ·
            refine ⟨20306514549616742915964823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27075352732822323887953097 20306514549616742915964823)
            ·
              refine ⟨30459771824425114373947235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20306514549616742915964823 30459771824425114373947235)
              ·
                refine ⟨45689657736637671560920853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30459771824425114373947235 45689657736637671560920853)
                ·
                  refine ⟨2141702706404890854418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45689657736637671560920853 2141702706404890854418165)
                  ·
                    refine ⟨200784628725458517601703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2141702706404890854418165 200784628725458517601703)
                    ·
                      rfl

theorem cell23_1173080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1173080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173080 prefixEnd_1173080 := by exact prefixLift 1173080
  have htrace : WordTrace (prefixWord ++ tailWord_1173080) baseStart_1173080 baseEnd_1173080 := by
    simpa [prefixWord, tailWord_1173080, baseEnd_1173080] using wordTrace_append hprefix tailTrace_1173080
  have hstable : (prefixWord ++ tailWord_1173080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173080).length < 2 ^ (prefixWord ++ tailWord_1173080).sum := by decide
  have hdescent : baseEnd_1173080 < baseStart_1173080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173120 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1173120 : Nat := 118140960795 + 1173120 * 2 ^ 59
def prefixEnd_1173120 : Nat := 4983230072969 + 3 ^ 40 * 1173120 * 2
def baseEnd_1173120 : Nat := 602374425402555396304925

theorem tailTrace_1173120 : CollatzResearch.WordTrace tailWord_1173120 prefixEnd_1173120 602374425402555396304925 := by
  unfold tailWord_1173120
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393600754997033895098407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28524801006662711860131209 21393600754997033895098407)
  ·
    refine ⟨32090401132495550842647611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21393600754997033895098407 32090401132495550842647611)
    ·
      refine ⟨48135601698743326263971417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32090401132495550842647611 48135601698743326263971417)
      ·
        refine ⟨36101701274057494697978563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48135601698743326263971417 36101701274057494697978563)
        ·
          refine ⟨54152551911086242046967845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36101701274057494697978563 54152551911086242046967845)
          ·
            refine ⟨10153603483328670383806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54152551911086242046967845 10153603483328670383806471)
            ·
              refine ⟨15230405224993005575709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10153603483328670383806471 15230405224993005575709707)
              ·
                refine ⟨22845607837489508363564561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15230405224993005575709707 22845607837489508363564561)
                ·
                  refine ⟨17134205878117131272673421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22845607837489508363564561 17134205878117131272673421)
                  ·
                    refine ⟨6425327204293924227252533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17134205878117131272673421 6425327204293924227252533)
                    ·
                      refine ⟨602374425402555396304925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6425327204293924227252533 602374425402555396304925)
                      ·
                        rfl

theorem cell23_1173120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1173120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173120 prefixEnd_1173120 := by exact prefixLift 1173120
  have htrace : WordTrace (prefixWord ++ tailWord_1173120) baseStart_1173120 baseEnd_1173120 := by
    simpa [prefixWord, tailWord_1173120, baseEnd_1173120] using wordTrace_append hprefix tailTrace_1173120
  have hstable : (prefixWord ++ tailWord_1173120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173120).length < 2 ^ (prefixWord ++ tailWord_1173120).sum := by decide
  have hdescent : baseEnd_1173120 < baseStart_1173120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173134 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_1173134 : Nat := 118140960795 + 1173134 * 2 ^ 59
def prefixEnd_1173134 : Nat := 4983230072969 + 3 ^ 40 * 1173134 * 2
def baseEnd_1173134 : Nat := 602381614131718341529861

theorem tailTrace_1173134 : CollatzResearch.WordTrace tailWord_1173134 prefixEnd_1173134 602381614131718341529861 := by
  unfold tailWord_1173134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348464016492918522650807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28525141421295565454137637 5348464016492918522650807)
  ·
    refine ⟨8022696024739377783976211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5348464016492918522650807 8022696024739377783976211)
    ·
      refine ⟨12034044037109066675964317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022696024739377783976211 12034044037109066675964317)
      ·
        refine ⟨4512766513915900003486619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12034044037109066675964317 4512766513915900003486619)
        ·
          refine ⟨6769149770873850005229929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512766513915900003486619 6769149770873850005229929)
          ·
            refine ⟨5076862328155387503922447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769149770873850005229929 5076862328155387503922447)
            ·
              refine ⟨7615293492233081255883671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076862328155387503922447 7615293492233081255883671)
              ·
                refine ⟨11422940238349621883825507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615293492233081255883671 11422940238349621883825507)
                ·
                  refine ⟨17134410357524432825738261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11422940238349621883825507 17134410357524432825738261)
                  ·
                    refine ⟨803175485508957788706481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17134410357524432825738261 803175485508957788706481)
                    ·
                      refine ⟨602381614131718341529861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803175485508957788706481 602381614131718341529861)
                      ·
                        rfl

theorem cell23_1173134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_1173134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173134 prefixEnd_1173134 := by exact prefixLift 1173134
  have htrace : WordTrace (prefixWord ++ tailWord_1173134) baseStart_1173134 baseEnd_1173134 := by
    simpa [prefixWord, tailWord_1173134, baseEnd_1173134] using wordTrace_append hprefix tailTrace_1173134
  have hstable : (prefixWord ++ tailWord_1173134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173134).length < 2 ^ (prefixWord ++ tailWord_1173134).sum := by decide
  have hdescent : baseEnd_1173134 < baseStart_1173134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173144 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_1173144 : Nat := 118140960795 + 1173144 * 2 ^ 59
def prefixEnd_1173144 : Nat := 4983230072969 + 3 ^ 40 * 1173144 * 2
def baseEnd_1173144 : Nat := 200795582979421100801605

theorem tailTrace_1173144 : CollatzResearch.WordTrace tailWord_1173144 prefixEnd_1173144 200795582979421100801605 := by
  unfold tailWord_1173144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21394038430953559944535243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28525384574604746592713657 21394038430953559944535243)
  ·
    refine ⟨32091057646430339916802865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21394038430953559944535243 32091057646430339916802865)
    ·
      refine ⟨24068293234822754937602149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32091057646430339916802865 24068293234822754937602149)
      ·
        refine ⟨4512804981529266550800403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24068293234822754937602149 4512804981529266550800403)
        ·
          refine ⟨6769207472293899826200605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4512804981529266550800403 6769207472293899826200605)
          ·
            refine ⟨2538452802110212434825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6769207472293899826200605 2538452802110212434825227)
            ·
              refine ⟨3807679203165318652237841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2538452802110212434825227 3807679203165318652237841)
              ·
                refine ⟨2855759402373988989178381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807679203165318652237841 2855759402373988989178381)
                ·
                  refine ⟨1070909775890245870941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2855759402373988989178381 1070909775890245870941893)
                  ·
                    refine ⟨200795582979421100801605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070909775890245870941893 200795582979421100801605)
                    ·
                      rfl

theorem cell23_1173144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_1173144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173144 prefixEnd_1173144 := by exact prefixLift 1173144
  have htrace : WordTrace (prefixWord ++ tailWord_1173144) baseStart_1173144 baseEnd_1173144 := by
    simpa [prefixWord, tailWord_1173144, baseEnd_1173144] using wordTrace_append hprefix tailTrace_1173144
  have hstable : (prefixWord ++ tailWord_1173144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173144).length < 2 ^ (prefixWord ++ tailWord_1173144).sum := by decide
  have hdescent : baseEnd_1173144 < baseStart_1173144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173212 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1173212 : Nat := 118140960795 + 1173212 * 2 ^ 59
def prefixEnd_1173212 : Nat := 4983230072969 + 3 ^ 40 * 1173212 * 2
def baseEnd_1173212 : Nat := 200807221874256345451501

theorem tailTrace_1173212 : CollatzResearch.WordTrace tailWord_1173212 prefixEnd_1173212 200807221874256345451501 := by
  unfold tailWord_1173212
  simp only [CollatzResearch.WordTrace]
  refine ⟨21395278512830383751272945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28527038017107178335030593 21395278512830383751272945)
  ·
    refine ⟨16046458884622787813454709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21395278512830383751272945 16046458884622787813454709)
    ·
      refine ⟨1504355520433386357511379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16046458884622787813454709 1504355520433386357511379)
      ·
        refine ⟨2256533280650079536267069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504355520433386357511379 2256533280650079536267069)
        ·
          refine ⟨846199980243779826100151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2256533280650079536267069 846199980243779826100151)
          ·
            refine ⟨1269299970365669739150227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846199980243779826100151 1269299970365669739150227)
            ·
              refine ⟨1903949955548504608725341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269299970365669739150227 1903949955548504608725341)
              ·
                refine ⟨713981233330689228272003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1903949955548504608725341 713981233330689228272003)
                ·
                  refine ⟨1070971849996033842408005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 713981233330689228272003 1070971849996033842408005)
                  ·
                    refine ⟨200807221874256345451501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070971849996033842408005 200807221874256345451501)
                    ·
                      rfl

theorem cell23_1173212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1173212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173212 prefixEnd_1173212 := by exact prefixLift 1173212
  have htrace : WordTrace (prefixWord ++ tailWord_1173212) baseStart_1173212 baseEnd_1173212 := by
    simpa [prefixWord, tailWord_1173212, baseEnd_1173212] using wordTrace_append hprefix tailTrace_1173212
  have hstable : (prefixWord ++ tailWord_1173212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173212).length < 2 ^ (prefixWord ++ tailWord_1173212).sum := by decide
  have hdescent : baseEnd_1173212 < baseStart_1173212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173227 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_1173227 : Nat := 118140960795 + 1173227 * 2 ^ 59
def prefixEnd_1173227 : Nat := 4983230072969 + 3 ^ 40 * 1173227 * 2
def baseEnd_1173227 : Nat := 602429367832586477666933

theorem tailTrace_1173227 : CollatzResearch.WordTrace tailWord_1173227 prefixEnd_1173227 602429367832586477666933 := by
  unfold tailWord_1173227
  simp only [CollatzResearch.WordTrace]
  refine ⟨42791104120606425064341935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28527402747070950042894623 42791104120606425064341935)
  ·
    refine ⟨64186656180909637596512903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42791104120606425064341935 64186656180909637596512903)
    ·
      refine ⟨96279984271364456394769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64186656180909637596512903 96279984271364456394769355)
      ·
        refine ⟨144419976407046684592154033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96279984271364456394769355 144419976407046684592154033)
        ·
          refine ⟨108314982305285013444115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144419976407046684592154033 108314982305285013444115525)
          ·
            refine ⟨20309059182240940020771661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108314982305285013444115525 20309059182240940020771661)
            ·
              refine ⟨7615897193340352507789373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20309059182240940020771661 7615897193340352507789373)
              ·
                refine ⟨2855961447502632190421015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7615897193340352507789373 2855961447502632190421015)
                ·
                  refine ⟨4283942171253948285631523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855961447502632190421015 4283942171253948285631523)
                  ·
                    refine ⟨6425913256880922428447285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283942171253948285631523 6425913256880922428447285)
                    ·
                      refine ⟨602429367832586477666933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6425913256880922428447285 602429367832586477666933)
                      ·
                        rfl

theorem cell23_1173227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_1173227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173227 prefixEnd_1173227 := by exact prefixLift 1173227
  have htrace : WordTrace (prefixWord ++ tailWord_1173227) baseStart_1173227 baseEnd_1173227 := by
    simpa [prefixWord, tailWord_1173227, baseEnd_1173227] using wordTrace_append hprefix tailTrace_1173227
  have hstable : (prefixWord ++ tailWord_1173227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173227).length < 2 ^ (prefixWord ++ tailWord_1173227).sum := by decide
  have hdescent : baseEnd_1173227 < baseStart_1173227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173234 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_1173234 : Nat := 118140960795 + 1173234 * 2 ^ 59
def prefixEnd_1173234 : Nat := 4983230072969 + 3 ^ 40 * 1173234 * 2
def baseEnd_1173234 : Nat := 200810987399055983426467

theorem tailTrace_1173234 : CollatzResearch.WordTrace tailWord_1173234 prefixEnd_1173234 200810987399055983426467 := by
  unfold tailWord_1173234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697839857895266314961689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28527572954387376839897837 10697839857895266314961689)
  ·
    refine ⟨8023379893421449736221267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10697839857895266314961689 8023379893421449736221267)
    ·
      refine ⟨12035069840132174604331901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023379893421449736221267 12035069840132174604331901)
      ·
        refine ⟨4513151190049565476624463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12035069840132174604331901 4513151190049565476624463)
        ·
          refine ⟨6769726785074348214936695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4513151190049565476624463 6769726785074348214936695)
          ·
            refine ⟨10154590177611522322405043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769726785074348214936695 10154590177611522322405043)
            ·
              refine ⟨15231885266417283483607565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10154590177611522322405043 15231885266417283483607565)
              ·
                refine ⟨5711956974906481306352837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15231885266417283483607565 5711956974906481306352837)
                ·
                  refine ⟨1070991932794965244941157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5711956974906481306352837 1070991932794965244941157)
                  ·
                    refine ⟨200810987399055983426467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1070991932794965244941157 200810987399055983426467)
                    ·
                      rfl

theorem cell23_1173234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_1173234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173234 prefixEnd_1173234 := by exact prefixLift 1173234
  have htrace : WordTrace (prefixWord ++ tailWord_1173234) baseStart_1173234 baseEnd_1173234 := by
    simpa [prefixWord, tailWord_1173234, baseEnd_1173234] using wordTrace_append hprefix tailTrace_1173234
  have hstable : (prefixWord ++ tailWord_1173234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173234).length < 2 ^ (prefixWord ++ tailWord_1173234).sum := by decide
  have hdescent : baseEnd_1173234 < baseStart_1173234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173244 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_1173244 : Nat := 118140960795 + 1173244 * 2 ^ 59
def prefixEnd_1173244 : Nat := 4983230072969 + 3 ^ 40 * 1173244 * 2
def baseEnd_1173244 : Nat := 602438097003712911154355

theorem tailTrace_1173244 : CollatzResearch.WordTrace tailWord_1173244 prefixEnd_1173244 602438097003712911154355 := by
  unfold tailWord_1173244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21395862080772418483855393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28527816107696557978473857 21395862080772418483855393)
  ·
    refine ⟨16046896560579313862891545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21395862080772418483855393 16046896560579313862891545)
    ·
      refine ⟨12035172420434485397168659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16046896560579313862891545 12035172420434485397168659)
      ·
        refine ⟨18052758630651728095752989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12035172420434485397168659 18052758630651728095752989)
        ·
          refine ⟨6769784486494398035907371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18052758630651728095752989 6769784486494398035907371)
          ·
            refine ⟨10154676729741597053861057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769784486494398035907371 10154676729741597053861057)
            ·
              refine ⟨7616007547306197790395793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10154676729741597053861057 7616007547306197790395793)
              ·
                refine ⟨5712005660479648342796845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7616007547306197790395793 5712005660479648342796845)
                ·
                  refine ⟨2142002122679868128548817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5712005660479648342796845 2142002122679868128548817)
                  ·
                    refine ⟨1606501592009901096411613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142002122679868128548817 1606501592009901096411613)
                    ·
                      refine ⟨602438097003712911154355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606501592009901096411613 602438097003712911154355)
                      ·
                        rfl

theorem cell23_1173244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_1173244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173244 prefixEnd_1173244 := by exact prefixLift 1173244
  have htrace : WordTrace (prefixWord ++ tailWord_1173244) baseStart_1173244 baseEnd_1173244 := by
    simpa [prefixWord, tailWord_1173244, baseEnd_1173244] using wordTrace_append hprefix tailTrace_1173244
  have hstable : (prefixWord ++ tailWord_1173244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173244).length < 2 ^ (prefixWord ++ tailWord_1173244).sum := by decide
  have hdescent : baseEnd_1173244 < baseStart_1173244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173251 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 2, 4]
def baseStart_1173251 : Nat := 118140960795 + 1173251 * 2 ^ 59
def prefixEnd_1173251 : Nat := 4983230072969 + 3 ^ 40 * 1173251 * 2
def baseEnd_1173251 : Nat := 200813897122764794588941

theorem tailTrace_1173251 : CollatzResearch.WordTrace tailWord_1173251 prefixEnd_1173251 200813897122764794588941 := by
  unfold tailWord_1173251
  simp only [CollatzResearch.WordTrace]
  refine ⟨42791979472519477163215607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28527986315012984775477071 42791979472519477163215607)
  ·
    refine ⟨64187969208779215744823411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42791979472519477163215607 64187969208779215744823411)
    ·
      refine ⟨96281953813168823617235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64187969208779215744823411 96281953813168823617235117)
      ·
        refine ⟨36105732679938308856463169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96281953813168823617235117 36105732679938308856463169)
        ·
          refine ⟨27079299509953731642347377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36105732679938308856463169 27079299509953731642347377)
          ·
            refine ⟨20309474632465298731760533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27079299509953731642347377 20309474632465298731760533)
            ·
              refine ⟨952006623396810878051275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20309474632465298731760533 952006623396810878051275)
              ·
                refine ⟨1428009935095216317076913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952006623396810878051275 1428009935095216317076913)
                ·
                  refine ⟨1071007451321412237807685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1428009935095216317076913 1071007451321412237807685)
                  ·
                    refine ⟨200813897122764794588941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1071007451321412237807685 200813897122764794588941)
                    ·
                      rfl

theorem cell23_1173251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 4].length) (baseStart_1173251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173251 prefixEnd_1173251 := by exact prefixLift 1173251
  have htrace : WordTrace (prefixWord ++ tailWord_1173251) baseStart_1173251 baseEnd_1173251 := by
    simpa [prefixWord, tailWord_1173251, baseEnd_1173251] using wordTrace_append hprefix tailTrace_1173251
  have hstable : (prefixWord ++ tailWord_1173251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173251).length < 2 ^ (prefixWord ++ tailWord_1173251).sum := by decide
  have hdescent : baseEnd_1173251 < baseStart_1173251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173274 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1173274 : Nat := 118140960795 + 1173274 * 2 ^ 59
def prefixEnd_1173274 : Nat := 4983230072969 + 3 ^ 40 * 1173274 * 2
def baseEnd_1173274 : Nat := 602453501423347793779217

theorem tailTrace_1173274 : CollatzResearch.WordTrace tailWord_1173274 prefixEnd_1173274 602453501423347793779217 := by
  unfold tailWord_1173274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10698204587859038022825719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28528545567624101394201917 10698204587859038022825719)
  ·
    refine ⟨16047306881788557034238579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10698204587859038022825719 16047306881788557034238579)
    ·
      refine ⟨24070960322682835551357869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16047306881788557034238579 24070960322682835551357869)
      ·
        refine ⟨9026610121006063331759201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24070960322682835551357869 9026610121006063331759201)
        ·
          refine ⟨6769957590754547498819401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9026610121006063331759201 6769957590754547498819401)
          ·
            refine ⟨5077468193065910624114551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769957590754547498819401 5077468193065910624114551)
            ·
              refine ⟨7616202289598865936171827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077468193065910624114551 7616202289598865936171827)
              ·
                refine ⟨11424303434398298904257741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616202289598865936171827 11424303434398298904257741)
                ·
                  refine ⟨4284113787899362089096653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11424303434398298904257741 4284113787899362089096653)
                  ·
                    refine ⟨1606542670462260783411245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4284113787899362089096653 1606542670462260783411245)
                    ·
                      refine ⟨602453501423347793779217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606542670462260783411245 602453501423347793779217)
                      ·
                        rfl

theorem cell23_1173274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1173274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173274 prefixEnd_1173274 := by exact prefixLift 1173274
  have htrace : WordTrace (prefixWord ++ tailWord_1173274) baseStart_1173274 baseEnd_1173274 := by
    simpa [prefixWord, tailWord_1173274, baseEnd_1173274] using wordTrace_append hprefix tailTrace_1173274
  have hstable : (prefixWord ++ tailWord_1173274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173274).length < 2 ^ (prefixWord ++ tailWord_1173274).sum := by decide
  have hdescent : baseEnd_1173274 < baseStart_1173274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173292 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_1173292 : Nat := 118140960795 + 1173292 * 2 ^ 59
def prefixEnd_1173292 : Nat := 4983230072969 + 3 ^ 40 * 1173292 * 2
def baseEnd_1173292 : Nat := 602462744075128723354135

theorem tailTrace_1173292 : CollatzResearch.WordTrace tailWord_1173292 prefixEnd_1173292 602462744075128723354135 := by
  unfold tailWord_1173292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21396737432685470582729065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28528983243580627443638753 21396737432685470582729065)
  ·
    refine ⟨16047553074514102937046799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21396737432685470582729065 16047553074514102937046799)
    ·
      refine ⟨24071329611771154405570199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16047553074514102937046799 24071329611771154405570199)
      ·
        refine ⟨36106994417656731608355299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24071329611771154405570199 36106994417656731608355299)
        ·
          refine ⟨54160491626485097412532949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36106994417656731608355299 54160491626485097412532949)
          ·
            refine ⟨1269386522495744470606241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54160491626485097412532949 1269386522495744470606241)
            ·
              refine ⟨952039891871808352954681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269386522495744470606241 952039891871808352954681)
              ·
                refine ⟨714029918903856264716011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952039891871808352954681 714029918903856264716011)
                ·
                  refine ⟨1071044878355784397074017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714029918903856264716011 1071044878355784397074017)
                  ·
                    refine ⟨803283658766838297805513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071044878355784397074017 803283658766838297805513)
                    ·
                      refine ⟨602462744075128723354135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803283658766838297805513 602462744075128723354135)
                      ·
                        rfl

theorem cell23_1173292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_1173292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173292 prefixEnd_1173292 := by exact prefixLift 1173292
  have htrace : WordTrace (prefixWord ++ tailWord_1173292) baseStart_1173292 baseEnd_1173292 := by
    simpa [prefixWord, tailWord_1173292, baseEnd_1173292] using wordTrace_append hprefix tailTrace_1173292
  have hstable : (prefixWord ++ tailWord_1173292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173292).length < 2 ^ (prefixWord ++ tailWord_1173292).sum := by decide
  have hdescent : baseEnd_1173292 < baseStart_1173292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173337 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 9]
def baseStart_1173337 : Nat := 118140960795 + 1173337 * 2 ^ 59
def prefixEnd_1173337 : Nat := 4983230072969 + 3 ^ 40 * 1173337 * 2
def baseEnd_1173337 : Nat := 66942872300509005254603

theorem tailTrace_1173337 : CollatzResearch.WordTrace tailWord_1173337 prefixEnd_1173337 66942872300509005254603 := by
  unfold tailWord_1173337
  simp only [CollatzResearch.WordTrace]
  refine ⟨42795116150207913850846265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28530077433471942567230843 42795116150207913850846265)
  ·
    refine ⟨32096337112655935388134699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42795116150207913850846265 32096337112655935388134699)
    ·
      refine ⟨48144505668983903082202049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32096337112655935388134699 48144505668983903082202049)
      ·
        refine ⟨36108379251737927311651537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48144505668983903082202049 36108379251737927311651537)
        ·
          refine ⟨27081284438803445483738653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36108379251737927311651537 27081284438803445483738653)
          ·
            refine ⟨10155481664551292056401995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27081284438803445483738653 10155481664551292056401995)
            ·
              refine ⟨15233222496826938084602993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10155481664551292056401995 15233222496826938084602993)
              ·
                refine ⟨11424916872620203563452245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15233222496826938084602993 11424916872620203563452245)
                ·
                  refine ⟨66942872300509005254603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11424916872620203563452245 66942872300509005254603)
                  ·
                    rfl

theorem cell23_1173337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_1173337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173337 prefixEnd_1173337 := by exact prefixLift 1173337
  have htrace : WordTrace (prefixWord ++ tailWord_1173337) baseStart_1173337 baseEnd_1173337 := by
    simpa [prefixWord, tailWord_1173337, baseEnd_1173337] using wordTrace_append hprefix tailTrace_1173337
  have hstable : (prefixWord ++ tailWord_1173337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173337).length < 2 ^ (prefixWord ++ tailWord_1173337).sum := by decide
  have hdescent : baseEnd_1173337 < baseStart_1173337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173344 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1173344 : Nat := 118140960795 + 1173344 * 2 ^ 59
def prefixEnd_1173344 : Nat := 4983230072969 + 3 ^ 40 * 1173344 * 2
def baseEnd_1173344 : Nat := 602489445069162519903895

theorem tailTrace_1173344 : CollatzResearch.WordTrace tailWord_1173344 prefixEnd_1173344 602489445069162519903895 := by
  unfold tailWord_1173344
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397685730591277023175543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28530247640788369364234057 21397685730591277023175543)
  ·
    refine ⟨32096528595886915534763315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21397685730591277023175543 32096528595886915534763315)
    ·
      refine ⟨48144792893830373302144973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32096528595886915534763315 48144792893830373302144973)
      ·
        refine ⟨18054297335186389988304365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48144792893830373302144973 18054297335186389988304365)
        ·
          refine ⟨6770361500694896245614137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18054297335186389988304365 6770361500694896245614137)
          ·
            refine ⟨5077771125521172184210603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770361500694896245614137 5077771125521172184210603)
            ·
              refine ⟨7616656688281758276315905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077771125521172184210603 7616656688281758276315905)
              ·
                refine ⟨5712492516211318707236929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7616656688281758276315905 5712492516211318707236929)
                ·
                  refine ⟨4284369387158489030427697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5712492516211318707236929 4284369387158489030427697)
                  ·
                    refine ⟨3213277040368866772820773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284369387158489030427697 3213277040368866772820773)
                    ·
                      refine ⟨602489445069162519903895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3213277040368866772820773 602489445069162519903895)
                      ·
                        rfl

theorem cell23_1173344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1173344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173344 prefixEnd_1173344 := by exact prefixLift 1173344
  have htrace : WordTrace (prefixWord ++ tailWord_1173344) baseStart_1173344 baseEnd_1173344 := by
    simpa [prefixWord, tailWord_1173344, baseEnd_1173344] using wordTrace_append hprefix tailTrace_1173344
  have hstable : (prefixWord ++ tailWord_1173344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173344).length < 2 ^ (prefixWord ++ tailWord_1173344).sum := by decide
  have hdescent : baseEnd_1173344 < baseStart_1173344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173416 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1173416 : Nat := 118140960795 + 1173416 * 2 ^ 59
def prefixEnd_1173416 : Nat := 4983230072969 + 3 ^ 40 * 1173416 * 2
def baseEnd_1173416 : Nat := 602526415676286238203565

theorem tailTrace_1173416 : CollatzResearch.WordTrace tailWord_1173416 prefixEnd_1173416 602526415676286238203565 := by
  unfold tailWord_1173416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21398998758460855171486051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28531998344614473561981401 21398998758460855171486051)
  ·
    refine ⟨32098498137691282757229077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21398998758460855171486051 32098498137691282757229077)
    ·
      refine ⟨1504617100204278879245113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32098498137691282757229077 1504617100204278879245113)
      ·
        refine ⟨1128462825153209159433835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1504617100204278879245113 1128462825153209159433835)
        ·
          refine ⟨1692694237729813739150753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128462825153209159433835 1692694237729813739150753)
          ·
            refine ⟨1269520678297360304363065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692694237729813739150753 1269520678297360304363065)
            ·
              refine ⟨952140508723020228272299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1269520678297360304363065 952140508723020228272299)
              ·
                refine ⟨1428210763084530342408449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952140508723020228272299 1428210763084530342408449)
                ·
                  refine ⟨1071158072313397756806337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1428210763084530342408449 1071158072313397756806337)
                  ·
                    refine ⟨803368554235048317604753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071158072313397756806337 803368554235048317604753)
                    ·
                      refine ⟨602526415676286238203565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803368554235048317604753 602526415676286238203565)
                      ·
                        rfl

theorem cell23_1173416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1173416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173416 prefixEnd_1173416 := by exact prefixLift 1173416
  have htrace : WordTrace (prefixWord ++ tailWord_1173416) baseStart_1173416 baseEnd_1173416 := by
    simpa [prefixWord, tailWord_1173416, baseEnd_1173416] using wordTrace_append hprefix tailTrace_1173416
  have hstable : (prefixWord ++ tailWord_1173416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173416).length < 2 ^ (prefixWord ++ tailWord_1173416).sum := by decide
  have hdescent : baseEnd_1173416 < baseStart_1173416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173438 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1173438 : Nat := 118140960795 + 1173438 * 2 ^ 59
def prefixEnd_1173438 : Nat := 4983230072969 + 3 ^ 40 * 1173438 * 2
def baseEnd_1173438 : Nat := 602537712250685152128463

theorem tailTrace_1173438 : CollatzResearch.WordTrace tailWord_1173438 prefixEnd_1173438 602537712250685152128463 := by
  unfold tailWord_1173438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349849990355251012534121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28532533281894672066848645 5349849990355251012534121)
  ·
    refine ⟨4012387492766438259400591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5349849990355251012534121 4012387492766438259400591)
    ·
      refine ⟨6018581239149657389100887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012387492766438259400591 6018581239149657389100887)
      ·
        refine ⟨9027871858724486083651331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018581239149657389100887 9027871858724486083651331)
        ·
          refine ⟨13541807788086729125476997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027871858724486083651331 13541807788086729125476997)
          ·
            refine ⟨2539088960266261711026937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13541807788086729125476997 2539088960266261711026937)
            ·
              refine ⟨1904316720199696283270203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539088960266261711026937 1904316720199696283270203)
              ·
                refine ⟨2856475080299544424905305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904316720199696283270203 2856475080299544424905305)
                ·
                  refine ⟨2142356310224658318678979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2856475080299544424905305 2142356310224658318678979)
                  ·
                    refine ⟨3213534465336987478018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2142356310224658318678979 3213534465336987478018469)
                    ·
                      refine ⟨602537712250685152128463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3213534465336987478018469 602537712250685152128463)
                      ·
                        rfl

theorem cell23_1173438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1173438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173438 prefixEnd_1173438 := by exact prefixLift 1173438
  have htrace : WordTrace (prefixWord ++ tailWord_1173438) baseStart_1173438 baseEnd_1173438 := by
    simpa [prefixWord, tailWord_1173438, baseEnd_1173438] using wordTrace_append hprefix tailTrace_1173438
  have hstable : (prefixWord ++ tailWord_1173438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173438).length < 2 ^ (prefixWord ++ tailWord_1173438).sum := by decide
  have hdescent : baseEnd_1173438 < baseStart_1173438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173461 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 6]
def baseStart_1173461 : Nat := 118140960795 + 1173461 * 2 ^ 59
def prefixEnd_1173461 : Nat := 4983230072969 + 3 ^ 40 * 1173461 * 2
def baseEnd_1173461 : Nat := 66949946922859840237873

theorem tailTrace_1173461 : CollatzResearch.WordTrace tailWord_1173461 prefixEnd_1173461 66949946922859840237873 := by
  unfold tailWord_1173461
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799638801758683028360237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28533092534505788685573491 42799638801758683028360237)
  ·
    refine ⟨16049864550659506135635089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42799638801758683028360237 16049864550659506135635089)
    ·
      refine ⟨12037398412994629601726317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16049864550659506135635089 12037398412994629601726317)
      ·
        refine ⟨4514024404872986100647369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12037398412994629601726317 4514024404872986100647369)
        ·
          refine ⟨3385518303654739575485527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514024404872986100647369 3385518303654739575485527)
          ·
            refine ⟨5078277455482109363228291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385518303654739575485527 5078277455482109363228291)
            ·
              refine ⟨7617416183223164044842437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078277455482109363228291 7617416183223164044842437)
              ·
                refine ⟨1428265534354343258407957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7617416183223164044842437 1428265534354343258407957)
                ·
                  refine ⟨66949946922859840237873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1428265534354343258407957 66949946922859840237873)
                  ·
                    rfl

theorem cell23_1173461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_1173461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173461 prefixEnd_1173461 := by exact prefixLift 1173461
  have htrace : WordTrace (prefixWord ++ tailWord_1173461) baseStart_1173461 baseEnd_1173461 := by
    simpa [prefixWord, tailWord_1173461, baseEnd_1173461] using wordTrace_append hprefix tailTrace_1173461
  have hstable : (prefixWord ++ tailWord_1173461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173461).length < 2 ^ (prefixWord ++ tailWord_1173461).sum := by decide
  have hdescent : baseEnd_1173461 < baseStart_1173461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173464 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1173464 : Nat := 118140960795 + 1173464 * 2 ^ 59
def prefixEnd_1173464 : Nat := 4983230072969 + 3 ^ 40 * 1173464 * 2
def baseEnd_1173464 : Nat := 602551062747702050403343

theorem tailTrace_1173464 : CollatzResearch.WordTrace tailWord_1173464 prefixEnd_1173464 602551062747702050403343 := by
  unfold tailWord_1173464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21399874110373907270359723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28533165480498543027146297 21399874110373907270359723)
  ·
    refine ⟨32099811165560860905539585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21399874110373907270359723 32099811165560860905539585)
    ·
      refine ⟨24074858374170645679154689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32099811165560860905539585 24074858374170645679154689)
      ·
        refine ⟨18056143780627984259366017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24074858374170645679154689 18056143780627984259366017)
        ·
          refine ⟨13542107835470988194524513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18056143780627984259366017 13542107835470988194524513)
          ·
            refine ⟨10156580876603241145893385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13542107835470988194524513 10156580876603241145893385)
            ·
              refine ⟨7617435657452430859420039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10156580876603241145893385 7617435657452430859420039)
              ·
                refine ⟨11426153486178646289130059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617435657452430859420039 11426153486178646289130059)
                ·
                  refine ⟨17139230229267969433695089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11426153486178646289130059 17139230229267969433695089)
                  ·
                    refine ⟨12854422671950977075271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17139230229267969433695089 12854422671950977075271317)
                    ·
                      refine ⟨602551062747702050403343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12854422671950977075271317 602551062747702050403343)
                      ·
                        rfl

theorem cell23_1173464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1173464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173464 prefixEnd_1173464 := by exact prefixLift 1173464
  have htrace : WordTrace (prefixWord ++ tailWord_1173464) baseStart_1173464 baseEnd_1173464 := by
    simpa [prefixWord, tailWord_1173464, baseEnd_1173464] using wordTrace_append hprefix tailTrace_1173464
  have hstable : (prefixWord ++ tailWord_1173464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173464).length < 2 ^ (prefixWord ++ tailWord_1173464).sum := by decide
  have hdescent : baseEnd_1173464 < baseStart_1173464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173465 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 1, 4]
def baseStart_1173465 : Nat := 118140960795 + 1173465 * 2 ^ 59
def prefixEnd_1173465 : Nat := 4983230072969 + 3 ^ 40 * 1173465 * 2
def baseEnd_1173465 : Nat := 200850525409452182163613

theorem tailTrace_1173465 : CollatzResearch.WordTrace tailWord_1173465 prefixEnd_1173465 200850525409452182163613 := by
  unfold tailWord_1173465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799784693744191711505849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28533189795829461141003899 42799784693744191711505849)
  ·
    refine ⟨32099838520308143783629387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42799784693744191711505849 32099838520308143783629387)
    ·
      refine ⟨48149757780462215675444081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32099838520308143783629387 48149757780462215675444081)
      ·
        refine ⟨36112318335346661756583061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48149757780462215675444081 36112318335346661756583061)
        ·
          refine ⟨1692764921969374769839831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36112318335346661756583061 1692764921969374769839831)
          ·
            refine ⟨2539147382954062154759747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692764921969374769839831 2539147382954062154759747)
            ·
              refine ⟨3808721074431093232139621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539147382954062154759747 3808721074431093232139621)
              ·
                refine ⟨714135201455829981026179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3808721074431093232139621 714135201455829981026179)
                ·
                  refine ⟨1071202802183744971539269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714135201455829981026179 1071202802183744971539269)
                  ·
                    refine ⟨200850525409452182163613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1071202802183744971539269 200850525409452182163613)
                    ·
                      rfl

theorem cell23_1173465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 4].length) (baseStart_1173465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173465 prefixEnd_1173465 := by exact prefixLift 1173465
  have htrace : WordTrace (prefixWord ++ tailWord_1173465) baseStart_1173465 baseEnd_1173465 := by
    simpa [prefixWord, tailWord_1173465, baseEnd_1173465] using wordTrace_append hprefix tailTrace_1173465
  have hstable : (prefixWord ++ tailWord_1173465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173465).length < 2 ^ (prefixWord ++ tailWord_1173465).sum := by decide
  have hdescent : baseEnd_1173465 < baseStart_1173465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_1173504 : Nat := 118140960795 + 1173504 * 2 ^ 59
def prefixEnd_1173504 : Nat := 4983230072969 + 3 ^ 40 * 1173504 * 2
def baseEnd_1173504 : Nat := 200857200657960631301053

theorem tailTrace_1173504 : CollatzResearch.WordTrace tailWord_1173504 prefixEnd_1173504 200857200657960631301053 := by
  unfold tailWord_1173504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21400603570301450686087783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28534138093735267581450377 21400603570301450686087783)
  ·
    refine ⟨32100905355452176029131675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21400603570301450686087783 32100905355452176029131675)
    ·
      refine ⟨48151358033178264043697513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32100905355452176029131675 48151358033178264043697513)
      ·
        refine ⟨36113518524883698032773135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48151358033178264043697513 36113518524883698032773135)
        ·
          refine ⟨54170277787325547049159703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36113518524883698032773135 54170277787325547049159703)
          ·
            refine ⟨81255416680988320573739555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54170277787325547049159703 81255416680988320573739555)
            ·
              refine ⟨121883125021482480860609333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81255416680988320573739555 121883125021482480860609333)
              ·
                refine ⟨11426542970763982580682125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121883125021482480860609333 11426542970763982580682125)
                ·
                  refine ⟨4284953614036493467755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11426542970763982580682125 4284953614036493467755797)
                  ·
                    refine ⟨200857200657960631301053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4284953614036493467755797 200857200657960631301053)
                    ·
                      rfl

theorem cell23_1173504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_1173504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173504 prefixEnd_1173504 := by exact prefixLift 1173504
  have htrace : WordTrace (prefixWord ++ tailWord_1173504) baseStart_1173504 baseEnd_1173504 := by
    simpa [prefixWord, tailWord_1173504, baseEnd_1173504] using wordTrace_append hprefix tailTrace_1173504
  have hstable : (prefixWord ++ tailWord_1173504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173504).length < 2 ^ (prefixWord ++ tailWord_1173504).sum := by decide
  have hdescent : baseEnd_1173504 < baseStart_1173504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173531 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3]
def baseStart_1173531 : Nat := 118140960795 + 1173531 * 2 ^ 59
def prefixEnd_1173531 : Nat := 4983230072969 + 3 ^ 40 * 1173531 * 2
def baseEnd_1173531 : Nat := 602585465951553288265535

theorem tailTrace_1173531 : CollatzResearch.WordTrace tailWord_1173531 prefixEnd_1173531 602585465951553288265535 := by
  unfold tailWord_1173531
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802191911505084983408447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28534794607670056655605631 42802191911505084983408447)
  ·
    refine ⟨64203287867257627475112671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42802191911505084983408447 64203287867257627475112671)
    ·
      refine ⟨96304931800886441212669007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64203287867257627475112671 96304931800886441212669007)
      ·
        refine ⟨144457397701329661819003511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96304931800886441212669007 144457397701329661819003511)
        ·
          refine ⟨216686096551994492728505267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144457397701329661819003511 216686096551994492728505267)
          ·
            refine ⟨325029144827991739092757901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216686096551994492728505267 325029144827991739092757901)
            ·
              refine ⟨121885929310496902159784213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325029144827991739092757901 121885929310496902159784213)
              ·
                refine ⟨5713402936429542288739885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121885929310496902159784213 5713402936429542288739885)
                ·
                  refine ⟨2142526101161078358277457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713402936429542288739885 2142526101161078358277457)
                  ·
                    refine ⟨1606894575870808768708093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2142526101161078358277457 1606894575870808768708093)
                    ·
                      refine ⟨602585465951553288265535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606894575870808768708093 602585465951553288265535)
                      ·
                        rfl

theorem cell23_1173531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 3].length) (baseStart_1173531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173531 prefixEnd_1173531 := by exact prefixLift 1173531
  have htrace : WordTrace (prefixWord ++ tailWord_1173531) baseStart_1173531 baseEnd_1173531 := by
    simpa [prefixWord, tailWord_1173531, baseEnd_1173531] using wordTrace_append hprefix tailTrace_1173531
  have hstable : (prefixWord ++ tailWord_1173531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173531).length < 2 ^ (prefixWord ++ tailWord_1173531).sum := by decide
  have hdescent : baseEnd_1173531 < baseStart_1173531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173541 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_1173541 : Nat := 118140960795 + 1173541 * 2 ^ 59
def prefixEnd_1173541 : Nat := 4983230072969 + 3 ^ 40 * 1173541 * 2
def baseEnd_1173541 : Nat := 602590600758098249140489

theorem tailTrace_1173541 : CollatzResearch.WordTrace tailWord_1173541 prefixEnd_1173541 602590600758098249140489 := by
  unfold tailWord_1173541
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802556641468856691272477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28535037760979237794181651 42802556641468856691272477)
  ·
    refine ⟨16050958740550821259227179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42802556641468856691272477 16050958740550821259227179)
    ·
      refine ⟨24076438110826231888840769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16050958740550821259227179 24076438110826231888840769)
      ·
        refine ⟨18057328583119673916630577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24076438110826231888840769 18057328583119673916630577)
        ·
          refine ⟨13542996437339755437472933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18057328583119673916630577 13542996437339755437472933)
          ·
            refine ⟨2539311832001204144526175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13542996437339755437472933 2539311832001204144526175)
            ·
              refine ⟨3808967748001806216789263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539311832001204144526175 3808967748001806216789263)
              ·
                refine ⟨5713451622002709325183895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808967748001806216789263 5713451622002709325183895)
                ·
                  refine ⟨8570177433004063987775843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713451622002709325183895 8570177433004063987775843)
                  ·
                    refine ⟨12855266149506095981663765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8570177433004063987775843 12855266149506095981663765)
                    ·
                      refine ⟨602590600758098249140489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12855266149506095981663765 602590600758098249140489)
                      ·
                        rfl

theorem cell23_1173541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_1173541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173541 prefixEnd_1173541 := by exact prefixLift 1173541
  have htrace : WordTrace (prefixWord ++ tailWord_1173541) baseStart_1173541 baseEnd_1173541 := by
    simpa [prefixWord, tailWord_1173541, baseEnd_1173541] using wordTrace_append hprefix tailTrace_1173541
  have hstable : (prefixWord ++ tailWord_1173541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173541).length < 2 ^ (prefixWord ++ tailWord_1173541).sum := by decide
  have hdescent : baseEnd_1173541 < baseStart_1173541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173556 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1173556 : Nat := 118140960795 + 1173556 * 2 ^ 59
def prefixEnd_1173556 : Nat := 4983230072969 + 3 ^ 40 * 1173556 * 2
def baseEnd_1173556 : Nat := 602598302967915690452921

theorem tailTrace_1173556 : CollatzResearch.WordTrace tailWord_1173556 prefixEnd_1173556 602598302967915690452921 := by
  unfold tailWord_1173556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21401551868207257126534261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28535402490943009502045681 21401551868207257126534261)
  ·
    refine ⟨2006395487644430355612587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21401551868207257126534261 2006395487644430355612587)
    ·
      refine ⟨3009593231466645533418881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006395487644430355612587 3009593231466645533418881)
      ·
        refine ⟨2257194923599984150064161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009593231466645533418881 2257194923599984150064161)
        ·
          refine ⟨1692896192699988112548121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257194923599984150064161 1692896192699988112548121)
          ·
            refine ⟨1269672144524991084411091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1692896192699988112548121 1269672144524991084411091)
            ·
              refine ⟨1904508216787486626616637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269672144524991084411091 1904508216787486626616637)
              ·
                refine ⟨714190581295307484981239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1904508216787486626616637 714190581295307484981239)
                ·
                  refine ⟨1071285871942961227471859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714190581295307484981239 1071285871942961227471859)
                  ·
                    refine ⟨1606928807914441841207789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1071285871942961227471859 1606928807914441841207789)
                    ·
                      refine ⟨602598302967915690452921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1606928807914441841207789 602598302967915690452921)
                      ·
                        rfl

theorem cell23_1173556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1173556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173556 prefixEnd_1173556 := by exact prefixLift 1173556
  have htrace : WordTrace (prefixWord ++ tailWord_1173556) baseStart_1173556 baseEnd_1173556 := by
    simpa [prefixWord, tailWord_1173556, baseEnd_1173556] using wordTrace_append hprefix tailTrace_1173556
  have hstable : (prefixWord ++ tailWord_1173556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173556).length < 2 ^ (prefixWord ++ tailWord_1173556).sum := by decide
  have hdescent : baseEnd_1173556 < baseStart_1173556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173558 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1173558 : Nat := 118140960795 + 1173558 * 2 ^ 59
def prefixEnd_1173558 : Nat := 4983230072969 + 3 ^ 40 * 1173558 * 2
def baseEnd_1173558 : Nat := 602599329929224682627911

theorem tailTrace_1173558 : CollatzResearch.WordTrace tailWord_1173558 prefixEnd_1173558 602599329929224682627911 := by
  unfold tailWord_1173558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675198542650454287165083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28535451121604845729760885 2675198542650454287165083)
  ·
    refine ⟨4012797813975681430747625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675198542650454287165083 4012797813975681430747625)
    ·
      refine ⟨3009598360481761073060719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4012797813975681430747625 3009598360481761073060719)
      ·
        refine ⟨4514397540722641609591079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009598360481761073060719 4514397540722641609591079)
        ·
          refine ⟨6771596311083962414386619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514397540722641609591079 6771596311083962414386619)
          ·
            refine ⟨10157394466625943621579929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771596311083962414386619 10157394466625943621579929)
            ·
              refine ⟨7618045849969457716184947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10157394466625943621579929 7618045849969457716184947)
              ·
                refine ⟨11427068774954186574277421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618045849969457716184947 11427068774954186574277421)
                ·
                  refine ⟨4285150790607819965354033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11427068774954186574277421 4285150790607819965354033)
                  ·
                    refine ⟨3213863092955864974015525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285150790607819965354033 3213863092955864974015525)
                    ·
                      refine ⟨602599329929224682627911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3213863092955864974015525 602599329929224682627911)
                      ·
                        rfl

theorem cell23_1173558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1173558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173558 prefixEnd_1173558 := by exact prefixLift 1173558
  have htrace : WordTrace (prefixWord ++ tailWord_1173558) baseStart_1173558 baseEnd_1173558 := by
    simpa [prefixWord, tailWord_1173558, baseEnd_1173558] using wordTrace_append hprefix tailTrace_1173558
  have hstable : (prefixWord ++ tailWord_1173558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173558).length < 2 ^ (prefixWord ++ tailWord_1173558).sum := by decide
  have hdescent : baseEnd_1173558 < baseStart_1173558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173588 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_1173588 : Nat := 118140960795 + 1173588 * 2 ^ 59
def prefixEnd_1173588 : Nat := 4983230072969 + 3 ^ 40 * 1173588 * 2
def baseEnd_1173588 : Nat := 602614734348859565252773

theorem tailTrace_1173588 : CollatzResearch.WordTrace tailWord_1173588 prefixEnd_1173588 602614734348859565252773 := by
  unfold tailWord_1173588
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402135436149291859116709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28536180581532389145488945 21402135436149291859116709)
  ·
    refine ⟨4012900394277992223584383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21402135436149291859116709 4012900394277992223584383)
    ·
      refine ⟨6019350591416988335376575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012900394277992223584383 6019350591416988335376575)
      ·
        refine ⟨9029025887125482503064863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019350591416988335376575 9029025887125482503064863)
        ·
          refine ⟨13543538830688223754597295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029025887125482503064863 13543538830688223754597295)
          ·
            refine ⟨20315308246032335631895943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543538830688223754597295 20315308246032335631895943)
            ·
              refine ⟨30472962369048503447843915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20315308246032335631895943 30472962369048503447843915)
              ·
                refine ⟨45709443553572755171765873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30472962369048503447843915 45709443553572755171765873)
                ·
                  refine ⟨34282082665179566378824405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45709443553572755171765873 34282082665179566378824405)
                  ·
                    refine ⟨803486312465146087003697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34282082665179566378824405 803486312465146087003697)
                    ·
                      refine ⟨602614734348859565252773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803486312465146087003697 602614734348859565252773)
                      ·
                        rfl

theorem cell23_1173588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_1173588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173588 prefixEnd_1173588 := by exact prefixLift 1173588
  have htrace : WordTrace (prefixWord ++ tailWord_1173588) baseStart_1173588 baseEnd_1173588 := by
    simpa [prefixWord, tailWord_1173588, baseEnd_1173588] using wordTrace_append hprefix tailTrace_1173588
  have hstable : (prefixWord ++ tailWord_1173588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173588).length < 2 ^ (prefixWord ++ tailWord_1173588).sum := by decide
  have hdescent : baseEnd_1173588 < baseStart_1173588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173605 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_1173605 : Nat := 118140960795 + 1173605 * 2 ^ 59
def prefixEnd_1173605 : Nat := 4983230072969 + 3 ^ 40 * 1173605 * 2
def baseEnd_1173605 : Nat := 602623463519985998740195

theorem tailTrace_1173605 : CollatzResearch.WordTrace tailWord_1173605 prefixEnd_1173605 602623463519985998740195 := by
  unfold tailWord_1173605
  simp only [CollatzResearch.WordTrace]
  refine ⟨42804890913236995621602269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28536593942157997081068179 42804890913236995621602269)
  ·
    refine ⟨16051834092463873358100851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42804890913236995621602269 16051834092463873358100851)
    ·
      refine ⟨24077751138695810037151277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16051834092463873358100851 24077751138695810037151277)
      ·
        refine ⟨9029156677010928763931729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24077751138695810037151277 9029156677010928763931729)
        ·
          refine ⟨6771867507758196572948797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9029156677010928763931729 6771867507758196572948797)
          ·
            refine ⟨2539450315409323714855799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6771867507758196572948797 2539450315409323714855799)
            ·
              refine ⟨3809175473113985572283699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539450315409323714855799 3809175473113985572283699)
              ·
                refine ⟨5713763209670978358425549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809175473113985572283699 5713763209670978358425549)
                ·
                  refine ⟨2142661203626616884409581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5713763209670978358425549 2142661203626616884409581)
                  ·
                    refine ⟨803497951359981331653593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142661203626616884409581 803497951359981331653593)
                    ·
                      refine ⟨602623463519985998740195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803497951359981331653593 602623463519985998740195)
                      ·
                        rfl

theorem cell23_1173605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_1173605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173605 prefixEnd_1173605 := by exact prefixLift 1173605
  have htrace : WordTrace (prefixWord ++ tailWord_1173605) baseStart_1173605 baseEnd_1173605 := by
    simpa [prefixWord, tailWord_1173605, baseEnd_1173605] using wordTrace_append hprefix tailTrace_1173605
  have hstable : (prefixWord ++ tailWord_1173605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173605).length < 2 ^ (prefixWord ++ tailWord_1173605).sum := by decide
  have hdescent : baseEnd_1173605 < baseStart_1173605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173641 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 7]
def baseStart_1173641 : Nat := 118140960795 + 1173641 * 2 ^ 59
def prefixEnd_1173641 : Nat := 4983230072969 + 3 ^ 40 * 1173641 * 2
def baseEnd_1173641 : Nat := 66960216535949761987781

theorem tailTrace_1173641 : CollatzResearch.WordTrace tailWord_1173641 prefixEnd_1173641 66960216535949761987781 := by
  unfold tailWord_1173641
  simp only [CollatzResearch.WordTrace]
  refine ⟨42806203941106573769912777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28537469294071049179941851 42806203941106573769912777)
  ·
    refine ⟨32104652955829930327434583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42806203941106573769912777 32104652955829930327434583)
    ·
      refine ⟨48156979433744895491151875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32104652955829930327434583 48156979433744895491151875)
      ·
        refine ⟨72235469150617343236727813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48156979433744895491151875 72235469150617343236727813)
        ·
          refine ⟨13544150465740751856886465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72235469150617343236727813 13544150465740751856886465)
          ·
            refine ⟨10158112849305563892664849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13544150465740751856886465 10158112849305563892664849)
            ·
              refine ⟨7618584636979172919498637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10158112849305563892664849 7618584636979172919498637)
              ·
                refine ⟨2856969238867189844811989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7618584636979172919498637 2856969238867189844811989)
                ·
                  refine ⟨66960216535949761987781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2856969238867189844811989 66960216535949761987781)
                  ·
                    rfl

theorem cell23_1173641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_1173641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173641 prefixEnd_1173641 := by exact prefixLift 1173641
  have htrace : WordTrace (prefixWord ++ tailWord_1173641) baseStart_1173641 baseEnd_1173641 := by
    simpa [prefixWord, tailWord_1173641, baseEnd_1173641] using wordTrace_append hprefix tailTrace_1173641
  have hstable : (prefixWord ++ tailWord_1173641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173641).length < 2 ^ (prefixWord ++ tailWord_1173641).sum := by decide
  have hdescent : baseEnd_1173641 < baseStart_1173641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173725 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1173725 : Nat := 118140960795 + 1173725 * 2 ^ 59
def prefixEnd_1173725 : Nat := 4983230072969 + 3 ^ 40 * 1173725 * 2
def baseEnd_1173725 : Nat := 602685081198525529239643

theorem tailTrace_1173725 : CollatzResearch.WordTrace tailWord_1173725 prefixEnd_1173725 602685081198525529239643 := by
  unfold tailWord_1173725
  simp only [CollatzResearch.WordTrace]
  refine ⟨42809267672802256115970629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28539511781868170743980419 42809267672802256115970629)
  ·
    refine ⟨8026737688650423021744493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42809267672802256115970629 8026737688650423021744493)
    ·
      refine ⟨3010026633243908633154185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8026737688650423021744493 3010026633243908633154185)
      ·
        refine ⟨2257519974932931474865639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010026633243908633154185 2257519974932931474865639)
        ·
          refine ⟨3386279962399397212298459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257519974932931474865639 3386279962399397212298459)
          ·
            refine ⟨5079419943599095818447689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386279962399397212298459 5079419943599095818447689)
            ·
              refine ⟨3809564957699321863835767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079419943599095818447689 3809564957699321863835767)
              ·
                refine ⟨5714347436548982795753651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809564957699321863835767 5714347436548982795753651)
                ·
                  refine ⟨8571521154823474193630477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714347436548982795753651 8571521154823474193630477)
                  ·
                    refine ⟨3214320433058802822611429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8571521154823474193630477 3214320433058802822611429)
                    ·
                      refine ⟨602685081198525529239643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3214320433058802822611429 602685081198525529239643)
                      ·
                        rfl

theorem cell23_1173725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1173725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173725 prefixEnd_1173725 := by exact prefixLift 1173725
  have htrace : WordTrace (prefixWord ++ tailWord_1173725) baseStart_1173725 baseEnd_1173725 := by
    simpa [prefixWord, tailWord_1173725, baseEnd_1173725] using wordTrace_append hprefix tailTrace_1173725
  have hstable : (prefixWord ++ tailWord_1173725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173725).length < 2 ^ (prefixWord ++ tailWord_1173725).sum := by decide
  have hdescent : baseEnd_1173725 < baseStart_1173725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173728 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1173728 : Nat := 118140960795 + 1173728 * 2 ^ 59
def prefixEnd_1173728 : Nat := 4983230072969 + 3 ^ 40 * 1173728 * 2
def baseEnd_1173728 : Nat := 602686621640489017502129

theorem tailTrace_1173728 : CollatzResearch.WordTrace tailWord_1173728 prefixEnd_1173728 602686621640489017502129 := by
  unfold tailWord_1173728
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404688545895693814164919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28539584727860925085553225 21404688545895693814164919)
  ·
    refine ⟨32107032818843540721247379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21404688545895693814164919 32107032818843540721247379)
    ·
      refine ⟨48160549228265311081871069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32107032818843540721247379 48160549228265311081871069)
      ·
        refine ⟨18060205960599491655701651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48160549228265311081871069 18060205960599491655701651)
        ·
          refine ⟨27090308940899237483552477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18060205960599491655701651 27090308940899237483552477)
          ·
            refine ⟨10158865852837214056332179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27090308940899237483552477 10158865852837214056332179)
            ·
              refine ⟨15238298779255821084498269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10158865852837214056332179 15238298779255821084498269)
              ·
                refine ⟨5714362042220932906686851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15238298779255821084498269 5714362042220932906686851)
                ·
                  refine ⟨8571543063331399360030277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714362042220932906686851 8571543063331399360030277)
                  ·
                    refine ⟨1607164324374637380005677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8571543063331399360030277 1607164324374637380005677)
                    ·
                      refine ⟨602686621640489017502129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607164324374637380005677 602686621640489017502129)
                      ·
                        rfl

theorem cell23_1173728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1173728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173728 prefixEnd_1173728 := by exact prefixLift 1173728
  have htrace : WordTrace (prefixWord ++ tailWord_1173728) baseStart_1173728 baseEnd_1173728 := by
    simpa [prefixWord, tailWord_1173728, baseEnd_1173728] using wordTrace_append hprefix tailTrace_1173728
  have hstable : (prefixWord ++ tailWord_1173728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173728).length < 2 ^ (prefixWord ++ tailWord_1173728).sum := by decide
  have hdescent : baseEnd_1173728 < baseStart_1173728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173775 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_1173775 : Nat := 118140960795 + 1173775 * 2 ^ 59
def prefixEnd_1173775 : Nat := 4983230072969 + 3 ^ 40 * 1173775 * 2
def baseEnd_1173775 : Nat := 602710755231250333614413

theorem tailTrace_1173775 : CollatzResearch.WordTrace tailWord_1173775 prefixEnd_1173775 602710755231250333614413 := by
  unfold tailWord_1173775
  simp only [CollatzResearch.WordTrace]
  refine ⟨42811091322621114655290779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28540727548414076436860519 42811091322621114655290779)
  ·
    refine ⟨64216636983931671982936169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42811091322621114655290779 64216636983931671982936169)
    ·
      refine ⟨48162477737948753987202127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64216636983931671982936169 48162477737948753987202127)
      ·
        refine ⟨72243716606923130980803191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48162477737948753987202127 72243716606923130980803191)
        ·
          refine ⟨108365574910384696471204787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72243716606923130980803191 108365574910384696471204787)
          ·
            refine ⟨162548362365577044706807181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108365574910384696471204787 162548362365577044706807181)
            ·
              refine ⟨60955635887091391765052693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162548362365577044706807181 60955635887091391765052693)
              ·
                refine ⟨2857295432207408988986845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60955635887091391765052693 2857295432207408988986845)
                ·
                  refine ⟨1071485787077778370870067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2857295432207408988986845 1071485787077778370870067)
                  ·
                    refine ⟨1607228680616667556305101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1071485787077778370870067 1607228680616667556305101)
                    ·
                      refine ⟨602710755231250333614413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607228680616667556305101 602710755231250333614413)
                      ·
                        rfl

theorem cell23_1173775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_1173775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173775 prefixEnd_1173775 := by exact prefixLift 1173775
  have htrace : WordTrace (prefixWord ++ tailWord_1173775) baseStart_1173775 baseEnd_1173775 := by
    simpa [prefixWord, tailWord_1173775, baseEnd_1173775] using wordTrace_append hprefix tailTrace_1173775
  have hstable : (prefixWord ++ tailWord_1173775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173775).length < 2 ^ (prefixWord ++ tailWord_1173775).sum := by decide
  have hdescent : baseEnd_1173775 < baseStart_1173775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173832 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_1173832 : Nat := 118140960795 + 1173832 * 2 ^ 59
def prefixEnd_1173832 : Nat := 4983230072969 + 3 ^ 40 * 1173832 * 2
def baseEnd_1173832 : Nat := 602740023628556610601651

theorem tailTrace_1173832 : CollatzResearch.WordTrace tailWord_1173832 prefixEnd_1173832 602740023628556610601651 := by
  unfold tailWord_1173832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21406585141707306695057875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28542113522276408926743833 21406585141707306695057875)
  ·
    refine ⟨32109877712560960042586813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21406585141707306695057875 32109877712560960042586813)
    ·
      refine ⟨12041204142210360015970055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32109877712560960042586813 12041204142210360015970055)
      ·
        refine ⟨18061806213315540023955083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041204142210360015970055 18061806213315540023955083)
        ·
          refine ⟨27092709319973310035932625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18061806213315540023955083 27092709319973310035932625)
          ·
            refine ⟨20319531989979982526949469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27092709319973310035932625 20319531989979982526949469)
            ·
              refine ⟨7619824496242493447606051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20319531989979982526949469 7619824496242493447606051)
              ·
                refine ⟨11429736744363740171409077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619824496242493447606051 11429736744363740171409077)
                ·
                  refine ⟨1071537819784100641069601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11429736744363740171409077 1071537819784100641069601)
                  ·
                    refine ⟨803653364838075480802201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071537819784100641069601 803653364838075480802201)
                    ·
                      refine ⟨602740023628556610601651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803653364838075480802201 602740023628556610601651)
                      ·
                        rfl

theorem cell23_1173832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_1173832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173832 prefixEnd_1173832 := by exact prefixLift 1173832
  have htrace : WordTrace (prefixWord ++ tailWord_1173832) baseStart_1173832 baseEnd_1173832 := by
    simpa [prefixWord, tailWord_1173832, baseEnd_1173832] using wordTrace_append hprefix tailTrace_1173832
  have hstable : (prefixWord ++ tailWord_1173832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173832).length < 2 ^ (prefixWord ++ tailWord_1173832).sum := by decide
  have hdescent : baseEnd_1173832 < baseStart_1173832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173866 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1173866 : Nat := 118140960795 + 1173866 * 2 ^ 59
def prefixEnd_1173866 : Nat := 4983230072969 + 3 ^ 40 * 1173866 * 2
def baseEnd_1173866 : Nat := 602757481970809477576495

theorem tailTrace_1173866 : CollatzResearch.WordTrace tailWord_1173866 prefixEnd_1173866 602757481970809477576495 := by
  unfold tailWord_1173866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10703602591322859299213363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28542940243527624797902301 10703602591322859299213363)
  ·
    refine ⟨16055403886984288948820045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10703602591322859299213363 16055403886984288948820045)
    ·
      refine ⟨6020776457619108355807517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16055403886984288948820045 6020776457619108355807517)
      ·
        refine ⟨2257791171607165633427819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6020776457619108355807517 2257791171607165633427819)
        ·
          refine ⟨3386686757410748450141729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257791171607165633427819 3386686757410748450141729)
          ·
            refine ⟨2540015068058061337606297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386686757410748450141729 2540015068058061337606297)
            ·
              refine ⟨1905011301043546003204723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540015068058061337606297 1905011301043546003204723)
              ·
                refine ⟨2857516951565319004807085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905011301043546003204723 2857516951565319004807085)
                ·
                  refine ⟨1071568856836994626802657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2857516951565319004807085 1071568856836994626802657)
                  ·
                    refine ⟨803676642627745970101993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071568856836994626802657 803676642627745970101993)
                    ·
                      refine ⟨602757481970809477576495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803676642627745970101993 602757481970809477576495)
                      ·
                        rfl

theorem cell23_1173866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1173866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173866 prefixEnd_1173866 := by exact prefixLift 1173866
  have htrace : WordTrace (prefixWord ++ tailWord_1173866) baseStart_1173866 baseEnd_1173866 := by
    simpa [prefixWord, tailWord_1173866, baseEnd_1173866] using wordTrace_append hprefix tailTrace_1173866
  have hstable : (prefixWord ++ tailWord_1173866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173866).length < 2 ^ (prefixWord ++ tailWord_1173866).sum := by decide
  have hdescent : baseEnd_1173866 < baseStart_1173866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173925 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_1173925 : Nat := 118140960795 + 1173925 * 2 ^ 59
def prefixEnd_1173925 : Nat := 4983230072969 + 3 ^ 40 * 1173925 * 2
def baseEnd_1173925 : Nat := 602787777329424746738723

theorem tailTrace_1173925 : CollatzResearch.WordTrace tailWord_1173925 prefixEnd_1173925 602787777329424746738723 := by
  unfold tailWord_1173925
  simp only [CollatzResearch.WordTrace]
  refine ⟨42816562272077690273251229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28544374848051793515500819 42816562272077690273251229)
  ·
    refine ⟨16056210852029133852469211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42816562272077690273251229 16056210852029133852469211)
    ·
      refine ⟨24084316278043700778703817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056210852029133852469211 24084316278043700778703817)
      ·
        refine ⟨18063237208532775584027863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24084316278043700778703817 18063237208532775584027863)
        ·
          refine ⟨27094855812799163376041795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18063237208532775584027863 27094855812799163376041795)
          ·
            refine ⟨40642283719198745064062693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27094855812799163376041795 40642283719198745064062693)
            ·
              refine ⟨7620428197349764699511755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40642283719198745064062693 7620428197349764699511755)
              ·
                refine ⟨11430642296024647049267633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7620428197349764699511755 11430642296024647049267633)
                ·
                  refine ⟨8572981722018485286950725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11430642296024647049267633 8572981722018485286950725)
                  ·
                    refine ⟨1607434072878465991303261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8572981722018485286950725 1607434072878465991303261)
                    ·
                      refine ⟨602787777329424746738723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607434072878465991303261 602787777329424746738723)
                      ·
                        rfl

theorem cell23_1173925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_1173925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173925 prefixEnd_1173925 := by exact prefixLift 1173925
  have htrace : WordTrace (prefixWord ++ tailWord_1173925) baseStart_1173925 baseEnd_1173925 := by
    simpa [prefixWord, tailWord_1173925, baseEnd_1173925] using wordTrace_append hprefix tailTrace_1173925
  have hstable : (prefixWord ++ tailWord_1173925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173925).length < 2 ^ (prefixWord ++ tailWord_1173925).sum := by decide
  have hdescent : baseEnd_1173925 < baseStart_1173925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173955 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3]
def baseStart_1173955 : Nat := 118140960795 + 1173955 * 2 ^ 59
def prefixEnd_1173955 : Nat := 4983230072969 + 3 ^ 40 * 1173955 * 2
def baseEnd_1173955 : Nat := 602803181749059629363585

theorem tailTrace_1173955 : CollatzResearch.WordTrace tailWord_1173955 prefixEnd_1173955 602803181749059629363585 := by
  unfold tailWord_1173955
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817656461969005396843319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28545104307979336931228879 42817656461969005396843319)
  ·
    refine ⟨64226484692953508095264979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42817656461969005396843319 64226484692953508095264979)
    ·
      refine ⟨96339727039430262142897469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64226484692953508095264979 96339727039430262142897469)
      ·
        refine ⟨36127397639786348303586551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96339727039430262142897469 36127397639786348303586551)
        ·
          refine ⟨54191096459679522455379827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36127397639786348303586551 54191096459679522455379827)
          ·
            refine ⟨81286644689519283683069741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54191096459679522455379827 81286644689519283683069741)
            ·
              refine ⟨30482491758569731381151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81286644689519283683069741 30482491758569731381151153)
              ·
                refine ⟨22861868818927298535863365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30482491758569731381151153 22861868818927298535863365)
                ·
                  refine ⟨4286600403548868475474381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22861868818927298535863365 4286600403548868475474381)
                  ·
                    refine ⟨1607475151330825678302893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286600403548868475474381 1607475151330825678302893)
                    ·
                      refine ⟨602803181749059629363585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607475151330825678302893 602803181749059629363585)
                      ·
                        rfl

theorem cell23_1173955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_1173955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173955 prefixEnd_1173955 := by exact prefixLift 1173955
  have htrace : WordTrace (prefixWord ++ tailWord_1173955) baseStart_1173955 baseEnd_1173955 := by
    simpa [prefixWord, tailWord_1173955, baseEnd_1173955] using wordTrace_append hprefix tailTrace_1173955
  have hstable : (prefixWord ++ tailWord_1173955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173955).length < 2 ^ (prefixWord ++ tailWord_1173955).sum := by decide
  have hdescent : baseEnd_1173955 < baseStart_1173955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173956 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1173956 : Nat := 118140960795 + 1173956 * 2 ^ 59
def prefixEnd_1173956 : Nat := 4983230072969 + 3 ^ 40 * 1173956 * 2
def baseEnd_1173956 : Nat := 602803695229714125451081

theorem tailTrace_1173956 : CollatzResearch.WordTrace tailWord_1173956 prefixEnd_1173956 602803695229714125451081 := by
  unfold tailWord_1173956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21408846467482691283814861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28545128623310255045086481 21408846467482691283814861)
  ·
    refine ⟨8028317425306009231430573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21408846467482691283814861 8028317425306009231430573)
    ·
      refine ⟨3010619034489753461786465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8028317425306009231430573 3010619034489753461786465)
      ·
        refine ⟨2257964275867315096339849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3010619034489753461786465 2257964275867315096339849)
        ·
          refine ⟨1693473206900486322254887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2257964275867315096339849 1693473206900486322254887)
          ·
            refine ⟨2540209810350729483382331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693473206900486322254887 2540209810350729483382331)
            ·
              refine ⟨3810314715526094225073497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540209810350729483382331 3810314715526094225073497)
              ·
                refine ⟨2857736036644570668805123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810314715526094225073497 2857736036644570668805123)
                ·
                  refine ⟨4286604054966856003207685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857736036644570668805123 4286604054966856003207685)
                  ·
                    refine ⟨803738260306285500601441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4286604054966856003207685 803738260306285500601441)
                    ·
                      refine ⟨602803695229714125451081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803738260306285500601441 602803695229714125451081)
                      ·
                        rfl

theorem cell23_1173956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1173956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173956 prefixEnd_1173956 := by exact prefixLift 1173956
  have htrace : WordTrace (prefixWord ++ tailWord_1173956) baseStart_1173956 baseEnd_1173956 := by
    simpa [prefixWord, tailWord_1173956, baseEnd_1173956] using wordTrace_append hprefix tailTrace_1173956
  have hstable : (prefixWord ++ tailWord_1173956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173956).length < 2 ^ (prefixWord ++ tailWord_1173956).sum := by decide
  have hdescent : baseEnd_1173956 < baseStart_1173956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173962 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_1173962 : Nat := 118140960795 + 1173962 * 2 ^ 59
def prefixEnd_1173962 : Nat := 4983230072969 + 3 ^ 40 * 1173962 * 2
def baseEnd_1173962 : Nat := 66978530679293455775117

theorem tailTrace_1173962 : CollatzResearch.WordTrace tailWord_1173962 prefixEnd_1173962 66978530679293455775117 := by
  unfold tailWord_1173962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704477943235911398087035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28545274515295763728232093 10704477943235911398087035)
  ·
    refine ⟨16056716914853867097130553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10704477943235911398087035 16056716914853867097130553)
    ·
      refine ⟨12042537686140400322847915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16056716914853867097130553 12042537686140400322847915)
      ·
        refine ⟨18063806529210600484271873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12042537686140400322847915 18063806529210600484271873)
        ·
          refine ⟨13547854896907950363203905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18063806529210600484271873 13547854896907950363203905)
          ·
            refine ⟨10160891172680962772402929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13547854896907950363203905 10160891172680962772402929)
            ·
              refine ⟨7620668379510722079302197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10160891172680962772402929 7620668379510722079302197)
              ·
                refine ⟨714437660579130194934581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7620668379510722079302197 714437660579130194934581)
                ·
                  refine ⟨66978530679293455775117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714437660579130194934581 66978530679293455775117)
                  ·
                    rfl

theorem cell23_1173962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_1173962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173962 prefixEnd_1173962 := by exact prefixLift 1173962
  have htrace : WordTrace (prefixWord ++ tailWord_1173962) baseStart_1173962 baseEnd_1173962 := by
    simpa [prefixWord, tailWord_1173962, baseEnd_1173962] using wordTrace_append hprefix tailTrace_1173962
  have hstable : (prefixWord ++ tailWord_1173962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173962).length < 2 ^ (prefixWord ++ tailWord_1173962).sum := by decide
  have hdescent : baseEnd_1173962 < baseStart_1173962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173985 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1173985 : Nat := 118140960795 + 1173985 * 2 ^ 59
def prefixEnd_1173985 : Nat := 4983230072969 + 3 ^ 40 * 1173985 * 2
def baseEnd_1173985 : Nat := 602818586168694511988447

theorem tailTrace_1173985 : CollatzResearch.WordTrace tailWord_1173985 prefixEnd_1173985 602818586168694511988447 := by
  unfold tailWord_1173985
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818750651860320520435409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28545833767906880346956939 42818750651860320520435409)
  ·
    refine ⟨32114062988895240390326557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42818750651860320520435409 32114062988895240390326557)
    ·
      refine ⟨12042773620835715146372459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32114062988895240390326557 12042773620835715146372459)
      ·
        refine ⟨18064160431253572719558689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12042773620835715146372459 18064160431253572719558689)
        ·
          refine ⟨13548120323440179539669017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18064160431253572719558689 13548120323440179539669017)
          ·
            refine ⟨10161090242580134654751763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13548120323440179539669017 10161090242580134654751763)
            ·
              refine ⟨15241635363870201982127645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10161090242580134654751763 15241635363870201982127645)
              ·
                refine ⟨5715613261451325743297867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15241635363870201982127645 5715613261451325743297867)
                ·
                  refine ⟨8573419892176988614946801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715613261451325743297867 8573419892176988614946801)
                  ·
                    refine ⟨6430064919132741461210101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8573419892176988614946801 6430064919132741461210101)
                    ·
                      refine ⟨602818586168694511988447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6430064919132741461210101 602818586168694511988447)
                      ·
                        rfl

theorem cell23_1173985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1173985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173985 prefixEnd_1173985 := by exact prefixLift 1173985
  have htrace : WordTrace (prefixWord ++ tailWord_1173985) baseStart_1173985 baseEnd_1173985 := by
    simpa [prefixWord, tailWord_1173985, baseEnd_1173985] using wordTrace_append hprefix tailTrace_1173985
  have hstable : (prefixWord ++ tailWord_1173985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173985).length < 2 ^ (prefixWord ++ tailWord_1173985).sum := by decide
  have hdescent : baseEnd_1173985 < baseStart_1173985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173986 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1173986 : Nat := 118140960795 + 1173986 * 2 ^ 59
def prefixEnd_1173986 : Nat := 4983230072969 + 3 ^ 40 * 1173986 * 2
def baseEnd_1173986 : Nat := 602819099649349008075943

theorem tailTrace_1173986 : CollatzResearch.WordTrace tailWord_1173986 prefixEnd_1173986 602819099649349008075943 := by
  unfold tailWord_1173986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10704696781214174422805453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28545858083237798460814541 10704696781214174422805453)
  ·
    refine ⟨4014261292955315408552045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10704696781214174422805453 4014261292955315408552045)
    ·
      refine ⟨1505347984858243278207017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4014261292955315408552045 1505347984858243278207017)
      ·
        refine ⟨1129010988643682458655263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1505347984858243278207017 1129010988643682458655263)
        ·
          refine ⟨1693516482965523687982895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129010988643682458655263 1693516482965523687982895)
          ·
            refine ⟨2540274724448285531974343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693516482965523687982895 2540274724448285531974343)
            ·
              refine ⟨3810412086672428297961515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540274724448285531974343 3810412086672428297961515)
              ·
                refine ⟨5715618130008642446942273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810412086672428297961515 5715618130008642446942273)
                ·
                  refine ⟨4286713597506481835206705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715618130008642446942273 4286713597506481835206705)
                  ·
                    refine ⟨3215035198129861376405029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4286713597506481835206705 3215035198129861376405029)
                    ·
                      refine ⟨602819099649349008075943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3215035198129861376405029 602819099649349008075943)
                      ·
                        rfl

theorem cell23_1173986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1173986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173986 prefixEnd_1173986 := by exact prefixLift 1173986
  have htrace : WordTrace (prefixWord ++ tailWord_1173986) baseStart_1173986 baseEnd_1173986 := by
    simpa [prefixWord, tailWord_1173986, baseEnd_1173986] using wordTrace_append hprefix tailTrace_1173986
  have hstable : (prefixWord ++ tailWord_1173986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173986).length < 2 ^ (prefixWord ++ tailWord_1173986).sum := by decide
  have hdescent : baseEnd_1173986 < baseStart_1173986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173989 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1173989 : Nat := 118140960795 + 1173989 * 2 ^ 59
def prefixEnd_1173989 : Nat := 4983230072969 + 3 ^ 40 * 1173989 * 2
def baseEnd_1173989 : Nat := 602820640091312496338429

theorem tailTrace_1173989 : CollatzResearch.WordTrace tailWord_1173989 prefixEnd_1173989 602820640091312496338429 := by
  unfold tailWord_1173989
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818896543845829203581021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28545931029230552802387347 42818896543845829203581021)
  ·
    refine ⟨16057086203942185951342883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42818896543845829203581021 16057086203942185951342883)
    ·
      refine ⟨24085629305913278927014325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16057086203942185951342883 24085629305913278927014325)
      ·
        refine ⟨2258027747429369899407593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24085629305913278927014325 2258027747429369899407593)
        ·
          refine ⟨1693520810572027424555695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2258027747429369899407593 1693520810572027424555695)
          ·
            refine ⟨2540281215858041136833543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693520810572027424555695 2540281215858041136833543)
            ·
              refine ⟨3810421823787061705250315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540281215858041136833543 3810421823787061705250315)
              ·
                refine ⟨5715632735680592557875473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810421823787061705250315 5715632735680592557875473)
                ·
                  refine ⟨4286724551760444418406605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715632735680592557875473 4286724551760444418406605)
                  ·
                    refine ⟨1607521706910166656902477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4286724551760444418406605 1607521706910166656902477)
                    ·
                      refine ⟨602820640091312496338429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607521706910166656902477 602820640091312496338429)
                      ·
                        rfl

theorem cell23_1173989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1173989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173989 prefixEnd_1173989 := by exact prefixLift 1173989
  have htrace : WordTrace (prefixWord ++ tailWord_1173989) baseStart_1173989 baseEnd_1173989 := by
    simpa [prefixWord, tailWord_1173989, baseEnd_1173989] using wordTrace_append hprefix tailTrace_1173989
  have hstable : (prefixWord ++ tailWord_1173989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173989).length < 2 ^ (prefixWord ++ tailWord_1173989).sum := by decide
  have hdescent : baseEnd_1173989 < baseStart_1173989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1173995 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_1173995 : Nat := 118140960795 + 1173995 * 2 ^ 59
def prefixEnd_1173995 : Nat := 4983230072969 + 3 ^ 40 * 1173995 * 2
def baseEnd_1173995 : Nat := 602823720975239472863401

theorem tailTrace_1173995 : CollatzResearch.WordTrace tailWord_1173995 prefixEnd_1173995 602823720975239472863401 := by
  unfold tailWord_1173995
  simp only [CollatzResearch.WordTrace]
  refine ⟨42819115381824092228299439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28546076921216061485532959 42819115381824092228299439)
  ·
    refine ⟨64228673072736138342449159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42819115381824092228299439 64228673072736138342449159)
    ·
      refine ⟨96343009609104207513673739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64228673072736138342449159 96343009609104207513673739)
      ·
        refine ⟨144514514413656311270510609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96343009609104207513673739 144514514413656311270510609)
        ·
          refine ⟨108385885810242233452882957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144514514413656311270510609 108385885810242233452882957)
          ·
            refine ⟨40644707178840837544831109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108385885810242233452882957 40644707178840837544831109)
            ·
              refine ⟨7620882596032657039655833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40644707178840837544831109 7620882596032657039655833)
              ·
                refine ⟨5715661947024492779741875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7620882596032657039655833 5715661947024492779741875)
                ·
                  refine ⟨8573492920536739169612813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715661947024492779741875 8573492920536739169612813)
                  ·
                    refine ⟨3215059845201277188604805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8573492920536739169612813 3215059845201277188604805)
                    ·
                      refine ⟨602823720975239472863401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3215059845201277188604805 602823720975239472863401)
                      ·
                        rfl

theorem cell23_1173995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_1173995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1173995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1173995 prefixEnd_1173995 := by exact prefixLift 1173995
  have htrace : WordTrace (prefixWord ++ tailWord_1173995) baseStart_1173995 baseEnd_1173995 := by
    simpa [prefixWord, tailWord_1173995, baseEnd_1173995] using wordTrace_append hprefix tailTrace_1173995
  have hstable : (prefixWord ++ tailWord_1173995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1173995).length < 2 ^ (prefixWord ++ tailWord_1173995).sum := by decide
  have hdescent : baseEnd_1173995 < baseStart_1173995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1173995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174012 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_1174012 : Nat := 118140960795 + 1174012 * 2 ^ 59
def prefixEnd_1174012 : Nat := 4983230072969 + 3 ^ 40 * 1174012 * 2
def baseEnd_1174012 : Nat := 602832450146365906350823

theorem tailTrace_1174012 : CollatzResearch.WordTrace tailWord_1174012 prefixEnd_1174012 602832450146365906350823 := by
  unfold tailWord_1174012
  simp only [CollatzResearch.WordTrace]
  refine ⟨21409867711381252065834145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28546490281841669421112193 21409867711381252065834145)
  ·
    refine ⟨16057400783535939049375609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21409867711381252065834145 16057400783535939049375609)
    ·
      refine ⟨12043050587651954287031707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16057400783535939049375609 12043050587651954287031707)
      ·
        refine ⟨18064575881477931430547561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12043050587651954287031707 18064575881477931430547561)
        ·
          refine ⟨13548431911108448572910671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18064575881477931430547561 13548431911108448572910671)
          ·
            refine ⟨20322647866662672859366007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13548431911108448572910671 20322647866662672859366007)
            ·
              refine ⟨30483971799994009289049011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20322647866662672859366007 30483971799994009289049011)
              ·
                refine ⟨45725957699991013933573517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30483971799994009289049011 45725957699991013933573517)
                ·
                  refine ⟨17147234137496630225090069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45725957699991013933573517 17147234137496630225090069)
                  ·
                    refine ⟨803776600195154541801097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17147234137496630225090069 803776600195154541801097)
                    ·
                      refine ⟨602832450146365906350823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803776600195154541801097 602832450146365906350823)
                      ·
                        rfl

theorem cell23_1174012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_1174012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174012 prefixEnd_1174012 := by exact prefixLift 1174012
  have htrace : WordTrace (prefixWord ++ tailWord_1174012) baseStart_1174012 baseEnd_1174012 := by
    simpa [prefixWord, tailWord_1174012, baseEnd_1174012] using wordTrace_append hprefix tailTrace_1174012
  have hstable : (prefixWord ++ tailWord_1174012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174012).length < 2 ^ (prefixWord ++ tailWord_1174012).sum := by decide
  have hdescent : baseEnd_1174012 < baseStart_1174012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174035 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 8]
def baseStart_1174035 : Nat := 118140960795 + 1174035 * 2 ^ 59
def prefixEnd_1174035 : Nat := 4983230072969 + 3 ^ 40 * 1174035 * 2
def baseEnd_1174035 : Nat := 66982695577935479595913

theorem tailTrace_1174035 : CollatzResearch.WordTrace tailWord_1174035 prefixEnd_1174035 66982695577935479595913 := by
  unfold tailWord_1174035
  simp only [CollatzResearch.WordTrace]
  refine ⟨42820574301679179059755559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28547049534452786039837039 42820574301679179059755559)
  ·
    refine ⟨64230861452518768589633339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42820574301679179059755559 64230861452518768589633339)
    ·
      refine ⟨96346292178778152884450009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64230861452518768589633339 96346292178778152884450009)
      ·
        refine ⟨72259719134083614663337507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96346292178778152884450009 72259719134083614663337507)
        ·
          refine ⟨108389578701125421995006261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72259719134083614663337507 108389578701125421995006261)
          ·
            refine ⟨10161523003230508312031837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108389578701125421995006261 10161523003230508312031837)
            ·
              refine ⟨3810571126211440617011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10161523003230508312031837 3810571126211440617011939)
              ·
                refine ⟨5715856689317160925517909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810571126211440617011939 5715856689317160925517909)
                ·
                  refine ⟨66982695577935479595913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5715856689317160925517909 66982695577935479595913)
                  ·
                    rfl

theorem cell23_1174035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 8].length) (baseStart_1174035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174035 prefixEnd_1174035 := by exact prefixLift 1174035
  have htrace : WordTrace (prefixWord ++ tailWord_1174035) baseStart_1174035 baseEnd_1174035 := by
    simpa [prefixWord, tailWord_1174035, baseEnd_1174035] using wordTrace_append hprefix tailTrace_1174035
  have hstable : (prefixWord ++ tailWord_1174035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174035).length < 2 ^ (prefixWord ++ tailWord_1174035).sum := by decide
  have hdescent : baseEnd_1174035 < baseStart_1174035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174133 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1174133 : Nat := 118140960795 + 1174133 * 2 ^ 59
def prefixEnd_1174133 : Nat := 4983230072969 + 3 ^ 40 * 1174133 * 2
def baseEnd_1174133 : Nat := 200964860435186644312589

theorem tailTrace_1174133 : CollatzResearch.WordTrace tailWord_1174133 prefixEnd_1174133 200964860435186644312589 := by
  unfold tailWord_1174133
  simp only [CollatzResearch.WordTrace]
  refine ⟨42824148655324141796823053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28549432436882761197882035 42824148655324141796823053)
  ·
    refine ⟨16059055745746553173808645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42824148655324141796823053 16059055745746553173808645)
    ·
      refine ⟨3011072952327478720089121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16059055745746553173808645 3011072952327478720089121)
      ·
        refine ⟨2258304714245609040066841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3011072952327478720089121 2258304714245609040066841)
        ·
          refine ⟨1693728535684206780050131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2258304714245609040066841 1693728535684206780050131)
          ·
            refine ⟨2540592803526310170075197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693728535684206780050131 2540592803526310170075197)
            ·
              refine ⟨952722301322366313778199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540592803526310170075197 952722301322366313778199)
              ·
                refine ⟨1429083451983549470667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952722301322366313778199 1429083451983549470667299)
                ·
                  refine ⟨2143625177975324206000949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429083451983549470667299 2143625177975324206000949)
                  ·
                    refine ⟨200964860435186644312589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2143625177975324206000949 200964860435186644312589)
                    ·
                      rfl

theorem cell23_1174133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1174133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174133 prefixEnd_1174133 := by exact prefixLift 1174133
  have htrace : WordTrace (prefixWord ++ tailWord_1174133) baseStart_1174133 baseEnd_1174133 := by
    simpa [prefixWord, tailWord_1174133, baseEnd_1174133] using wordTrace_append hprefix tailTrace_1174133
  have hstable : (prefixWord ++ tailWord_1174133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174133).length < 2 ^ (prefixWord ++ tailWord_1174133).sum := by decide
  have hdescent : baseEnd_1174133 < baseStart_1174133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174169 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_1174169 : Nat := 118140960795 + 1174169 * 2 ^ 59
def prefixEnd_1174169 : Nat := 4983230072969 + 3 ^ 40 * 1174169 * 2
def baseEnd_1174169 : Nat := 602913066609121792087601

theorem tailTrace_1174169 : CollatzResearch.WordTrace tailWord_1174169 prefixEnd_1174169 602913066609121792087601 := by
  unfold tailWord_1174169
  simp only [CollatzResearch.WordTrace]
  refine ⟨42825461683193719945133561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28550307788795813296755707 42825461683193719945133561)
  ·
    refine ⟨32119096262395289958850171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42825461683193719945133561 32119096262395289958850171)
    ·
      refine ⟨48178644393592934938275257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32119096262395289958850171 48178644393592934938275257)
      ·
        refine ⟨36133983295194701203706443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48178644393592934938275257 36133983295194701203706443)
        ·
          refine ⟨54200974942792051805559665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36133983295194701203706443 54200974942792051805559665)
          ·
            refine ⟨40650731207094038854169749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54200974942792051805559665 40650731207094038854169749)
            ·
              refine ⟨1905503025332533071289207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40650731207094038854169749 1905503025332533071289207)
              ·
                refine ⟨2858254537998799606933811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905503025332533071289207 2858254537998799606933811)
                ·
                  refine ⟨4287381806998199410400717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858254537998799606933811 4287381806998199410400717)
                  ·
                    refine ⟨1607768177624324778900269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4287381806998199410400717 1607768177624324778900269)
                    ·
                      refine ⟨602913066609121792087601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607768177624324778900269 602913066609121792087601)
                      ·
                        rfl

theorem cell23_1174169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_1174169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174169 prefixEnd_1174169 := by exact prefixLift 1174169
  have htrace : WordTrace (prefixWord ++ tailWord_1174169) baseStart_1174169 baseEnd_1174169 := by
    simpa [prefixWord, tailWord_1174169, baseEnd_1174169] using wordTrace_append hprefix tailTrace_1174169
  have hstable : (prefixWord ++ tailWord_1174169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174169).length < 2 ^ (prefixWord ++ tailWord_1174169).sum := by decide
  have hdescent : baseEnd_1174169 < baseStart_1174169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174170 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1174170 : Nat := 118140960795 + 1174170 * 2 ^ 59
def prefixEnd_1174170 : Nat := 4983230072969 + 3 ^ 40 * 1174170 * 2
def baseEnd_1174170 : Nat := 602913580089776288175097

theorem tailTrace_1174170 : CollatzResearch.WordTrace tailWord_1174170 prefixEnd_1174170 602913580089776288175097 := by
  unfold tailWord_1174170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706374539047524278979991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28550332104126731410613309 10706374539047524278979991)
  ·
    refine ⟨16059561808571286418469987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706374539047524278979991 16059561808571286418469987)
    ·
      refine ⟨24089342712856929627704981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059561808571286418469987 24089342712856929627704981)
      ·
        refine ⟨1129187939665168576298671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24089342712856929627704981 1129187939665168576298671)
        ·
          refine ⟨1693781909497752864448007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129187939665168576298671 1693781909497752864448007)
          ·
            refine ⟨2540672864246629296672011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693781909497752864448007 2540672864246629296672011)
            ·
              refine ⟨3811009296369943945008017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540672864246629296672011 3811009296369943945008017)
              ·
                refine ⟨2858256972277457958756013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3811009296369943945008017 2858256972277457958756013)
                ·
                  refine ⟨1071846364604046734533505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2858256972277457958756013 1071846364604046734533505)
                  ·
                    refine ⟨803884773453035050900129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071846364604046734533505 803884773453035050900129)
                    ·
                      refine ⟨602913580089776288175097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803884773453035050900129 602913580089776288175097)
                      ·
                        rfl

theorem cell23_1174170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1174170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174170 prefixEnd_1174170 := by exact prefixLift 1174170
  have htrace : WordTrace (prefixWord ++ tailWord_1174170) baseStart_1174170 baseEnd_1174170 := by
    simpa [prefixWord, tailWord_1174170, baseEnd_1174170] using wordTrace_append hprefix tailTrace_1174170
  have hstable : (prefixWord ++ tailWord_1174170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174170).length < 2 ^ (prefixWord ++ tailWord_1174170).sum := by decide
  have hdescent : baseEnd_1174170 < baseStart_1174170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174190 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1174190 : Nat := 118140960795 + 1174190 * 2 ^ 59
def prefixEnd_1174190 : Nat := 4983230072969 + 3 ^ 40 * 1174190 * 2
def baseEnd_1174190 : Nat := 602923849702866209925005

theorem tailTrace_1174190 : CollatzResearch.WordTrace tailWord_1174190 prefixEnd_1174190 602923849702866209925005 := by
  unfold tailWord_1174190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353278452014705066456003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28550818410745093687765349 5353278452014705066456003)
  ·
    refine ⟨8029917678022057599684005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353278452014705066456003 8029917678022057599684005)
    ·
      refine ⟨1505609564629135799940751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8029917678022057599684005 1505609564629135799940751)
      ·
        refine ⟨2258414346943703699911127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505609564629135799940751 2258414346943703699911127)
        ·
          refine ⟨3387621520415555549866691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258414346943703699911127 3387621520415555549866691)
          ·
            refine ⟨5081432280623333324800037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387621520415555549866691 5081432280623333324800037)
            ·
              refine ⟨952768552616874998400007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5081432280623333324800037 952768552616874998400007)
              ·
                refine ⟨1429152828925312497600011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952768552616874998400007 1429152828925312497600011)
                ·
                  refine ⟨2143729243387968746400017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429152828925312497600011 2143729243387968746400017)
                  ·
                    refine ⟨1607796932540976559800013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2143729243387968746400017 1607796932540976559800013)
                    ·
                      refine ⟨602923849702866209925005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607796932540976559800013 602923849702866209925005)
                      ·
                        rfl

theorem cell23_1174190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1174190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174190 prefixEnd_1174190 := by exact prefixLift 1174190
  have htrace : WordTrace (prefixWord ++ tailWord_1174190) baseStart_1174190 baseEnd_1174190 := by
    simpa [prefixWord, tailWord_1174190, baseEnd_1174190] using wordTrace_append hprefix tailTrace_1174190
  have hstable : (prefixWord ++ tailWord_1174190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174190).length < 2 ^ (prefixWord ++ tailWord_1174190).sum := by decide
  have hdescent : baseEnd_1174190 < baseStart_1174190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174202 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_1174202 : Nat := 118140960795 + 1174202 * 2 ^ 59
def prefixEnd_1174202 : Nat := 4983230072969 + 3 ^ 40 * 1174202 * 2
def baseEnd_1174202 : Nat := 200976670490240054324983

theorem tailTrace_1174202 : CollatzResearch.WordTrace tailWord_1174202 prefixEnd_1174202 200976670490240054324983 := by
  unfold tailWord_1174202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706666323018541645271215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28551110194716111054056573 10706666323018541645271215)
  ·
    refine ⟨16059999484527812467906823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10706666323018541645271215 16059999484527812467906823)
    ·
      refine ⟨24089999226791718701860235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059999484527812467906823 24089999226791718701860235)
      ·
        refine ⟨36134998840187578052790353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24089999226791718701860235 36134998840187578052790353)
        ·
          refine ⟨27101249130140683539592765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36134998840187578052790353 27101249130140683539592765)
          ·
            refine ⟨10162968423802756327347287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27101249130140683539592765 10162968423802756327347287)
            ·
              refine ⟨15244452635704134491020931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10162968423802756327347287 15244452635704134491020931)
              ·
                refine ⟨22866678953556201736531397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15244452635704134491020931 22866678953556201736531397)
                ·
                  refine ⟨4287502303791787825599637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22866678953556201736531397 4287502303791787825599637)
                  ·
                    refine ⟨200976670490240054324983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4287502303791787825599637 200976670490240054324983)
                    ·
                      rfl

theorem cell23_1174202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_1174202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174202 prefixEnd_1174202 := by exact prefixLift 1174202
  have htrace : WordTrace (prefixWord ++ tailWord_1174202) baseStart_1174202 baseEnd_1174202 := by
    simpa [prefixWord, tailWord_1174202, baseEnd_1174202] using wordTrace_append hprefix tailTrace_1174202
  have hstable : (prefixWord ++ tailWord_1174202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174202).length < 2 ^ (prefixWord ++ tailWord_1174202).sum := by decide
  have hdescent : baseEnd_1174202 < baseStart_1174202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174220 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1174220 : Nat := 118140960795 + 1174220 * 2 ^ 59
def prefixEnd_1174220 : Nat := 4983230072969 + 3 ^ 40 * 1174220 * 2
def baseEnd_1174220 : Nat := 602939254122501092549867

theorem tailTrace_1174220 : CollatzResearch.WordTrace tailWord_1174220 prefixEnd_1174220 602939254122501092549867 := by
  unfold tailWord_1174220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21413660903004477827620057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28551547870672637103493409 21413660903004477827620057)
  ·
    refine ⟨16060245677253358370715043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21413660903004477827620057 16060245677253358370715043)
    ·
      refine ⟨24090368515880037556072565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16060245677253358370715043 24090368515880037556072565)
      ·
        refine ⟨2258472048363753520881803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24090368515880037556072565 2258472048363753520881803)
        ·
          refine ⟨3387708072545630281322705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258472048363753520881803 3387708072545630281322705)
          ·
            refine ⟨2540781054409222710992029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3387708072545630281322705 2540781054409222710992029)
            ·
              refine ⟨952792895403458516622011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2540781054409222710992029 952792895403458516622011)
              ·
                refine ⟨1429189343105187774933017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952792895403458516622011 1429189343105187774933017)
                ·
                  refine ⟨1071892007328890831199763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1429189343105187774933017 1071892007328890831199763)
                  ·
                    refine ⟨1607838010993336246799645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1071892007328890831199763 1607838010993336246799645)
                    ·
                      refine ⟨602939254122501092549867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1607838010993336246799645 602939254122501092549867)
                      ·
                        rfl

theorem cell23_1174220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1174220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174220 prefixEnd_1174220 := by exact prefixLift 1174220
  have htrace : WordTrace (prefixWord ++ tailWord_1174220) baseStart_1174220 baseEnd_1174220 := by
    simpa [prefixWord, tailWord_1174220, baseEnd_1174220] using wordTrace_append hprefix tailTrace_1174220
  have hstable : (prefixWord ++ tailWord_1174220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174220).length < 2 ^ (prefixWord ++ tailWord_1174220).sum := by decide
  have hdescent : baseEnd_1174220 < baseStart_1174220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174243 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1174243 : Nat := 118140960795 + 1174243 * 2 ^ 59
def prefixEnd_1174243 : Nat := 4983230072969 + 3 ^ 40 * 1174243 * 2
def baseEnd_1174243 : Nat := 602951064177554502562261

theorem tailTrace_1174243 : CollatzResearch.WordTrace tailWord_1174243 prefixEnd_1174243 602951064177554502562261 := by
  unfold tailWord_1174243
  simp only [CollatzResearch.WordTrace]
  refine ⟨42828160684925630583327383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28552107123283753722218255 42828160684925630583327383)
  ·
    refine ⟨64242241027388445874991075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42828160684925630583327383 64242241027388445874991075)
    ·
      refine ⟨96363361541082668812486613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64242241027388445874991075 96363361541082668812486613)
      ·
        refine ⟨2258516286119125050292655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96363361541082668812486613 2258516286119125050292655)
        ·
          refine ⟨3387774429178687575438983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258516286119125050292655 3387774429178687575438983)
          ·
            refine ⟨5081661643768031363158475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387774429178687575438983 5081661643768031363158475)
            ·
              refine ⟨7622492465652047044737713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081661643768031363158475 7622492465652047044737713)
              ·
                refine ⟨5716869349239035283553285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7622492465652047044737713 5716869349239035283553285)
                ·
                  refine ⟨1071913002982319115666241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5716869349239035283553285 1071913002982319115666241)
                  ·
                    refine ⟨803934752236739336749681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1071913002982319115666241 803934752236739336749681)
                    ·
                      refine ⟨602951064177554502562261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803934752236739336749681 602951064177554502562261)
                      ·
                        rfl

theorem cell23_1174243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1174243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174243 prefixEnd_1174243 := by exact prefixLift 1174243
  have htrace : WordTrace (prefixWord ++ tailWord_1174243) baseStart_1174243 baseEnd_1174243 := by
    simpa [prefixWord, tailWord_1174243, baseEnd_1174243] using wordTrace_append hprefix tailTrace_1174243
  have hstable : (prefixWord ++ tailWord_1174243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174243).length < 2 ^ (prefixWord ++ tailWord_1174243).sum := by decide
  have hdescent : baseEnd_1174243 < baseStart_1174243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174316 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_1174316 : Nat := 118140960795 + 1174316 * 2 ^ 59
def prefixEnd_1174316 : Nat := 4983230072969 + 3 ^ 40 * 1174316 * 2
def baseEnd_1174316 : Nat := 602988548265332716949425

theorem tailTrace_1174316 : CollatzResearch.WordTrace tailWord_1174316 prefixEnd_1174316 602988548265332716949425 := by
  unfold tailWord_1174316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21415411606830582025367401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28553882142440776033823201 21415411606830582025367401)
  ·
    refine ⟨16061558705122936519025551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21415411606830582025367401 16061558705122936519025551)
    ·
      refine ⟨24092338057684404778538327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16061558705122936519025551 24092338057684404778538327)
      ·
        refine ⟨36138507086526607167807491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24092338057684404778538327 36138507086526607167807491)
        ·
          refine ⟨54207760629789910751711237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36138507086526607167807491 54207760629789910751711237)
          ·
            refine ⟨10163955118085608265945857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54207760629789910751711237 10163955118085608265945857)
            ·
              refine ⟨7622966338564206199459393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10163955118085608265945857 7622966338564206199459393)
              ·
                refine ⟨5717224753923154649594545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7622966338564206199459393 5717224753923154649594545)
                ·
                  refine ⟨4287918565442365987195909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5717224753923154649594545 4287918565442365987195909)
                  ·
                    refine ⟨803984731020443622599233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287918565442365987195909 803984731020443622599233)
                    ·
                      refine ⟨602988548265332716949425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 803984731020443622599233 602988548265332716949425)
                      ·
                        rfl

theorem cell23_1174316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_1174316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174316 prefixEnd_1174316 := by exact prefixLift 1174316
  have htrace : WordTrace (prefixWord ++ tailWord_1174316) baseStart_1174316 baseEnd_1174316 := by
    simpa [prefixWord, tailWord_1174316, baseEnd_1174316] using wordTrace_append hprefix tailTrace_1174316
  have hstable : (prefixWord ++ tailWord_1174316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174316).length < 2 ^ (prefixWord ++ tailWord_1174316).sum := by decide
  have hdescent : baseEnd_1174316 < baseStart_1174316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174339 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 6]
def baseStart_1174339 : Nat := 118140960795 + 1174339 * 2 ^ 59
def prefixEnd_1174339 : Nat := 4983230072969 + 3 ^ 40 * 1174339 * 2
def baseEnd_1174339 : Nat := 67000039813376236329091

theorem tailTrace_1174339 : CollatzResearch.WordTrace tailWord_1174339 prefixEnd_1174339 67000039813376236329091 := by
  unfold tailWord_1174339
  simp only [CollatzResearch.WordTrace]
  refine ⟨42831662092577838978822071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28554441395051892652548047 42831662092577838978822071)
  ·
    refine ⟨64247493138866758468233107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42831662092577838978822071 64247493138866758468233107)
    ·
      refine ⟨96371239708300137702349661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64247493138866758468233107 96371239708300137702349661)
      ·
        refine ⟨36139214890612551638381123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96371239708300137702349661 36139214890612551638381123)
        ·
          refine ⟨54208822335918827457571685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36139214890612551638381123 54208822335918827457571685)
          ·
            refine ⟨10164154187984780148294691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54208822335918827457571685 10164154187984780148294691)
            ·
              refine ⟨15246231281977170222442037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10164154187984780148294691 15246231281977170222442037)
              ·
                refine ⟨1429334182685359708353941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15246231281977170222442037 1429334182685359708353941)
                ·
                  refine ⟨67000039813376236329091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1429334182685359708353941 67000039813376236329091)
                  ·
                    rfl

theorem cell23_1174339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 6].length) (baseStart_1174339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174339 prefixEnd_1174339 := by exact prefixLift 1174339
  have htrace : WordTrace (prefixWord ++ tailWord_1174339) baseStart_1174339 baseEnd_1174339 := by
    simpa [prefixWord, tailWord_1174339, baseEnd_1174339] using wordTrace_append hprefix tailTrace_1174339
  have hstable : (prefixWord ++ tailWord_1174339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174339).length < 2 ^ (prefixWord ++ tailWord_1174339).sum := by decide
  have hdescent : baseEnd_1174339 < baseStart_1174339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174369 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1174369 : Nat := 118140960795 + 1174369 * 2 ^ 59
def prefixEnd_1174369 : Nat := 4983230072969 + 3 ^ 40 * 1174369 * 2
def baseEnd_1174369 : Nat := 201005254246673669862227

theorem tailTrace_1174369 : CollatzResearch.WordTrace tailWord_1174369 prefixEnd_1174369 201005254246673669862227 := by
  unfold tailWord_1174369
  simp only [CollatzResearch.WordTrace]
  refine ⟨42832756282469154102414161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28555170854979436068276107 42832756282469154102414161)
  ·
    refine ⟨32124567211851865576810621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42832756282469154102414161 32124567211851865576810621)
    ·
      refine ⟨12046712704444449591303983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32124567211851865576810621 12046712704444449591303983)
      ·
        refine ⟨18070069056666674386955975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12046712704444449591303983 18070069056666674386955975)
        ·
          refine ⟨27105103585000011580433963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18070069056666674386955975 27105103585000011580433963)
          ·
            refine ⟨40657655377500017370650945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27105103585000011580433963 40657655377500017370650945)
            ·
              refine ⟨30493241533125013027988209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40657655377500017370650945 30493241533125013027988209)
              ·
                refine ⟨22869931149843759770991157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30493241533125013027988209 22869931149843759770991157)
                ·
                  refine ⟨2144056045297852478530421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22869931149843759770991157 2144056045297852478530421)
                  ·
                    refine ⟨201005254246673669862227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2144056045297852478530421 201005254246673669862227)
                    ·
                      rfl

theorem cell23_1174369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1174369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174369 prefixEnd_1174369 := by exact prefixLift 1174369
  have htrace : WordTrace (prefixWord ++ tailWord_1174369) baseStart_1174369 baseEnd_1174369 := by
    simpa [prefixWord, tailWord_1174369, baseEnd_1174369] using wordTrace_append hprefix tailTrace_1174369
  have hstable : (prefixWord ++ tailWord_1174369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174369).length < 2 ^ (prefixWord ++ tailWord_1174369).sum := by decide
  have hdescent : baseEnd_1174369 < baseStart_1174369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174390 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1174390 : Nat := 118140960795 + 1174390 * 2 ^ 59
def prefixEnd_1174390 : Nat := 4983230072969 + 3 ^ 40 * 1174390 * 2
def baseEnd_1174390 : Nat := 67002949537085047491565

theorem tailTrace_1174390 : CollatzResearch.WordTrace tailWord_1174390 prefixEnd_1174390 67002949537085047491565 := by
  unfold tailWord_1174390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677095138462067168058039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28555681476928716459285749 2677095138462067168058039)
  ·
    refine ⟨4015642707693100752087059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677095138462067168058039 4015642707693100752087059)
    ·
      refine ⟨6023464061539651128130589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015642707693100752087059 6023464061539651128130589)
      ·
        refine ⟨2258799023077369173048971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6023464061539651128130589 2258799023077369173048971)
        ·
          refine ⟨3388198534616053759573457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258799023077369173048971 3388198534616053759573457)
          ·
            refine ⟨2541148900962040319680093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388198534616053759573457 2541148900962040319680093)
            ·
              refine ⟨952930837860765119880035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541148900962040319680093 952930837860765119880035)
              ·
                refine ⟨1429396256791147679820053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 952930837860765119880035 1429396256791147679820053)
                ·
                  refine ⟨67002949537085047491565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1429396256791147679820053 67002949537085047491565)
                  ·
                    rfl

theorem cell23_1174390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1174390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174390 prefixEnd_1174390 := by exact prefixLift 1174390
  have htrace : WordTrace (prefixWord ++ tailWord_1174390) baseStart_1174390 baseEnd_1174390 := by
    simpa [prefixWord, tailWord_1174390, baseEnd_1174390] using wordTrace_append hprefix tailTrace_1174390
  have hstable : (prefixWord ++ tailWord_1174390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174390).length < 2 ^ (prefixWord ++ tailWord_1174390).sum := by decide
  have hdescent : baseEnd_1174390 < baseStart_1174390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174433 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1174433 : Nat := 118140960795 + 1174433 * 2 ^ 59
def prefixEnd_1174433 : Nat := 4983230072969 + 3 ^ 40 * 1174433 * 2
def baseEnd_1174433 : Nat := 201016208500636253062129

theorem tailTrace_1174433 : CollatzResearch.WordTrace tailWord_1174433 prefixEnd_1174433 201016208500636253062129 := by
  unfold tailWord_1174433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42835090554237293032743953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28556727036158195355162635 42835090554237293032743953)
  ·
    refine ⟨32126317915677969774557965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42835090554237293032743953 32126317915677969774557965)
    ·
      refine ⟨12047369218379238665459237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32126317915677969774557965 12047369218379238665459237)
      ·
        refine ⟨2258881728446107249773607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12047369218379238665459237 2258881728446107249773607)
        ·
          refine ⟨3388322592669160874660411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258881728446107249773607 3388322592669160874660411)
          ·
            refine ⟨5082483889003741311990617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388322592669160874660411 5082483889003741311990617)
            ·
              refine ⟨3811862916752805983992963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5082483889003741311990617 3811862916752805983992963)
              ·
                refine ⟨5717794375129208975989445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811862916752805983992963 5717794375129208975989445)
                ·
                  refine ⟨1072086445336726682998021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5717794375129208975989445 1072086445336726682998021)
                  ·
                    refine ⟨201016208500636253062129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072086445336726682998021 201016208500636253062129)
                    ·
                      rfl

theorem cell23_1174433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1174433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174433 prefixEnd_1174433 := by exact prefixLift 1174433
  have htrace : WordTrace (prefixWord ++ tailWord_1174433) baseStart_1174433 baseEnd_1174433 := by
    simpa [prefixWord, tailWord_1174433, baseEnd_1174433] using wordTrace_append hprefix tailTrace_1174433
  have hstable : (prefixWord ++ tailWord_1174433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174433).length < 2 ^ (prefixWord ++ tailWord_1174433).sum := by decide
  have hdescent : baseEnd_1174433 < baseStart_1174433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174434 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_1174434 : Nat := 118140960795 + 1174434 * 2 ^ 59
def prefixEnd_1174434 : Nat := 4983230072969 + 3 ^ 40 * 1174434 * 2
def baseEnd_1174434 : Nat := 603049138982563255273883

theorem tailTrace_1174434 : CollatzResearch.WordTrace tailWord_1174434 prefixEnd_1174434 603049138982563255273883 := by
  unfold tailWord_1174434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708781756808417550882589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28556751351489113469020237 10708781756808417550882589)
  ·
    refine ⟨4015793158803156581580971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10708781756808417550882589 4015793158803156581580971)
    ·
      refine ⟨6023689738204734872371457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015793158803156581580971 6023689738204734872371457)
      ·
        refine ⟨4517767303653551154278593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023689738204734872371457 4517767303653551154278593)
        ·
          refine ⟨3388325477740163365708945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4517767303653551154278593 3388325477740163365708945)
          ·
            refine ⟨2541244108305122524281709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388325477740163365708945 2541244108305122524281709)
            ·
              refine ⟨952966540614420946605641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541244108305122524281709 952966540614420946605641)
              ·
                refine ⟨714724905460815709954231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 952966540614420946605641 714724905460815709954231)
                ·
                  refine ⟨1072087358191223564931347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714724905460815709954231 1072087358191223564931347)
                  ·
                    refine ⟨1608131037286835347397021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072087358191223564931347 1608131037286835347397021)
                    ·
                      refine ⟨603049138982563255273883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608131037286835347397021 603049138982563255273883)
                      ·
                        rfl

theorem cell23_1174434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_1174434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174434 prefixEnd_1174434 := by exact prefixLift 1174434
  have htrace : WordTrace (prefixWord ++ tailWord_1174434) baseStart_1174434 baseEnd_1174434 := by
    simpa [prefixWord, tailWord_1174434, baseEnd_1174434] using wordTrace_append hprefix tailTrace_1174434
  have hstable : (prefixWord ++ tailWord_1174434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174434).length < 2 ^ (prefixWord ++ tailWord_1174434).sum := by decide
  have hdescent : baseEnd_1174434 < baseStart_1174434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174469 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_1174469 : Nat := 118140960795 + 1174469 * 2 ^ 59
def prefixEnd_1174469 : Nat := 4983230072969 + 3 ^ 40 * 1174469 * 2
def baseEnd_1174469 : Nat := 603067110805470618336221

theorem tailTrace_1174469 : CollatzResearch.WordTrace tailWord_1174469 prefixEnd_1174469 603067110805470618336221 := by
  unfold tailWord_1174469
  simp only [CollatzResearch.WordTrace]
  refine ⟨42836403582106871181054461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28557602388071247454036307 42836403582106871181054461)
  ·
    refine ⟨16063651343290076692895423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42836403582106871181054461 16063651343290076692895423)
    ·
      refine ⟨24095477014935115039343135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063651343290076692895423 24095477014935115039343135)
      ·
        refine ⟨36143215522402672559014703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24095477014935115039343135 36143215522402672559014703)
        ·
          refine ⟨54214823283604008838522055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36143215522402672559014703 54214823283604008838522055)
          ·
            refine ⟨81322234925406013257783083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54214823283604008838522055 81322234925406013257783083)
            ·
              refine ⟨121983352388109019886674625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81322234925406013257783083 121983352388109019886674625)
              ·
                refine ⟨91487514291081764915005969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121983352388109019886674625 91487514291081764915005969)
                ·
                  refine ⟨68615635718311323686254477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91487514291081764915005969 68615635718311323686254477)
                  ·
                    refine ⟨25730863394366746382345429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68615635718311323686254477 25730863394366746382345429)
                    ·
                      refine ⟨603067110805470618336221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25730863394366746382345429 603067110805470618336221)
                      ·
                        rfl

theorem cell23_1174469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_1174469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174469 prefixEnd_1174469 := by exact prefixLift 1174469
  have htrace : WordTrace (prefixWord ++ tailWord_1174469) baseStart_1174469 baseEnd_1174469 := by
    simpa [prefixWord, tailWord_1174469, baseEnd_1174469] using wordTrace_append hprefix tailTrace_1174469
  have hstable : (prefixWord ++ tailWord_1174469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174469).length < 2 ^ (prefixWord ++ tailWord_1174469).sum := by decide
  have hdescent : baseEnd_1174469 < baseStart_1174469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174490 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1174490 : Nat := 118140960795 + 1174490 * 2 ^ 59
def prefixEnd_1174490 : Nat := 4983230072969 + 3 ^ 40 * 1174490 * 2
def baseEnd_1174490 : Nat := 603077893899215036173625

theorem tailTrace_1174490 : CollatzResearch.WordTrace tailWord_1174490 prefixEnd_1174490 603077893899215036173625 := by
  unfold tailWord_1174490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709292378757697941892231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28558113010020527845045949 10709292378757697941892231)
  ·
    refine ⟨16063938568136546912838347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709292378757697941892231 16063938568136546912838347)
    ·
      refine ⟨24095907852204820369257521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063938568136546912838347 24095907852204820369257521)
      ·
        refine ⟨18071930889153615276943141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24095907852204820369257521 18071930889153615276943141)
        ·
          refine ⟨3388487041716302864426839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18071930889153615276943141 3388487041716302864426839)
          ·
            refine ⟨5082730562574454296640259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388487041716302864426839 5082730562574454296640259)
            ·
              refine ⟨7624095843861681444960389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082730562574454296640259 7624095843861681444960389)
              ·
                refine ⟨1429517970724065270930073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7624095843861681444960389 1429517970724065270930073)
                ·
                  refine ⟨1072138478043048953197555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1429517970724065270930073 1072138478043048953197555)
                  ·
                    refine ⟨1608207717064573429796333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072138478043048953197555 1608207717064573429796333)
                    ·
                      refine ⟨603077893899215036173625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608207717064573429796333 603077893899215036173625)
                      ·
                        rfl

theorem cell23_1174490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1174490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174490 prefixEnd_1174490 := by exact prefixLift 1174490
  have htrace : WordTrace (prefixWord ++ tailWord_1174490) baseStart_1174490 baseEnd_1174490 := by
    simpa [prefixWord, tailWord_1174490, baseEnd_1174490] using wordTrace_append hprefix tailTrace_1174490
  have hstable : (prefixWord ++ tailWord_1174490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174490).length < 2 ^ (prefixWord ++ tailWord_1174490).sum := by decide
  have hdescent : baseEnd_1174490 < baseStart_1174490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174506 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1174506 : Nat := 118140960795 + 1174506 * 2 ^ 59
def prefixEnd_1174506 : Nat := 4983230072969 + 3 ^ 40 * 1174506 * 2
def baseEnd_1174506 : Nat := 201028703196562324524517

theorem tailTrace_1174506 : CollatzResearch.WordTrace tailWord_1174506 prefixEnd_1174506 201028703196562324524517 := by
  unfold tailWord_1174506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709438270743206625037843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28558502055315217666767581 10709438270743206625037843)
  ·
    refine ⟨16064157406114809937556765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709438270743206625037843 16064157406114809937556765)
    ·
      refine ⟨6024059027293053726583787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16064157406114809937556765 6024059027293053726583787)
      ·
        refine ⟨9036088540939580589875681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024059027293053726583787 9036088540939580589875681)
        ·
          refine ⟨6777066405704685442406761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9036088540939580589875681 6777066405704685442406761)
          ·
            refine ⟨5082799804278514081805071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6777066405704685442406761 5082799804278514081805071)
            ·
              refine ⟨7624199706417771122707607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082799804278514081805071 7624199706417771122707607)
              ·
                refine ⟨11436299559626656684061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624199706417771122707607 11436299559626656684061411)
                ·
                  refine ⟨17154449339439985026092117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11436299559626656684061411 17154449339439985026092117)
                  ·
                    refine ⟨201028703196562324524517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17154449339439985026092117 201028703196562324524517)
                    ·
                      rfl

theorem cell23_1174506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1174506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174506 prefixEnd_1174506 := by exact prefixLift 1174506
  have htrace : WordTrace (prefixWord ++ tailWord_1174506) baseStart_1174506 baseEnd_1174506 := by
    simpa [prefixWord, tailWord_1174506, baseEnd_1174506] using wordTrace_append hprefix tailTrace_1174506
  have hstable : (prefixWord ++ tailWord_1174506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174506).length < 2 ^ (prefixWord ++ tailWord_1174506).sum := by decide
  have hdescent : baseEnd_1174506 < baseStart_1174506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174553 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 5]
def baseStart_1174553 : Nat := 118140960795 + 1174553 * 2 ^ 59
def prefixEnd_1174553 : Nat := 4983230072969 + 3 ^ 40 * 1174553 * 2
def baseEnd_1174553 : Nat := 67012249242272032187315

theorem tailTrace_1174553 : CollatzResearch.WordTrace tailWord_1174553 prefixEnd_1174553 67012249242272032187315 := by
  unfold tailWord_1174553
  simp only [CollatzResearch.WordTrace]
  refine ⟨42839467313802553527112313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28559644875868369018074875 42839467313802553527112313)
  ·
    refine ⟨32129600485351915145334235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42839467313802553527112313 32129600485351915145334235)
    ·
      refine ⟨48194400728027872718001353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32129600485351915145334235 48194400728027872718001353)
      ·
        refine ⟨36145800546020904538501015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48194400728027872718001353 36145800546020904538501015)
        ·
          refine ⟨54218700819031356807751523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36145800546020904538501015 54218700819031356807751523)
          ·
            refine ⟨81328051228547035211627285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54218700819031356807751523 81328051228547035211627285)
            ·
              refine ⟨3812252401338142275545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81328051228547035211627285 3812252401338142275545029)
              ·
                refine ⟨714797325250901676664693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3812252401338142275545029 714797325250901676664693)
                ·
                  refine ⟨67012249242272032187315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 714797325250901676664693 67012249242272032187315)
                  ·
                    rfl

theorem cell23_1174553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 5].length) (baseStart_1174553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174553 prefixEnd_1174553 := by exact prefixLift 1174553
  have htrace : WordTrace (prefixWord ++ tailWord_1174553) baseStart_1174553 baseEnd_1174553 := by
    simpa [prefixWord, tailWord_1174553, baseEnd_1174553] using wordTrace_append hprefix tailTrace_1174553
  have hstable : (prefixWord ++ tailWord_1174553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174553).length < 2 ^ (prefixWord ++ tailWord_1174553).sum := by decide
  have hdescent : baseEnd_1174553 < baseStart_1174553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174563 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1174563 : Nat := 118140960795 + 1174563 * 2 ^ 59
def prefixEnd_1174563 : Nat := 4983230072969 + 3 ^ 40 * 1174563 * 2
def baseEnd_1174563 : Nat := 603115377986993250560789

theorem tailTrace_1174563 : CollatzResearch.WordTrace tailWord_1174563 prefixEnd_1174563 603115377986993250560789 := by
  unfold tailWord_1174563
  simp only [CollatzResearch.WordTrace]
  refine ⟨42839832043766325234976343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28559888029177550156650895 42839832043766325234976343)
  ·
    refine ⟨64259748065649487852464515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42839832043766325234976343 64259748065649487852464515)
    ·
      refine ⟨96389622098474231778696773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64259748065649487852464515 96389622098474231778696773)
      ·
        refine ⟨18073054143463918458505645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96389622098474231778696773 18073054143463918458505645)
        ·
          refine ⟨6777395303798969421939617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18073054143463918458505645 6777395303798969421939617)
          ·
            refine ⟨5083046477849227066454713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6777395303798969421939617 5083046477849227066454713)
            ·
              refine ⟨3812284858386920299841035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5083046477849227066454713 3812284858386920299841035)
              ·
                refine ⟨5718427287580380449761553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812284858386920299841035 5718427287580380449761553)
                ·
                  refine ⟨4288820465685285337321165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718427287580380449761553 4288820465685285337321165)
                  ·
                    refine ⟨1608307674631982001495437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4288820465685285337321165 1608307674631982001495437)
                    ·
                      refine ⟨603115377986993250560789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608307674631982001495437 603115377986993250560789)
                      ·
                        rfl

theorem cell23_1174563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1174563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174563 prefixEnd_1174563 := by exact prefixLift 1174563
  have htrace : WordTrace (prefixWord ++ tailWord_1174563) baseStart_1174563 baseEnd_1174563 := by
    simpa [prefixWord, tailWord_1174563, baseEnd_1174563] using wordTrace_append hprefix tailTrace_1174563
  have hstable : (prefixWord ++ tailWord_1174563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174563).length < 2 ^ (prefixWord ++ tailWord_1174563).sum := by decide
  have hdescent : baseEnd_1174563 < baseStart_1174563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174620 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1174620 : Nat := 118140960795 + 1174620 * 2 ^ 59
def prefixEnd_1174620 : Nat := 4983230072969 + 3 ^ 40 * 1174620 * 2
def baseEnd_1174620 : Nat := 603144646384299527548027

theorem tailTrace_1174620 : CollatzResearch.WordTrace tailWord_1174620 prefixEnd_1174620 603144646384299527548027 := by
  unfold tailWord_1174620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21420955502279911984900657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28561274003039882646534209 21420955502279911984900657)
  ·
    refine ⟨16065716626709933988675493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21420955502279911984900657 16065716626709933988675493)
    ·
      refine ⟨3012321867508112622876655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16065716626709933988675493 3012321867508112622876655)
      ·
        refine ⟨4518482801262168934314983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012321867508112622876655 4518482801262168934314983)
        ·
          refine ⟨6777724201893253401472475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518482801262168934314983 6777724201893253401472475)
          ·
            refine ⟨10166586302839880102208713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777724201893253401472475 10166586302839880102208713)
            ·
              refine ⟨7624939727129910076656535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10166586302839880102208713 7624939727129910076656535)
              ·
                refine ⟨11437409590694865114984803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7624939727129910076656535 11437409590694865114984803)
                ·
                  refine ⟨17156114386042297672477205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437409590694865114984803 17156114386042297672477205)
                  ·
                    refine ⟨804192861845732703397369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17156114386042297672477205 804192861845732703397369)
                    ·
                      refine ⟨603144646384299527548027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804192861845732703397369 603144646384299527548027)
                      ·
                        rfl

theorem cell23_1174620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1174620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174620 prefixEnd_1174620 := by exact prefixLift 1174620
  have htrace : WordTrace (prefixWord ++ tailWord_1174620) baseStart_1174620 baseEnd_1174620 := by
    simpa [prefixWord, tailWord_1174620, baseEnd_1174620] using wordTrace_append hprefix tailTrace_1174620
  have hstable : (prefixWord ++ tailWord_1174620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174620).length < 2 ^ (prefixWord ++ tailWord_1174620).sum := by decide
  have hdescent : baseEnd_1174620 < baseStart_1174620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174623 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1174623 : Nat := 118140960795 + 1174623 * 2 ^ 59
def prefixEnd_1174623 : Nat := 4983230072969 + 3 ^ 40 * 1174623 * 2
def baseEnd_1174623 : Nat := 603146186826263015810513

theorem tailTrace_1174623 : CollatzResearch.WordTrace tailWord_1174623 prefixEnd_1174623 603146186826263015810513 := by
  unfold tailWord_1174623
  simp only [CollatzResearch.WordTrace]
  refine ⟨42842020423548955482160523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28561346949032636988107015 42842020423548955482160523)
  ·
    refine ⟨64263030635323433223240785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42842020423548955482160523 64263030635323433223240785)
    ·
      refine ⟨48197272976492574917430589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64263030635323433223240785 48197272976492574917430589)
      ·
        refine ⟨18073977366184715594036471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48197272976492574917430589 18073977366184715594036471)
        ·
          refine ⟨27110966049277073391054707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18073977366184715594036471 27110966049277073391054707)
          ·
            refine ⟨40666449073915610086582061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27110966049277073391054707 40666449073915610086582061)
            ·
              refine ⟨15249918402718353782468273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40666449073915610086582061 15249918402718353782468273)
              ·
                refine ⟨11437438802038765336851205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15249918402718353782468273 11437438802038765336851205)
                ·
                  refine ⟨2144519775382268500659601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11437438802038765336851205 2144519775382268500659601)
                  ·
                    refine ⟨1608389831536701375494701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144519775382268500659601 1608389831536701375494701)
                    ·
                      refine ⟨603146186826263015810513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608389831536701375494701 603146186826263015810513)
                      ·
                        rfl

theorem cell23_1174623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1174623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174623 prefixEnd_1174623 := by exact prefixLift 1174623
  have htrace : WordTrace (prefixWord ++ tailWord_1174623) baseStart_1174623 baseEnd_1174623 := by
    simpa [prefixWord, tailWord_1174623, baseEnd_1174623] using wordTrace_append hprefix tailTrace_1174623
  have hstable : (prefixWord ++ tailWord_1174623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174623).length < 2 ^ (prefixWord ++ tailWord_1174623).sum := by decide
  have hdescent : baseEnd_1174623 < baseStart_1174623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174640 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_1174640 : Nat := 118140960795 + 1174640 * 2 ^ 59
def prefixEnd_1174640 : Nat := 4983230072969 + 3 ^ 40 * 1174640 * 2
def baseEnd_1174640 : Nat := 603154915997389449297935

theorem tailTrace_1174640 : CollatzResearch.WordTrace tailWord_1174640 prefixEnd_1174640 603154915997389449297935 := by
  unfold tailWord_1174640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421320232243683692764687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28561760309658244923686249 21421320232243683692764687)
  ·
    refine ⟨32131980348365525539147031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21421320232243683692764687 32131980348365525539147031)
    ·
      refine ⟨48197970522548288308720547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32131980348365525539147031 48197970522548288308720547)
      ·
        refine ⟨72296955783822432463080821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48197970522548288308720547 72296955783822432463080821)
        ·
          refine ⟨6777839604733353043413827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72296955783822432463080821 6777839604733353043413827)
          ·
            refine ⟨10166759407100029565120741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777839604733353043413827 10166759407100029565120741)
            ·
              refine ⟨1906267388831255543460139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10166759407100029565120741 1906267388831255543460139)
              ·
                refine ⟨2859401083246883315190209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906267388831255543460139 2859401083246883315190209)
                ·
                  refine ⟨2144550812435162486392657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2859401083246883315190209 2144550812435162486392657)
                  ·
                    refine ⟨1608413109326371864794493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2144550812435162486392657 1608413109326371864794493)
                    ·
                      refine ⟨603154915997389449297935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608413109326371864794493 603154915997389449297935)
                      ·
                        rfl

theorem cell23_1174640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_1174640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174640 prefixEnd_1174640 := by exact prefixLift 1174640
  have htrace : WordTrace (prefixWord ++ tailWord_1174640) baseStart_1174640 baseEnd_1174640 := by
    simpa [prefixWord, tailWord_1174640, baseEnd_1174640] using wordTrace_append hprefix tailTrace_1174640
  have hstable : (prefixWord ++ tailWord_1174640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174640).length < 2 ^ (prefixWord ++ tailWord_1174640).sum := by decide
  have hdescent : baseEnd_1174640 < baseStart_1174640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174660 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1174660 : Nat := 118140960795 + 1174660 * 2 ^ 59
def prefixEnd_1174660 : Nat := 4983230072969 + 3 ^ 40 * 1174660 * 2
def baseEnd_1174660 : Nat := 67018353956719930116427

theorem tailTrace_1174660 : CollatzResearch.WordTrace tailWord_1174660 prefixEnd_1174660 67018353956719930116427 := by
  unfold tailWord_1174660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421684962207455400628717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28562246616276607200838289 21421684962207455400628717)
  ·
    refine ⟨8033131860827795775235769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21421684962207455400628717 8033131860827795775235769)
    ·
      refine ⟨6024848895620846831426827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8033131860827795775235769 6024848895620846831426827)
      ·
        refine ⟨9037273343431270247140241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024848895620846831426827 9037273343431270247140241)
        ·
          refine ⟨6777955007573452685355181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9037273343431270247140241 6777955007573452685355181)
          ·
            refine ⟨2541733127840044757008193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6777955007573452685355181 2541733127840044757008193)
            ·
              refine ⟨1906299845880033567756145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2541733127840044757008193 1906299845880033567756145)
              ·
                refine ⟨1429724884410025175817109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906299845880033567756145 1429724884410025175817109)
                ·
                  refine ⟨67018353956719930116427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1429724884410025175817109 67018353956719930116427)
                  ·
                    rfl

theorem cell23_1174660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1174660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174660 prefixEnd_1174660 := by exact prefixLift 1174660
  have htrace : WordTrace (prefixWord ++ tailWord_1174660) baseStart_1174660 baseEnd_1174660 := by
    simpa [prefixWord, tailWord_1174660, baseEnd_1174660] using wordTrace_append hprefix tailTrace_1174660
  have hstable : (prefixWord ++ tailWord_1174660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174660).length < 2 ^ (prefixWord ++ tailWord_1174660).sum := by decide
  have hdescent : baseEnd_1174660 < baseStart_1174660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174664 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1174664 : Nat := 118140960795 + 1174664 * 2 ^ 59
def prefixEnd_1174664 : Nat := 4983230072969 + 3 ^ 40 * 1174664 * 2
def baseEnd_1174664 : Nat := 201055746511032451799275

theorem tailTrace_1174664 : CollatzResearch.WordTrace tailWord_1174664 prefixEnd_1174664 201055746511032451799275 := by
  unfold tailWord_1174664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421757908200209742201523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28562343877600279656268697 21421757908200209742201523)
  ·
    refine ⟨32132636862300314613302285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21421757908200209742201523 32132636862300314613302285)
    ·
      refine ⟨12049738823362617979988357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32132636862300314613302285 12049738823362617979988357)
      ·
        refine ⟨2259326029380490871247817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12049738823362617979988357 2259326029380490871247817)
        ·
          refine ⟨1694494522035368153435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2259326029380490871247817 1694494522035368153435863)
          ·
            refine ⟨2541741783053052230153795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694494522035368153435863 2541741783053052230153795)
            ·
              refine ⟨3812612674579578345230693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541741783053052230153795 3812612674579578345230693)
              ·
                refine ⟨714864876483670939730755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3812612674579578345230693 714864876483670939730755)
                ·
                  refine ⟨1072297314725506409596133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714864876483670939730755 1072297314725506409596133)
                  ·
                    refine ⟨201055746511032451799275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072297314725506409596133 201055746511032451799275)
                    ·
                      rfl

theorem cell23_1174664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1174664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174664 prefixEnd_1174664 := by exact prefixLift 1174664
  have htrace : WordTrace (prefixWord ++ tailWord_1174664) baseStart_1174664 baseEnd_1174664 := by
    simpa [prefixWord, tailWord_1174664, baseEnd_1174664] using wordTrace_append hprefix tailTrace_1174664
  have hstable : (prefixWord ++ tailWord_1174664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174664).length < 2 ^ (prefixWord ++ tailWord_1174664).sum := by decide
  have hdescent : baseEnd_1174664 < baseStart_1174664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174703 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 6]
def baseStart_1174703 : Nat := 118140960795 + 1174703 * 2 ^ 59
def prefixEnd_1174703 : Nat := 4983230072969 + 3 ^ 40 * 1174703 * 2
def baseEnd_1174703 : Nat := 201062421759540900936715

theorem tailTrace_1174703 : CollatzResearch.WordTrace tailWord_1174703 prefixEnd_1174703 201062421759540900936715 := by
  unfold tailWord_1174703
  simp only [CollatzResearch.WordTrace]
  refine ⟨42844938263259129145072763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28563292175506086096715175 42844938263259129145072763)
  ·
    refine ⟨64267407394888693717609145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42844938263259129145072763 64267407394888693717609145)
    ·
      refine ⟨48200555546166520288206859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64267407394888693717609145 48200555546166520288206859)
      ·
        refine ⟨72300833319249780432310289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48200555546166520288206859 72300833319249780432310289)
        ·
          refine ⟨54225624989437335324232717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72300833319249780432310289 54225624989437335324232717)
          ·
            refine ⟨20334609371039000746587269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54225624989437335324232717 20334609371039000746587269)
            ·
              refine ⟨3812739257069812639985113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20334609371039000746587269 3812739257069812639985113)
              ·
                refine ⟨2859554442802359479988835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812739257069812639985113 2859554442802359479988835)
                ·
                  refine ⟨4289331664203539219983253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859554442802359479988835 4289331664203539219983253)
                  ·
                    refine ⟨201062421759540900936715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4289331664203539219983253 201062421759540900936715)
                    ·
                      rfl

theorem cell23_1174703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_1174703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174703 prefixEnd_1174703 := by exact prefixLift 1174703
  have htrace : WordTrace (prefixWord ++ tailWord_1174703) baseStart_1174703 baseEnd_1174703 := by
    simpa [prefixWord, tailWord_1174703, baseEnd_1174703] using wordTrace_append hprefix tailTrace_1174703
  have hstable : (prefixWord ++ tailWord_1174703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174703).length < 2 ^ (prefixWord ++ tailWord_1174703).sum := by decide
  have hdescent : baseEnd_1174703 < baseStart_1174703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174721 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1174721 : Nat := 118140960795 + 1174721 * 2 ^ 59
def prefixEnd_1174721 : Nat := 4983230072969 + 3 ^ 40 * 1174721 * 2
def baseEnd_1174721 : Nat := 603196507930403632385063

theorem tailTrace_1174721 : CollatzResearch.WordTrace tailWord_1174721 prefixEnd_1174721 603196507930403632385063 := by
  unfold tailWord_1174721
  simp only [CollatzResearch.WordTrace]
  refine ⟨42845594777193918219228017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28563729851462612146152011 42845594777193918219228017)
  ·
    refine ⟨32134196082895438664421013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42845594777193918219228017 32134196082895438664421013)
    ·
      refine ⟨1506290441385723687394735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32134196082895438664421013 1506290441385723687394735)
      ·
        refine ⟨2259435662078585531092103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506290441385723687394735 2259435662078585531092103)
        ·
          refine ⟨3389153493117878296638155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259435662078585531092103 3389153493117878296638155)
          ·
            refine ⟨5083730239676817444957233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389153493117878296638155 5083730239676817444957233)
            ·
              refine ⟨3812797679757613083717925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5083730239676817444957233 3812797679757613083717925)
              ·
                refine ⟨714899564954552453197111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3812797679757613083717925 714899564954552453197111)
                ·
                  refine ⟨1072349347431828679795667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714899564954552453197111 1072349347431828679795667)
                  ·
                    refine ⟨1608524021147743019693501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072349347431828679795667 1608524021147743019693501)
                    ·
                      refine ⟨603196507930403632385063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608524021147743019693501 603196507930403632385063)
                      ·
                        rfl

theorem cell23_1174721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1174721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174721 prefixEnd_1174721 := by exact prefixLift 1174721
  have htrace : WordTrace (prefixWord ++ tailWord_1174721) baseStart_1174721 baseEnd_1174721 := by
    simpa [prefixWord, tailWord_1174721, baseEnd_1174721] using wordTrace_append hprefix tailTrace_1174721
  have hstable : (prefixWord ++ tailWord_1174721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174721).length < 2 ^ (prefixWord ++ tailWord_1174721).sum := by decide
  have hdescent : baseEnd_1174721 < baseStart_1174721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174730 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1174730 : Nat := 118140960795 + 1174730 * 2 ^ 59
def prefixEnd_1174730 : Nat := 4983230072969 + 3 ^ 40 * 1174730 * 2
def baseEnd_1174730 : Nat := 603201129256294097172521

theorem tailTrace_1174730 : CollatzResearch.WordTrace tailWord_1174730 prefixEnd_1174730 603201129256294097172521 := by
  unfold tailWord_1174730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10711480758540328189076411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28563948689440875170870429 10711480758540328189076411)
  ·
    refine ⟨16067221137810492283614617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10711480758540328189076411 16067221137810492283614617)
    ·
      refine ⟨12050415853357869212710963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16067221137810492283614617 12050415853357869212710963)
      ·
        refine ⟨18075623780036803819066445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12050415853357869212710963 18075623780036803819066445)
        ·
          refine ⟨6778358917513801432149917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18075623780036803819066445 6778358917513801432149917)
          ·
            refine ⟨2541884594067675537056219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6778358917513801432149917 2541884594067675537056219)
            ·
              refine ⟨3812826891101513305584329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541884594067675537056219 3812826891101513305584329)
              ·
                refine ⟨2859620168326134979188247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812826891101513305584329 2859620168326134979188247)
                ·
                  refine ⟨4289430252489202468782371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859620168326134979188247 4289430252489202468782371)
                  ·
                    refine ⟨6434145378733803703173557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289430252489202468782371 6434145378733803703173557)
                    ·
                      refine ⟨603201129256294097172521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6434145378733803703173557 603201129256294097172521)
                      ·
                        rfl

theorem cell23_1174730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1174730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174730 prefixEnd_1174730 := by exact prefixLift 1174730
  have htrace : WordTrace (prefixWord ++ tailWord_1174730) baseStart_1174730 baseEnd_1174730 := by
    simpa [prefixWord, tailWord_1174730, baseEnd_1174730] using wordTrace_append hprefix tailTrace_1174730
  have hstable : (prefixWord ++ tailWord_1174730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174730).length < 2 ^ (prefixWord ++ tailWord_1174730).sum := by decide
  have hdescent : baseEnd_1174730 < baseStart_1174730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174760 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1174760 : Nat := 118140960795 + 1174760 * 2 ^ 59
def prefixEnd_1174760 : Nat := 4983230072969 + 3 ^ 40 * 1174760 * 2
def baseEnd_1174760 : Nat := 603216533675928979797383

theorem tailTrace_1174760 : CollatzResearch.WordTrace tailWord_1174760 prefixEnd_1174760 603216533675928979797383 := by
  unfold tailWord_1174760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423508612026313939948867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28564678149368418586598489 21423508612026313939948867)
  ·
    refine ⟨32135262918039470909923301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21423508612026313939948867 32135262918039470909923301)
    ·
      refine ⟨6025361797132400795610619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32135262918039470909923301 6025361797132400795610619)
      ·
        refine ⟨9038042695698601193415929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025361797132400795610619 9038042695698601193415929)
        ·
          refine ⟨6778532021773950895061947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9038042695698601193415929 6778532021773950895061947)
          ·
            refine ⟨10167798032660926342592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778532021773950895061947 10167798032660926342592921)
            ·
              refine ⟨7625848524495694756944691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167798032660926342592921 7625848524495694756944691)
              ·
                refine ⟨11438772786743542135417037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7625848524495694756944691 11438772786743542135417037)
                ·
                  refine ⟨4289539795028828300781389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11438772786743542135417037 4289539795028828300781389)
                  ·
                    refine ⟨1608577423135810612793021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4289539795028828300781389 1608577423135810612793021)
                    ·
                      refine ⟨603216533675928979797383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608577423135810612793021 603216533675928979797383)
                      ·
                        rfl

theorem cell23_1174760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1174760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174760 prefixEnd_1174760 := by exact prefixLift 1174760
  have htrace : WordTrace (prefixWord ++ tailWord_1174760) baseStart_1174760 baseEnd_1174760 := by
    simpa [prefixWord, tailWord_1174760, baseEnd_1174760] using wordTrace_append hprefix tailTrace_1174760
  have hstable : (prefixWord ++ tailWord_1174760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174760).length < 2 ^ (prefixWord ++ tailWord_1174760).sum := by decide
  have hdescent : baseEnd_1174760 < baseStart_1174760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174772 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1174772 : Nat := 118140960795 + 1174772 * 2 ^ 59
def prefixEnd_1174772 : Nat := 4983230072969 + 3 ^ 40 * 1174772 * 2
def baseEnd_1174772 : Nat := 603222695443782932847329

theorem tailTrace_1174772 : CollatzResearch.WordTrace tailWord_1174772 prefixEnd_1174772 603222695443782932847329 := by
  unfold tailWord_1174772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423727450004576964667285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28564969933339435952889713 21423727450004576964667285)
  ·
    refine ⟨1004237224218964545218779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21423727450004576964667285 1004237224218964545218779)
    ·
      refine ⟨1506355836328446817828169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004237224218964545218779 1506355836328446817828169)
      ·
        refine ⟨1129766877246335113371127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506355836328446817828169 1129766877246335113371127)
        ·
          refine ⟨1694650315869502670056691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129766877246335113371127 1694650315869502670056691)
          ·
            refine ⟨2541975473804254005085037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694650315869502670056691 2541975473804254005085037)
            ·
              refine ⟨953240802676595251906889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541975473804254005085037 953240802676595251906889)
              ·
                refine ⟨714930602007446438930167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953240802676595251906889 714930602007446438930167)
                ·
                  refine ⟨1072395903011169658395251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714930602007446438930167 1072395903011169658395251)
                  ·
                    refine ⟨1608593854516754487592877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072395903011169658395251 1608593854516754487592877)
                    ·
                      refine ⟨603222695443782932847329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608593854516754487592877 603222695443782932847329)
                      ·
                        rfl

theorem cell23_1174772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1174772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174772 prefixEnd_1174772 := by exact prefixLift 1174772
  have htrace : WordTrace (prefixWord ++ tailWord_1174772) baseStart_1174772 baseEnd_1174772 := by
    simpa [prefixWord, tailWord_1174772, baseEnd_1174772] using wordTrace_append hprefix tailTrace_1174772
  have hstable : (prefixWord ++ tailWord_1174772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174772).length < 2 ^ (prefixWord ++ tailWord_1174772).sum := by decide
  have hdescent : baseEnd_1174772 < baseStart_1174772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174777 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 3]
def baseStart_1174777 : Nat := 118140960795 + 1174777 * 2 ^ 59
def prefixEnd_1174777 : Nat := 4983230072969 + 3 ^ 40 * 1174777 * 2
def baseEnd_1174777 : Nat := 603225262847055413284805

theorem tailTrace_1174777 : CollatzResearch.WordTrace tailWord_1174777 prefixEnd_1174777 603225262847055413284805 := by
  unfold tailWord_1174777
  simp only [CollatzResearch.WordTrace]
  refine ⟨42847637264991039783266585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28565091509994026522177723 42847637264991039783266585)
  ·
    refine ⟨32135727948743279837449939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42847637264991039783266585 32135727948743279837449939)
    ·
      refine ⟨48203591923114919756174909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32135727948743279837449939 48203591923114919756174909)
      ·
        refine ⟨18076346971168094908565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48203591923114919756174909 18076346971168094908565591)
        ·
          refine ⟨27114520456752142362848387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18076346971168094908565591 27114520456752142362848387)
          ·
            refine ⟨40671780685128213544272581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27114520456752142362848387 40671780685128213544272581)
            ·
              refine ⟨7625958878461540039551109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40671780685128213544272581 7625958878461540039551109)
              ·
                refine ⟨1429867289711538757415833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7625958878461540039551109 1429867289711538757415833)
                ·
                  refine ⟨1072400467283654068061875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1429867289711538757415833 1072400467283654068061875)
                  ·
                    refine ⟨1608600700925481102092813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072400467283654068061875 1608600700925481102092813)
                    ·
                      refine ⟨603225262847055413284805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608600700925481102092813 603225262847055413284805)
                      ·
                        rfl

theorem cell23_1174777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_1174777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174777 prefixEnd_1174777 := by exact prefixLift 1174777
  have htrace : WordTrace (prefixWord ++ tailWord_1174777) baseStart_1174777 baseEnd_1174777 := by
    simpa [prefixWord, tailWord_1174777, baseEnd_1174777] using wordTrace_append hprefix tailTrace_1174777
  have hstable : (prefixWord ++ tailWord_1174777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174777).length < 2 ^ (prefixWord ++ tailWord_1174777).sum := by decide
  have hdescent : baseEnd_1174777 < baseStart_1174777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174793 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_1174793 : Nat := 118140960795 + 1174793 * 2 ^ 59
def prefixEnd_1174793 : Nat := 4983230072969 + 3 ^ 40 * 1174793 * 2
def baseEnd_1174793 : Nat := 201077826179175783561577

theorem tailTrace_1174793 : CollatzResearch.WordTrace tailWord_1174793 prefixEnd_1174793 201077826179175783561577 := by
  unfold tailWord_1174793
  simp only [CollatzResearch.WordTrace]
  refine ⟨42848220832933074515849033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28565480555288716343899355 42848220832933074515849033)
  ·
    refine ⟨32136165624699805886886775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42848220832933074515849033 32136165624699805886886775)
    ·
      refine ⟨48204248437049708830330163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32136165624699805886886775 48204248437049708830330163)
      ·
        refine ⟨72306372655574563245495245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48204248437049708830330163 72306372655574563245495245)
        ·
          refine ⟨27114889745840461217060717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72306372655574563245495245 27114889745840461217060717)
          ·
            refine ⟨10168083654690172956397769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27114889745840461217060717 10168083654690172956397769)
            ·
              refine ⟨7626062741017629717298327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10168083654690172956397769 7626062741017629717298327)
              ·
                refine ⟨11439094111526444575947491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626062741017629717298327 11439094111526444575947491)
                ·
                  refine ⟨17158641167289666863921237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11439094111526444575947491 17158641167289666863921237)
                  ·
                    refine ⟨201077826179175783561577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17158641167289666863921237 201077826179175783561577)
                    ·
                      rfl

theorem cell23_1174793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_1174793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174793 prefixEnd_1174793 := by exact prefixLift 1174793
  have htrace : WordTrace (prefixWord ++ tailWord_1174793) baseStart_1174793 baseEnd_1174793 := by
    simpa [prefixWord, tailWord_1174793, baseEnd_1174793] using wordTrace_append hprefix tailTrace_1174793
  have hstable : (prefixWord ++ tailWord_1174793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174793).length < 2 ^ (prefixWord ++ tailWord_1174793).sum := by decide
  have hdescent : baseEnd_1174793 < baseStart_1174793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174820 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1174820 : Nat := 118140960795 + 1174820 * 2 ^ 59
def prefixEnd_1174820 : Nat := 4983230072969 + 3 ^ 40 * 1174820 * 2
def baseEnd_1174820 : Nat := 603247342515198745047107

theorem tailTrace_1174820 : CollatzResearch.WordTrace tailWord_1174820 prefixEnd_1174820 603247342515198745047107 := by
  unfold tailWord_1174820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21424602801917629063540957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28566137069223505418054609 21424602801917629063540957)
  ·
    refine ⟨8034226050719110898827859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21424602801917629063540957 8034226050719110898827859)
    ·
      refine ⟨12051339076078666348241789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034226050719110898827859 12051339076078666348241789)
      ·
        refine ⟨4519252153529499880590671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12051339076078666348241789 4519252153529499880590671)
        ·
          refine ⟨6778878230294249820886007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519252153529499880590671 6778878230294249820886007)
          ·
            refine ⟨10168317345441374731329011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778878230294249820886007 10168317345441374731329011)
            ·
              refine ⟨15252476018162062096993517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10168317345441374731329011 15252476018162062096993517)
              ·
                refine ⟨5719678506810773286372569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15252476018162062096993517 5719678506810773286372569)
                ·
                  refine ⟨4289758880108079964779427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5719678506810773286372569 4289758880108079964779427)
                  ·
                    refine ⟨6434638320162119947169141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4289758880108079964779427 6434638320162119947169141)
                    ·
                      refine ⟨603247342515198745047107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6434638320162119947169141 603247342515198745047107)
                      ·
                        rfl

theorem cell23_1174820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1174820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174820 prefixEnd_1174820 := by exact prefixLift 1174820
  have htrace : WordTrace (prefixWord ++ tailWord_1174820) baseStart_1174820 baseEnd_1174820 := by
    simpa [prefixWord, tailWord_1174820, baseEnd_1174820] using wordTrace_append hprefix tailTrace_1174820
  have hstable : (prefixWord ++ tailWord_1174820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174820).length < 2 ^ (prefixWord ++ tailWord_1174820).sum := by decide
  have hdescent : baseEnd_1174820 < baseStart_1174820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174821 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_1174821 : Nat := 118140960795 + 1174821 * 2 ^ 59
def prefixEnd_1174821 : Nat := 4983230072969 + 3 ^ 40 * 1174821 * 2
def baseEnd_1174821 : Nat := 603247855995853241134603

theorem tailTrace_1174821 : CollatzResearch.WordTrace tailWord_1174821 prefixEnd_1174821 603247855995853241134603 := by
  unfold tailWord_1174821
  simp only [CollatzResearch.WordTrace]
  refine ⟨42849242076831635297868317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28566161384554423531912211 42849242076831635297868317)
  ·
    refine ⟨16068465778811863236700619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42849242076831635297868317 16068465778811863236700619)
    ·
      refine ⟨24102698668217794855050929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16068465778811863236700619 24102698668217794855050929)
      ·
        refine ⟨18077024001163346141288197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24102698668217794855050929 18077024001163346141288197)
        ·
          refine ⟨3389442000218127401491537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18077024001163346141288197 3389442000218127401491537)
          ·
            refine ⟨2542081500163595551118653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389442000218127401491537 2542081500163595551118653)
            ·
              refine ⟨953280562561348331669495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2542081500163595551118653 953280562561348331669495)
              ·
                refine ⟨1429920843842022497504243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953280562561348331669495 1429920843842022497504243)
                ·
                  refine ⟨2144881265763033746256365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429920843842022497504243 2144881265763033746256365)
                  ·
                    refine ⟨804330474661137654846137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144881265763033746256365 804330474661137654846137)
                    ·
                      refine ⟨603247855995853241134603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804330474661137654846137 603247855995853241134603)
                      ·
                        rfl

theorem cell23_1174821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_1174821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174821 prefixEnd_1174821 := by exact prefixLift 1174821
  have htrace : WordTrace (prefixWord ++ tailWord_1174821) baseStart_1174821 baseEnd_1174821 := by
    simpa [prefixWord, tailWord_1174821, baseEnd_1174821] using wordTrace_append hprefix tailTrace_1174821
  have hstable : (prefixWord ++ tailWord_1174821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174821).length < 2 ^ (prefixWord ++ tailWord_1174821).sum := by decide
  have hdescent : baseEnd_1174821 < baseStart_1174821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174907 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 2, 4, 2]
def baseStart_1174907 : Nat := 118140960795 + 1174907 * 2 ^ 59
def prefixEnd_1174907 : Nat := 4983230072969 + 3 ^ 40 * 1174907 * 2
def baseEnd_1174907 : Nat := 603292015332139904659207

theorem tailTrace_1174907 : CollatzResearch.WordTrace tailWord_1174907 prefixEnd_1174907 603292015332139904659207 := by
  unfold tailWord_1174907
  simp only [CollatzResearch.WordTrace]
  refine ⟨42852378754520071985498975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28568252503013381323665983 42852378754520071985498975)
  ·
    refine ⟨64278568131780107978248463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42852378754520071985498975 64278568131780107978248463)
    ·
      refine ⟨96417852197670161967372695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64278568131780107978248463 96417852197670161967372695)
      ·
        refine ⟨144626778296505242951059043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96417852197670161967372695 144626778296505242951059043)
        ·
          refine ⟨216940167444757864426588565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144626778296505242951059043 216940167444757864426588565)
          ·
            refine ⟨10169070348973024894996339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 216940167444757864426588565 10169070348973024894996339)
            ·
              refine ⟨15253605523459537342494509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10169070348973024894996339 15253605523459537342494509)
              ·
                refine ⟨5720102071297326503435441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15253605523459537342494509 5720102071297326503435441)
                ·
                  refine ⟨4290076553472994877576581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5720102071297326503435441 4290076553472994877576581)
                  ·
                    refine ⟨804389353776186539545609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290076553472994877576581 804389353776186539545609)
                    ·
                      refine ⟨603292015332139904659207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804389353776186539545609 603292015332139904659207)
                      ·
                        rfl

theorem cell23_1174907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4, 2].length) (baseStart_1174907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174907 prefixEnd_1174907 := by exact prefixLift 1174907
  have htrace : WordTrace (prefixWord ++ tailWord_1174907) baseStart_1174907 baseEnd_1174907 := by
    simpa [prefixWord, tailWord_1174907, baseEnd_1174907] using wordTrace_append hprefix tailTrace_1174907
  have hstable : (prefixWord ++ tailWord_1174907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174907).length < 2 ^ (prefixWord ++ tailWord_1174907).sum := by decide
  have hdescent : baseEnd_1174907 < baseStart_1174907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174917 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_1174917 : Nat := 118140960795 + 1174917 * 2 ^ 59
def prefixEnd_1174917 : Nat := 4983230072969 + 3 ^ 40 * 1174917 * 2
def baseEnd_1174917 : Nat := 201099050046228288511387

theorem tailTrace_1174917 : CollatzResearch.WordTrace tailWord_1174917 prefixEnd_1174917 201099050046228288511387 := by
  unfold tailWord_1174917
  simp only [CollatzResearch.WordTrace]
  refine ⟨42852743484483843693363005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28568495656322562462242003 42852743484483843693363005)
  ·
    refine ⟨16069778806681441385011127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42852743484483843693363005 16069778806681441385011127)
    ·
      refine ⟨24104668210022162077516691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16069778806681441385011127 24104668210022162077516691)
      ·
        refine ⟨36157002315033243116275037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24104668210022162077516691 36157002315033243116275037)
        ·
          refine ⟨13558875868137466168603139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36157002315033243116275037 13558875868137466168603139)
          ·
            refine ⟨20338313802206199252904709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13558875868137466168603139 20338313802206199252904709)
            ·
              refine ⟨3813433837913662359919633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20338313802206199252904709 3813433837913662359919633)
              ·
                refine ⟨2860075378435246769939725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3813433837913662359919633 2860075378435246769939725)
                ·
                  refine ⟨1072528266913217538727397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2860075378435246769939725 1072528266913217538727397)
                  ·
                    refine ⟨201099050046228288511387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072528266913217538727397 201099050046228288511387)
                    ·
                      rfl

theorem cell23_1174917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_1174917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174917 prefixEnd_1174917 := by exact prefixLift 1174917
  have htrace : WordTrace (prefixWord ++ tailWord_1174917) baseStart_1174917 baseEnd_1174917 := by
    simpa [prefixWord, tailWord_1174917, baseEnd_1174917] using wordTrace_append hprefix tailTrace_1174917
  have hstable : (prefixWord ++ tailWord_1174917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174917).length < 2 ^ (prefixWord ++ tailWord_1174917).sum := by decide
  have hdescent : baseEnd_1174917 < baseStart_1174917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1174974 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1174974 : Nat := 118140960795 + 1174974 * 2 ^ 59
def prefixEnd_1174974 : Nat := 4983230072969 + 3 ^ 40 * 1174974 * 2
def baseEnd_1174974 : Nat := 603326418535991142521399

theorem tailTrace_1174974 : CollatzResearch.WordTrace tailWord_1174974 prefixEnd_1174974 603326418535991142521399 := by
  unfold tailWord_1174974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356852805659667803523497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28569881630184894952125317 5356852805659667803523497)
  ·
    refine ⟨4017639604244750852642623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5356852805659667803523497 4017639604244750852642623)
    ·
      refine ⟨6026459406367126278963935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017639604244750852642623 6026459406367126278963935)
      ·
        refine ⟨9039689109550689418445903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026459406367126278963935 9039689109550689418445903)
        ·
          refine ⟨13559533664326034127668855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039689109550689418445903 13559533664326034127668855)
          ·
            refine ⟨20339300496489051191503283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13559533664326034127668855 20339300496489051191503283)
            ·
              refine ⟨30508950744733576787254925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20339300496489051191503283 30508950744733576787254925)
              ·
                refine ⟨11440856529275091295220597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30508950744733576787254925 11440856529275091295220597)
                ·
                  refine ⟨1072580299619539808926931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11440856529275091295220597 1072580299619539808926931)
                  ·
                    refine ⟨1608870449429309713390397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072580299619539808926931 1608870449429309713390397)
                    ·
                      refine ⟨603326418535991142521399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608870449429309713390397 603326418535991142521399)
                      ·
                        rfl

theorem cell23_1174974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1174974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1174974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1174974 prefixEnd_1174974 := by exact prefixLift 1174974
  have htrace : WordTrace (prefixWord ++ tailWord_1174974) baseStart_1174974 baseEnd_1174974 := by
    simpa [prefixWord, tailWord_1174974, baseEnd_1174974] using wordTrace_append hprefix tailTrace_1174974
  have hstable : (prefixWord ++ tailWord_1174974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1174974).length < 2 ^ (prefixWord ++ tailWord_1174974).sum := by decide
  have hdescent : baseEnd_1174974 < baseStart_1174974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1174974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175020 : List Nat := [2, 2, 1, 1, 2, 1, 2, 12]
def baseStart_1175020 : Nat := 118140960795 + 1175020 * 2 ^ 59
def prefixEnd_1175020 : Nat := 4983230072969 + 3 ^ 40 * 1175020 * 2
def baseEnd_1175020 : Nat := 22346297727633257872081

theorem tailTrace_1175020 : CollatzResearch.WordTrace tailWord_1175020 prefixEnd_1175020 22346297727633257872081 := by
  unfold tailWord_1175020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428250101555346142181257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28571000135407128189575009 21428250101555346142181257)
  ·
    refine ⟨16071187576166509606635943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21428250101555346142181257 16071187576166509606635943)
    ·
      refine ⟨24106781364249764409953915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16071187576166509606635943 24106781364249764409953915)
      ·
        refine ⟨36160172046374646614930873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24106781364249764409953915 36160172046374646614930873)
        ·
          refine ⟨27120129034780984961198155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36160172046374646614930873 27120129034780984961198155)
          ·
            refine ⟨40680193552171477441797233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27120129034780984961198155 40680193552171477441797233)
            ·
              refine ⟨30510145164128608081347925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40680193552171477441797233 30510145164128608081347925)
              ·
                refine ⟨22346297727633257872081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 30510145164128608081347925 22346297727633257872081)
                ·
                  rfl

theorem cell23_1175020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 12].length) (baseStart_1175020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175020 prefixEnd_1175020 := by exact prefixLift 1175020
  have htrace : WordTrace (prefixWord ++ tailWord_1175020) baseStart_1175020 baseEnd_1175020 := by
    simpa [prefixWord, tailWord_1175020, baseEnd_1175020] using wordTrace_append hprefix tailTrace_1175020
  have hstable : (prefixWord ++ tailWord_1175020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175020).length < 2 ^ (prefixWord ++ tailWord_1175020).sum := by decide
  have hdescent : baseEnd_1175020 < baseStart_1175020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175024 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_1175024 : Nat := 118140960795 + 1175024 * 2 ^ 59
def prefixEnd_1175024 : Nat := 4983230072969 + 3 ^ 40 * 1175024 * 2
def baseEnd_1175024 : Nat := 201117364189571982298723

theorem tailTrace_1175024 : CollatzResearch.WordTrace tailWord_1175024 prefixEnd_1175024 201117364189571982298723 := by
  unfold tailWord_1175024
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428323047548100483754063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28571097396730800645005417 21428323047548100483754063)
  ·
    refine ⟨32142484571322150725631095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21428323047548100483754063 32142484571322150725631095)
    ·
      refine ⟨48213726856983226088446643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32142484571322150725631095 48213726856983226088446643)
      ·
        refine ⟨72320590285474839132669965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48213726856983226088446643 72320590285474839132669965)
        ·
          refine ⟨27120221357053064674751237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72320590285474839132669965 27120221357053064674751237)
          ·
            refine ⟨5085041504447449626515857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27120221357053064674751237 5085041504447449626515857)
            ·
              refine ⟨3813781128335587219886893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085041504447449626515857 3813781128335587219886893)
              ·
                refine ⟨1430167923125845207457585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3813781128335587219886893 1430167923125845207457585)
                ·
                  refine ⟨1072625942344383905593189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430167923125845207457585 1072625942344383905593189)
                  ·
                    refine ⟨201117364189571982298723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1072625942344383905593189 201117364189571982298723)
                    ·
                      rfl

theorem cell23_1175024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_1175024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175024 prefixEnd_1175024 := by exact prefixLift 1175024
  have htrace : WordTrace (prefixWord ++ tailWord_1175024) baseStart_1175024 baseEnd_1175024 := by
    simpa [prefixWord, tailWord_1175024, baseEnd_1175024] using wordTrace_append hprefix tailTrace_1175024
  have hstable : (prefixWord ++ tailWord_1175024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175024).length < 2 ^ (prefixWord ++ tailWord_1175024).sum := by decide
  have hdescent : baseEnd_1175024 < baseStart_1175024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175034 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_1175034 : Nat := 118140960795 + 1175034 * 2 ^ 59
def prefixEnd_1175034 : Nat := 4983230072969 + 3 ^ 40 * 1175034 * 2
def baseEnd_1175034 : Nat := 603357227375260907771123

theorem tailTrace_1175034 : CollatzResearch.WordTrace tailWord_1175034 prefixEnd_1175034 603357227375260907771123 := by
  unfold tailWord_1175034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10714252706264993168843039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28571340550039981783581437 10714252706264993168843039)
  ·
    refine ⟨16071379059397489753264559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10714252706264993168843039 16071379059397489753264559)
    ·
      refine ⟨24107068589096234629896839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16071379059397489753264559 24107068589096234629896839)
      ·
        refine ⟨36160602883644351944845259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24107068589096234629896839 36160602883644351944845259)
        ·
          refine ⟨54240904325466527917267889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36160602883644351944845259 54240904325466527917267889)
          ·
            refine ⟨40680678244099895937950917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54240904325466527917267889 40680678244099895937950917)
            ·
              refine ⟨7627627170768730488365797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40680678244099895937950917 7627627170768730488365797)
              ·
                refine ⟨1430180094519136966568587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7627627170768730488365797 1430180094519136966568587)
                ·
                  refine ⟨2145270141778705449852881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430180094519136966568587 2145270141778705449852881)
                  ·
                    refine ⟨1608952606334029087389661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2145270141778705449852881 1608952606334029087389661)
                    ·
                      refine ⟨603357227375260907771123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608952606334029087389661 603357227375260907771123)
                      ·
                        rfl

theorem cell23_1175034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_1175034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175034 prefixEnd_1175034 := by exact prefixLift 1175034
  have htrace : WordTrace (prefixWord ++ tailWord_1175034) baseStart_1175034 baseEnd_1175034 := by
    simpa [prefixWord, tailWord_1175034, baseEnd_1175034] using wordTrace_append hprefix tailTrace_1175034
  have hstable : (prefixWord ++ tailWord_1175034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175034).length < 2 ^ (prefixWord ++ tailWord_1175034).sum := by decide
  have hdescent : baseEnd_1175034 < baseStart_1175034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175048 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_1175048 : Nat := 118140960795 + 1175048 * 2 ^ 59
def prefixEnd_1175048 : Nat := 4983230072969 + 3 ^ 40 * 1175048 * 2
def baseEnd_1175048 : Nat := 603364416104423852996059

theorem tailTrace_1175048 : CollatzResearch.WordTrace tailWord_1175048 prefixEnd_1175048 603364416104423852996059 := by
  unfold tailWord_1175048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21428760723504626533190899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28571680964672835377587865 21428760723504626533190899)
  ·
    refine ⟨32143141085256939799786349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21428760723504626533190899 32143141085256939799786349)
    ·
      refine ⟨12053677906971352424919881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32143141085256939799786349 12053677906971352424919881)
      ·
        refine ⟨9040258430228514318689911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12053677906971352424919881 9040258430228514318689911)
        ·
          refine ⟨13560387645342771478034867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040258430228514318689911 13560387645342771478034867)
          ·
            refine ⟨20340581468014157217052301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13560387645342771478034867 20340581468014157217052301)
            ·
              refine ⟨7627718050505308956394613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20340581468014157217052301 7627718050505308956394613)
              ·
                refine ⟨715098567234872714661995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7627718050505308956394613 715098567234872714661995)
                ·
                  refine ⟨1072647850852309071992993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715098567234872714661995 1072647850852309071992993)
                  ·
                    refine ⟨804485888139231803994745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1072647850852309071992993 804485888139231803994745)
                    ·
                      refine ⟨603364416104423852996059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804485888139231803994745 603364416104423852996059)
                      ·
                        rfl

theorem cell23_1175048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_1175048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175048 prefixEnd_1175048 := by exact prefixLift 1175048
  have htrace : WordTrace (prefixWord ++ tailWord_1175048) baseStart_1175048 baseEnd_1175048 := by
    simpa [prefixWord, tailWord_1175048, baseEnd_1175048] using wordTrace_append hprefix tailTrace_1175048
  have hstable : (prefixWord ++ tailWord_1175048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175048).length < 2 ^ (prefixWord ++ tailWord_1175048).sum := by decide
  have hdescent : baseEnd_1175048 < baseStart_1175048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175051 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 3]
def baseStart_1175051 : Nat := 118140960795 + 1175051 * 2 ^ 59
def prefixEnd_1175051 : Nat := 4983230072969 + 3 ^ 40 * 1175051 * 2
def baseEnd_1175051 : Nat := 603365956546387341258545

theorem tailTrace_1175051 : CollatzResearch.WordTrace tailWord_1175051 prefixEnd_1175051 603365956546387341258545 := by
  unfold tailWord_1175051
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857630865998384578741007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28571753910665589719160671 42857630865998384578741007)
  ·
    refine ⟨64286446298997576868111511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42857630865998384578741007 64286446298997576868111511)
    ·
      refine ⟨96429669448496365302167267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64286446298997576868111511 96429669448496365302167267)
      ·
        refine ⟨144644504172744547953250901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96429669448496365302167267 144644504172744547953250901)
        ·
          refine ⟨1695052783274350171327159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 144644504172744547953250901 1695052783274350171327159)
          ·
            refine ⟨2542579174911525256990739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695052783274350171327159 2542579174911525256990739)
            ·
              refine ⟨3813868762367287885486109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542579174911525256990739 3813868762367287885486109)
              ·
                refine ⟨1430200785887732957057291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3813868762367287885486109 1430200785887732957057291)
                ·
                  refine ⟨2145301178831599435585937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430200785887732957057291 2145301178831599435585937)
                  ·
                    refine ⟨1608975884123699576689453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2145301178831599435585937 1608975884123699576689453)
                    ·
                      refine ⟨603365956546387341258545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1608975884123699576689453 603365956546387341258545)
                      ·
                        rfl

theorem cell23_1175051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 3].length) (baseStart_1175051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175051 prefixEnd_1175051 := by exact prefixLift 1175051
  have htrace : WordTrace (prefixWord ++ tailWord_1175051) baseStart_1175051 baseEnd_1175051 := by
    simpa [prefixWord, tailWord_1175051, baseEnd_1175051] using wordTrace_append hprefix tailTrace_1175051
  have hstable : (prefixWord ++ tailWord_1175051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175051).length < 2 ^ (prefixWord ++ tailWord_1175051).sum := by decide
  have hdescent : baseEnd_1175051 < baseStart_1175051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175091 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 1, 3, 2]
def baseStart_1175091 : Nat := 118140960795 + 1175091 * 2 ^ 59
def prefixEnd_1175091 : Nat := 4983230072969 + 3 ^ 40 * 1175091 * 2
def baseEnd_1175091 : Nat := 603386495772567184758361

theorem tailTrace_1175091 : CollatzResearch.WordTrace tailWord_1175091 prefixEnd_1175091 603386495772567184758361 := by
  unfold tailWord_1175091
  simp only [CollatzResearch.WordTrace]
  refine ⟨42859089785853471410197127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28572726523902314273464751 42859089785853471410197127)
  ·
    refine ⟨64288634678780207115295691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42859089785853471410197127 64288634678780207115295691)
    ·
      refine ⟨96432952018170310672943537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64288634678780207115295691 96432952018170310672943537)
      ·
        refine ⟨72324714013627733004707653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96432952018170310672943537 72324714013627733004707653)
        ·
          refine ⟨13560883877555199938382685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72324714013627733004707653 13560883877555199938382685)
          ·
            refine ⟨5085331454083199976893507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13560883877555199938382685 5085331454083199976893507)
            ·
              refine ⟨7627997181124799965340261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085331454083199976893507 7627997181124799965340261)
              ·
                refine ⟨1430249471460899993501299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7627997181124799965340261 1430249471460899993501299)
                ·
                  refine ⟨2145374207191349990251949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430249471460899993501299 2145374207191349990251949)
                  ·
                    refine ⟨804515327696756246344481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145374207191349990251949 804515327696756246344481)
                    ·
                      refine ⟨603386495772567184758361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804515327696756246344481 603386495772567184758361)
                      ·
                        rfl

theorem cell23_1175091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3, 2].length) (baseStart_1175091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175091 prefixEnd_1175091 := by exact prefixLift 1175091
  have htrace : WordTrace (prefixWord ++ tailWord_1175091) baseStart_1175091 baseEnd_1175091 := by
    simpa [prefixWord, tailWord_1175091, baseEnd_1175091] using wordTrace_append hprefix tailTrace_1175091
  have hstable : (prefixWord ++ tailWord_1175091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175091).length < 2 ^ (prefixWord ++ tailWord_1175091).sum := by decide
  have hdescent : baseEnd_1175091 < baseStart_1175091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2]
def baseStart_1175104 : Nat := 118140960795 + 1175104 * 2 ^ 59
def prefixEnd_1175104 : Nat := 4983230072969 + 3 ^ 40 * 1175104 * 2
def baseEnd_1175104 : Nat := 603393171021075633895801

theorem tailTrace_1175104 : CollatzResearch.WordTrace tailWord_1175104 prefixEnd_1175104 603393171021075633895801 := by
  unfold tailWord_1175104
  simp only [CollatzResearch.WordTrace]
  refine ⟨21429781967403187315210183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28573042623204249753613577 21429781967403187315210183)
  ·
    refine ⟨32144672951104780972815275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21429781967403187315210183 32144672951104780972815275)
    ·
      refine ⟨48217009426657171459222913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32144672951104780972815275 48217009426657171459222913)
      ·
        refine ⟨36162757069992878594417185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48217009426657171459222913 36162757069992878594417185)
        ·
          refine ⟨27122067802494658945812889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36162757069992878594417185 27122067802494658945812889)
          ·
            refine ⟨20341550851870994209359667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27122067802494658945812889 20341550851870994209359667)
            ·
              refine ⟨30512326277806491314039501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20341550851870994209359667 30512326277806491314039501)
              ·
                refine ⟨11442122354177434242764813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30512326277806491314039501 11442122354177434242764813)
                ·
                  refine ⟨4290795882816537841036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11442122354177434242764813 4290795882816537841036805)
                  ·
                    refine ⟨804524228028100845194401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4290795882816537841036805 804524228028100845194401)
                    ·
                      refine ⟨603393171021075633895801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804524228028100845194401 603393171021075633895801)
                      ·
                        rfl

theorem cell23_1175104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_1175104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175104 prefixEnd_1175104 := by exact prefixLift 1175104
  have htrace : WordTrace (prefixWord ++ tailWord_1175104) baseStart_1175104 baseEnd_1175104 := by
    simpa [prefixWord, tailWord_1175104, baseEnd_1175104] using wordTrace_append hprefix tailTrace_1175104
  have hstable : (prefixWord ++ tailWord_1175104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175104).length < 2 ^ (prefixWord ++ tailWord_1175104).sum := by decide
  have hdescent : baseEnd_1175104 < baseStart_1175104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175107 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3]
def baseStart_1175107 : Nat := 118140960795 + 1175107 * 2 ^ 59
def prefixEnd_1175107 : Nat := 4983230072969 + 3 ^ 40 * 1175107 * 2
def baseEnd_1175107 : Nat := 603394711463039122158287

theorem tailTrace_1175107 : CollatzResearch.WordTrace tailWord_1175107 prefixEnd_1175107 603394711463039122158287 := by
  unfold tailWord_1175107
  simp only [CollatzResearch.WordTrace]
  refine ⟨42859673353795506142779575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28573115569197004095186383 42859673353795506142779575)
  ·
    refine ⟨64289510030693259214169363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42859673353795506142779575 64289510030693259214169363)
    ·
      refine ⟨96434265046039888821254045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64289510030693259214169363 96434265046039888821254045)
      ·
        refine ⟨36162849392264958307970267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96434265046039888821254045 36162849392264958307970267)
        ·
          refine ⟨54244274088397437461955401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36162849392264958307970267 54244274088397437461955401)
          ·
            refine ⟨40683205566298078096466551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54244274088397437461955401 40683205566298078096466551)
            ·
              refine ⟨61024808349447117144699827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40683205566298078096466551 61024808349447117144699827)
              ·
                refine ⟨91537212524170675717049741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61024808349447117144699827 91537212524170675717049741)
                ·
                  refine ⟨34326454696564003393893653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91537212524170675717049741 34326454696564003393893653)
                  ·
                    refine ⟨1609052563901437659088765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34326454696564003393893653 1609052563901437659088765)
                    ·
                      refine ⟨603394711463039122158287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609052563901437659088765 603394711463039122158287)
                      ·
                        rfl

theorem cell23_1175107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_1175107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175107 prefixEnd_1175107 := by exact prefixLift 1175107
  have htrace : WordTrace (prefixWord ++ tailWord_1175107) baseStart_1175107 baseEnd_1175107 := by
    simpa [prefixWord, tailWord_1175107, baseEnd_1175107] using wordTrace_append hprefix tailTrace_1175107
  have hstable : (prefixWord ++ tailWord_1175107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175107).length < 2 ^ (prefixWord ++ tailWord_1175107).sum := by decide
  have hdescent : baseEnd_1175107 < baseStart_1175107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175121 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_1175121 : Nat := 118140960795 + 1175121 * 2 ^ 59
def prefixEnd_1175121 : Nat := 4983230072969 + 3 ^ 40 * 1175121 * 2
def baseEnd_1175121 : Nat := 603401900192202067383223

theorem tailTrace_1175121 : CollatzResearch.WordTrace tailWord_1175121 prefixEnd_1175121 603401900192202067383223 := by
  unfold tailWord_1175121
  simp only [CollatzResearch.WordTrace]
  refine ⟨42860183975744786533789217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28573455983829857689192811 42860183975744786533789217)
  ·
    refine ⟨32145137981808589900341913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42860183975744786533789217 32145137981808589900341913)
    ·
      refine ⟨24108853486356442425256435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32145137981808589900341913 24108853486356442425256435)
      ·
        refine ⟨36163280229534663637884653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24108853486356442425256435 36163280229534663637884653)
        ·
          refine ⟨13561230086075498864206745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36163280229534663637884653 13561230086075498864206745)
          ·
            refine ⟨10170922564556624148155059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13561230086075498864206745 10170922564556624148155059)
            ·
              refine ⟨15256383846834936222232589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10170922564556624148155059 15256383846834936222232589)
              ·
                refine ⟨5721143942563101083337221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15256383846834936222232589 5721143942563101083337221)
                ·
                  refine ⟨1072714489230581453125729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5721143942563101083337221 1072714489230581453125729)
                  ·
                    refine ⟨804535866922936089844297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1072714489230581453125729 804535866922936089844297)
                    ·
                      refine ⟨603401900192202067383223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804535866922936089844297 603401900192202067383223)
                      ·
                        rfl

theorem cell23_1175121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_1175121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175121 prefixEnd_1175121 := by exact prefixLift 1175121
  have htrace : WordTrace (prefixWord ++ tailWord_1175121) baseStart_1175121 baseEnd_1175121 := by
    simpa [prefixWord, tailWord_1175121, baseEnd_1175121] using wordTrace_append hprefix tailTrace_1175121
  have hstable : (prefixWord ++ tailWord_1175121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175121).length < 2 ^ (prefixWord ++ tailWord_1175121).sum := by decide
  have hdescent : baseEnd_1175121 < baseStart_1175121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175124 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1175124 : Nat := 118140960795 + 1175124 * 2 ^ 59
def prefixEnd_1175124 : Nat := 4983230072969 + 3 ^ 40 * 1175124 * 2
def baseEnd_1175124 : Nat := 603403440634165555645709

theorem tailTrace_1175124 : CollatzResearch.WordTrace tailWord_1175124 prefixEnd_1175124 603403440634165555645709 := by
  unfold tailWord_1175124
  simp only [CollatzResearch.WordTrace]
  refine ⟨21430146697366959023074213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28573528929822612030765617 21430146697366959023074213)
  ·
    refine ⟨4018152505756304816826415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21430146697366959023074213 4018152505756304816826415)
    ·
      refine ⟨6027228758634457225239623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018152505756304816826415 6027228758634457225239623)
      ·
        refine ⟨9040843137951685837859435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6027228758634457225239623 9040843137951685837859435)
        ·
          refine ⟨13561264706927528756789153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040843137951685837859435 13561264706927528756789153)
          ·
            refine ⟨10170948530195646567591865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13561264706927528756789153 10170948530195646567591865)
            ·
              refine ⟨7628211397646734925693899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10170948530195646567591865 7628211397646734925693899)
              ·
                refine ⟨11442317096470102388540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628211397646734925693899 11442317096470102388540849)
                ·
                  refine ⟨8581737822352576791405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11442317096470102388540849 8581737822352576791405637)
                  ·
                    refine ⟨1609075841691108148388557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8581737822352576791405637 1609075841691108148388557)
                    ·
                      refine ⟨603403440634165555645709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609075841691108148388557 603403440634165555645709)
                      ·
                        rfl

theorem cell23_1175124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1175124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175124 prefixEnd_1175124 := by exact prefixLift 1175124
  have htrace : WordTrace (prefixWord ++ tailWord_1175124) baseStart_1175124 baseEnd_1175124 := by
    simpa [prefixWord, tailWord_1175124, baseEnd_1175124] using wordTrace_append hprefix tailTrace_1175124
  have hstable : (prefixWord ++ tailWord_1175124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175124).length < 2 ^ (prefixWord ++ tailWord_1175124).sum := by decide
  have hdescent : baseEnd_1175124 < baseStart_1175124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175178 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_1175178 : Nat := 118140960795 + 1175178 * 2 ^ 59
def prefixEnd_1175178 : Nat := 4983230072969 + 3 ^ 40 * 1175178 * 2
def baseEnd_1175178 : Nat := 67047907621056482707829

theorem tailTrace_1175178 : CollatzResearch.WordTrace tailWord_1175178 prefixEnd_1175178 67047907621056482707829 := by
  unfold tailWord_1175178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10715565734134571317153547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28574841957692190179076125 10715565734134571317153547)
  ·
    refine ⟨16073348601201856975730321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10715565734134571317153547 16073348601201856975730321)
    ·
      refine ⟨12055011450901392731797741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16073348601201856975730321 12055011450901392731797741)
      ·
        refine ⟨4520629294088022274424153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12055011450901392731797741 4520629294088022274424153)
        ·
          refine ⟨3390471970566016705818115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4520629294088022274424153 3390471970566016705818115)
          ·
            refine ⟨5085707955849025058727173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390471970566016705818115 5085707955849025058727173)
            ·
              refine ⟨953570241721692198511345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5085707955849025058727173 953570241721692198511345)
              ·
                refine ⟨715177681291269148883509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953570241721692198511345 715177681291269148883509)
                ·
                  refine ⟨67047907621056482707829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715177681291269148883509 67047907621056482707829)
                  ·
                    rfl

theorem cell23_1175178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_1175178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175178 prefixEnd_1175178 := by exact prefixLift 1175178
  have htrace : WordTrace (prefixWord ++ tailWord_1175178) baseStart_1175178 baseEnd_1175178 := by
    simpa [prefixWord, tailWord_1175178, baseEnd_1175178] using wordTrace_append hprefix tailTrace_1175178
  have hstable : (prefixWord ++ tailWord_1175178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175178).length < 2 ^ (prefixWord ++ tailWord_1175178).sum := by decide
  have hdescent : baseEnd_1175178 < baseStart_1175178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175188 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1175188 : Nat := 118140960795 + 1175188 * 2 ^ 59
def prefixEnd_1175188 : Nat := 4983230072969 + 3 ^ 40 * 1175188 * 2
def baseEnd_1175188 : Nat := 603436303396053305245415

theorem tailTrace_1175188 : CollatzResearch.WordTrace tailWord_1175188 prefixEnd_1175188 603436303396053305245415 := by
  unfold tailWord_1175188
  simp only [CollatzResearch.WordTrace]
  refine ⟨21431313833251028488239109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28575085111001371317652145 21431313833251028488239109)
  ·
    refine ⟨4018371343734567841544833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21431313833251028488239109 4018371343734567841544833)
    ·
      refine ⟨3013778507800925881158625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4018371343734567841544833 3013778507800925881158625)
      ·
        refine ⟨2260333880850694410868969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3013778507800925881158625 2260333880850694410868969)
        ·
          refine ⟨1695250410638020808151727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260333880850694410868969 1695250410638020808151727)
          ·
            refine ⟨2542875615957031212227591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695250410638020808151727 2542875615957031212227591)
            ·
              refine ⟨3814313423935546818341387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542875615957031212227591 3814313423935546818341387)
              ·
                refine ⟨5721470135903320227512081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814313423935546818341387 5721470135903320227512081)
                ·
                  refine ⟨4291102601927490170634061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721470135903320227512081 4291102601927490170634061)
                  ·
                    refine ⟨1609163475722808813987773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4291102601927490170634061 1609163475722808813987773)
                    ·
                      refine ⟨603436303396053305245415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609163475722808813987773 603436303396053305245415)
                      ·
                        rfl

theorem cell23_1175188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1175188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175188 prefixEnd_1175188 := by exact prefixLift 1175188
  have htrace : WordTrace (prefixWord ++ tailWord_1175188) baseStart_1175188 baseEnd_1175188 := by
    simpa [prefixWord, tailWord_1175188, baseEnd_1175188] using wordTrace_append hprefix tailTrace_1175188
  have hstable : (prefixWord ++ tailWord_1175188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175188).length < 2 ^ (prefixWord ++ tailWord_1175188).sum := by decide
  have hdescent : baseEnd_1175188 < baseStart_1175188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175245 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1175245 : Nat := 118140960795 + 1175245 * 2 ^ 59
def prefixEnd_1175245 : Nat := 4983230072969 + 3 ^ 40 * 1175245 * 2
def baseEnd_1175245 : Nat := 603465571793359582232653

theorem tailTrace_1175245 : CollatzResearch.WordTrace tailWord_1175245 prefixEnd_1175245 603465571793359582232653 := by
  unfold tailWord_1175245
  simp only [CollatzResearch.WordTrace]
  refine ⟨42864706627295555711303189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28576471084863703807535459 42864706627295555711303189)
  ·
    refine ⟨2009283123154479173967337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42864706627295555711303189 2009283123154479173967337)
    ·
      refine ⟨1506962342365859380475503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2009283123154479173967337 1506962342365859380475503)
      ·
        refine ⟨2260443513548789070713255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1506962342365859380475503 2260443513548789070713255)
        ·
          refine ⟨3390665270323183606069883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260443513548789070713255 3390665270323183606069883)
          ·
            refine ⟨5085997905484775409104825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390665270323183606069883 5085997905484775409104825)
            ·
              refine ⟨3814498429113581556828619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085997905484775409104825 3814498429113581556828619)
              ·
                refine ⟨5721747643670372335242929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814498429113581556828619 5721747643670372335242929)
                ·
                  refine ⟨4291310732752779251432197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721747643670372335242929 4291310732752779251432197)
                  ·
                    refine ⟨804620762391146109643537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4291310732752779251432197 804620762391146109643537)
                    ·
                      refine ⟨603465571793359582232653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804620762391146109643537 603465571793359582232653)
                      ·
                        rfl

theorem cell23_1175245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1175245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175245 prefixEnd_1175245 := by exact prefixLift 1175245
  have htrace : WordTrace (prefixWord ++ tailWord_1175245) baseStart_1175245 baseEnd_1175245 := by
    simpa [prefixWord, tailWord_1175245, baseEnd_1175245] using wordTrace_append hprefix tailTrace_1175245
  have hstable : (prefixWord ++ tailWord_1175245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175245).length < 2 ^ (prefixWord ++ tailWord_1175245).sum := by decide
  have hdescent : baseEnd_1175245 < baseStart_1175245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175264 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_1175264 : Nat := 118140960795 + 1175264 * 2 ^ 59
def prefixEnd_1175264 : Nat := 4983230072969 + 3 ^ 40 * 1175264 * 2
def baseEnd_1175264 : Nat := 201158442641931669298355

theorem tailTrace_1175264 : CollatzResearch.WordTrace tailWord_1175264 prefixEnd_1175264 201158442641931669298355 := by
  unfold tailWord_1175264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432699807113360978122423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28576933076151147970829897 21432699807113360978122423)
  ·
    refine ⟨32149049710670041467183635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21432699807113360978122423 32149049710670041467183635)
    ·
      refine ⟨48223574566005062200775453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32149049710670041467183635 48223574566005062200775453)
      ·
        refine ⟨18083840462251898325290795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48223574566005062200775453 18083840462251898325290795)
        ·
          refine ⟨27125760693377847487936193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18083840462251898325290795 27125760693377847487936193)
          ·
            refine ⟨20344320520033385615952145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27125760693377847487936193 20344320520033385615952145)
            ·
              refine ⟨15258240390025039211964109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20344320520033385615952145 15258240390025039211964109)
              ·
                refine ⟨5721840146259389704486541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15258240390025039211964109 5721840146259389704486541)
                ·
                  refine ⟨2145690054847271139182453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5721840146259389704486541 2145690054847271139182453)
                  ·
                    refine ⟨201158442641931669298355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2145690054847271139182453 201158442641931669298355)
                    ·
                      rfl

theorem cell23_1175264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_1175264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175264 prefixEnd_1175264 := by exact prefixLift 1175264
  have htrace : WordTrace (prefixWord ++ tailWord_1175264) baseStart_1175264 baseEnd_1175264 := by
    simpa [prefixWord, tailWord_1175264, baseEnd_1175264] using wordTrace_append hprefix tailTrace_1175264
  have hstable : (prefixWord ++ tailWord_1175264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175264).length < 2 ^ (prefixWord ++ tailWord_1175264).sum := by decide
  have hdescent : baseEnd_1175264 < baseStart_1175264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175281 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1175281 : Nat := 118140960795 + 1175281 * 2 ^ 59
def prefixEnd_1175281 : Nat := 4983230072969 + 3 ^ 40 * 1175281 * 2
def baseEnd_1175281 : Nat := 201161352365640480460829

theorem tailTrace_1175281 : CollatzResearch.WordTrace tailWord_1175281 prefixEnd_1175281 201161352365640480460829 := by
  unfold tailWord_1175281
  simp only [CollatzResearch.WordTrace]
  refine ⟨42866019655165133859613697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28577346436776755906409131 42866019655165133859613697)
  ·
    refine ⟨32149514741373850394710273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42866019655165133859613697 32149514741373850394710273)
    ·
      refine ⟨24112136056030387796032705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32149514741373850394710273 24112136056030387796032705)
      ·
        refine ⟨18084102042022790847024529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24112136056030387796032705 18084102042022790847024529)
        ·
          refine ⟨13563076531517093135268397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18084102042022790847024529 13563076531517093135268397)
          ·
            refine ⟨5086153699318909925725649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13563076531517093135268397 5086153699318909925725649)
            ·
              refine ⟨3814615274489182444294237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086153699318909925725649 3814615274489182444294237)
              ·
                refine ⟨1430480727933443416610339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3814615274489182444294237 1430480727933443416610339)
                ·
                  refine ⟨2145721091900165124915509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430480727933443416610339 2145721091900165124915509)
                  ·
                    refine ⟨201161352365640480460829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2145721091900165124915509 201161352365640480460829)
                    ·
                      rfl

theorem cell23_1175281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1175281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175281 prefixEnd_1175281 := by exact prefixLift 1175281
  have htrace : WordTrace (prefixWord ++ tailWord_1175281) baseStart_1175281 baseEnd_1175281 := by
    simpa [prefixWord, tailWord_1175281, baseEnd_1175281] using wordTrace_append hprefix tailTrace_1175281
  have hstable : (prefixWord ++ tailWord_1175281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175281).length < 2 ^ (prefixWord ++ tailWord_1175281).sum := by decide
  have hdescent : baseEnd_1175281 < baseStart_1175281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175324 : List Nat := [2, 2, 3, 1, 1, 2, 1, 11]
def baseStart_1175324 : Nat := 118140960795 + 1175324 * 2 ^ 59
def prefixEnd_1175324 : Nat := 4983230072969 + 3 ^ 40 * 1175324 * 2
def baseEnd_1175324 : Nat := 22352079139446843449807

theorem tailTrace_1175324 : CollatzResearch.WordTrace tailWord_1175324 prefixEnd_1175324 22352079139446843449807 := by
  unfold tailWord_1175324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433793997004676101714513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28578391996006234802286017 21433793997004676101714513)
  ·
    refine ⟨16075345497753507076285885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21433793997004676101714513 16075345497753507076285885)
    ·
      refine ⟨6028254561657565153607207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16075345497753507076285885 6028254561657565153607207)
      ·
        refine ⟨9042381842486347730410811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028254561657565153607207 9042381842486347730410811)
        ·
          refine ⟨13563572763729521595616217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042381842486347730410811 13563572763729521595616217)
          ·
            refine ⟨10172679572797141196712163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13563572763729521595616217 10172679572797141196712163)
            ·
              refine ⟨15259019359195711795068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172679572797141196712163 15259019359195711795068245)
              ·
                refine ⟨22352079139446843449807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15259019359195711795068245 22352079139446843449807)
                ·
                  rfl

theorem cell23_1175324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 11].length) (baseStart_1175324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175324 prefixEnd_1175324 := by exact prefixLift 1175324
  have htrace : WordTrace (prefixWord ++ tailWord_1175324) baseStart_1175324 baseEnd_1175324 := by
    simpa [prefixWord, tailWord_1175324, baseEnd_1175324] using wordTrace_append hprefix tailTrace_1175324
  have hstable : (prefixWord ++ tailWord_1175324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175324).length < 2 ^ (prefixWord ++ tailWord_1175324).sum := by decide
  have hdescent : baseEnd_1175324 < baseStart_1175324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175352 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_1175352 : Nat := 118140960795 + 1175352 * 2 ^ 59
def prefixEnd_1175352 : Nat := 4983230072969 + 3 ^ 40 * 1175352 * 2
def baseEnd_1175352 : Nat := 603520514223390663594661

theorem tailTrace_1175352 : CollatzResearch.WordTrace tailWord_1175352 prefixEnd_1175352 603520514223390663594661 := by
  unfold tailWord_1175352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434304618953956492724155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28579072825271941990298873 21434304618953956492724155)
  ·
    refine ⟨32151456928430934739086233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21434304618953956492724155 32151456928430934739086233)
    ·
      refine ⟨24113592696323201054314675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32151456928430934739086233 24113592696323201054314675)
      ·
        refine ⟨36170389044484801581472013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24113592696323201054314675 36170389044484801581472013)
        ·
          refine ⟨13563895891681800593052005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36170389044484801581472013 13563895891681800593052005)
          ·
            refine ⟨2543230479690337611197251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13563895891681800593052005 2543230479690337611197251)
            ·
              refine ⟨3814845719535506416795877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543230479690337611197251 3814845719535506416795877)
              ·
                refine ⟨715283572412907453149227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3814845719535506416795877 715283572412907453149227)
                ·
                  refine ⟨1072925358619361179723841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715283572412907453149227 1072925358619361179723841)
                  ·
                    refine ⟨804694018964520884792881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1072925358619361179723841 804694018964520884792881)
                    ·
                      refine ⟨603520514223390663594661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804694018964520884792881 603520514223390663594661)
                      ·
                        rfl

theorem cell23_1175352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_1175352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175352 prefixEnd_1175352 := by exact prefixLift 1175352
  have htrace : WordTrace (prefixWord ++ tailWord_1175352) baseStart_1175352 baseEnd_1175352 := by
    simpa [prefixWord, tailWord_1175352, baseEnd_1175352] using wordTrace_append hprefix tailTrace_1175352
  have hstable : (prefixWord ++ tailWord_1175352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175352).length < 2 ^ (prefixWord ++ tailWord_1175352).sum := by decide
  have hdescent : baseEnd_1175352 < baseStart_1175352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175358 : List Nat := [4, 2, 1, 2, 2, 3, 1, 8]
def baseStart_1175358 : Nat := 118140960795 + 1175358 * 2 ^ 59
def prefixEnd_1175358 : Nat := 4983230072969 + 3 ^ 40 * 1175358 * 2
def baseEnd_1175358 : Nat := 22352725744715468152579

theorem tailTrace_1175358 : CollatzResearch.WordTrace tailWord_1175358 prefixEnd_1175358 22352725744715468152579 := by
  unfold tailWord_1175358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358603509485772001270841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28579218717257450673444485 5358603509485772001270841)
  ·
    refine ⟨4018952632114329000953131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5358603509485772001270841 4018952632114329000953131)
    ·
      refine ⟨6028428948171493501429697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018952632114329000953131 6028428948171493501429697)
      ·
        refine ⟨4521321711128620126072273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6028428948171493501429697 4521321711128620126072273)
        ·
          refine ⟨3390991283346465094554205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4521321711128620126072273 3390991283346465094554205)
          ·
            refine ⟨1271621731254924410457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3390991283346465094554205 1271621731254924410457827)
            ·
              refine ⟨1907432596882386615686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271621731254924410457827 1907432596882386615686741)
              ·
                refine ⟨22352725744715468152579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1907432596882386615686741 22352725744715468152579)
                ·
                  rfl

theorem cell23_1175358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_1175358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175358 prefixEnd_1175358 := by exact prefixLift 1175358
  have htrace : WordTrace (prefixWord ++ tailWord_1175358) baseStart_1175358 baseEnd_1175358 := by
    simpa [prefixWord, tailWord_1175358, baseEnd_1175358] using wordTrace_append hprefix tailTrace_1175358
  have hstable : (prefixWord ++ tailWord_1175358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175358).length < 2 ^ (prefixWord ++ tailWord_1175358).sum := by decide
  have hdescent : baseEnd_1175358 < baseStart_1175358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175368 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1175368 : Nat := 118140960795 + 1175368 * 2 ^ 59
def prefixEnd_1175368 : Nat := 4983230072969 + 3 ^ 40 * 1175368 * 2
def baseEnd_1175368 : Nat := 603528729913862600994587

theorem tailTrace_1175368 : CollatzResearch.WordTrace tailWord_1175368 prefixEnd_1175368 603528729913862600994587 := by
  unfold tailWord_1175368
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434596402924973859015379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28579461870566631812020505 21434596402924973859015379)
  ·
    refine ⟨32151894604387460788523069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21434596402924973859015379 32151894604387460788523069)
    ·
      refine ⟨12056960476645297795696151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32151894604387460788523069 12056960476645297795696151)
      ·
        refine ⟨18085440714967946693544227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12056960476645297795696151 18085440714967946693544227)
        ·
          refine ⟨27128161072451920040316341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18085440714967946693544227 27128161072451920040316341)
          ·
            refine ⟨2543265100542367503779657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27128161072451920040316341 2543265100542367503779657)
            ·
              refine ⟨1907448825406775627834743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543265100542367503779657 1907448825406775627834743)
              ·
                refine ⟨2861173238110163441752115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907448825406775627834743 2861173238110163441752115)
                ·
                  refine ⟨4291759857165245162628173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861173238110163441752115 4291759857165245162628173)
                  ·
                    refine ⟨1609409946436966935985565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4291759857165245162628173 1609409946436966935985565)
                    ·
                      refine ⟨603528729913862600994587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609409946436966935985565 603528729913862600994587)
                      ·
                        rfl

theorem cell23_1175368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1175368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175368 prefixEnd_1175368 := by exact prefixLift 1175368
  have htrace : WordTrace (prefixWord ++ tailWord_1175368) baseStart_1175368 baseEnd_1175368 := by
    simpa [prefixWord, tailWord_1175368, baseEnd_1175368] using wordTrace_append hprefix tailTrace_1175368
  have hstable : (prefixWord ++ tailWord_1175368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175368).length < 2 ^ (prefixWord ++ tailWord_1175368).sum := by decide
  have hdescent : baseEnd_1175368 < baseStart_1175368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175402 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1175402 : Nat := 118140960795 + 1175402 * 2 ^ 59
def prefixEnd_1175402 : Nat := 4983230072969 + 3 ^ 40 * 1175402 * 2
def baseEnd_1175402 : Nat := 603546188256115467969431

theorem tailTrace_1175402 : CollatzResearch.WordTrace tailWord_1175402 prefixEnd_1175402 603546188256115467969431 := by
  unfold tailWord_1175402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717608221931692881192115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28580288591817847683178973 10717608221931692881192115)
  ·
    refine ⟨16076412332897539321788173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10717608221931692881192115 16076412332897539321788173)
    ·
      refine ⟨6028654624836577245670565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16076412332897539321788173 6028654624836577245670565)
      ·
        refine ⟨1130372742156858233563231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6028654624836577245670565 1130372742156858233563231)
        ·
          refine ⟨1695559113235287350344847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130372742156858233563231 1695559113235287350344847)
          ·
            refine ⟨2543338669852931025517271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695559113235287350344847 2543338669852931025517271)
            ·
              refine ⟨3815008004779396538275907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543338669852931025517271 3815008004779396538275907)
              ·
                refine ⟨5722512007169094807413861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815008004779396538275907 5722512007169094807413861)
                ·
                  refine ⟨1072971001344205276390099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5722512007169094807413861 1072971001344205276390099)
                  ·
                    refine ⟨1609456502016307914585149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072971001344205276390099 1609456502016307914585149)
                    ·
                      refine ⟨603546188256115467969431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609456502016307914585149 603546188256115467969431)
                      ·
                        rfl

theorem cell23_1175402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1175402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175402 prefixEnd_1175402 := by exact prefixLift 1175402
  have htrace : WordTrace (prefixWord ++ tailWord_1175402) baseStart_1175402 baseEnd_1175402 := by
    simpa [prefixWord, tailWord_1175402, baseEnd_1175402] using wordTrace_append hprefix tailTrace_1175402
  have hstable : (prefixWord ++ tailWord_1175402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175402).length < 2 ^ (prefixWord ++ tailWord_1175402).sum := by decide
  have hdescent : baseEnd_1175402 < baseStart_1175402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175441 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_1175441 : Nat := 118140960795 + 1175441 * 2 ^ 59
def prefixEnd_1175441 : Nat := 4983230072969 + 3 ^ 40 * 1175441 * 2
def baseEnd_1175441 : Nat := 603566214001640815381751

theorem tailTrace_1175441 : CollatzResearch.WordTrace tailWord_1175441 prefixEnd_1175441 603566214001640815381751 := by
  unfold tailWord_1175441
  simp only [CollatzResearch.WordTrace]
  refine ⟨42871855334585481185438177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28581236889723654123625451 42871855334585481185438177)
  ·
    refine ⟨32153891500939110889078633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42871855334585481185438177 32153891500939110889078633)
    ·
      refine ⟨24115418625704333166808975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32153891500939110889078633 24115418625704333166808975)
      ·
        refine ⟨36173127938556499750213463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24115418625704333166808975 36173127938556499750213463)
        ·
          refine ⟨54259691907834749625320195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36173127938556499750213463 54259691907834749625320195)
          ·
            refine ⟨81389537861752124437980293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54259691907834749625320195 81389537861752124437980293)
            ·
              refine ⟨15260538349078523332121305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81389537861752124437980293 15260538349078523332121305)
              ·
                refine ⟨11445403761808892499090979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15260538349078523332121305 11445403761808892499090979)
                ·
                  refine ⟨17168105642713338748636469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445403761808892499090979 17168105642713338748636469)
                  ·
                    refine ⟨1609509904004375507684669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17168105642713338748636469 1609509904004375507684669)
                    ·
                      refine ⟨603566214001640815381751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609509904004375507684669 603566214001640815381751)
                      ·
                        rfl

theorem cell23_1175441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_1175441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175441 prefixEnd_1175441 := by exact prefixLift 1175441
  have htrace : WordTrace (prefixWord ++ tailWord_1175441) baseStart_1175441 baseEnd_1175441 := by
    simpa [prefixWord, tailWord_1175441, baseEnd_1175441] using wordTrace_append hprefix tailTrace_1175441
  have hstable : (prefixWord ++ tailWord_1175441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175441).length < 2 ^ (prefixWord ++ tailWord_1175441).sum := by decide
  have hdescent : baseEnd_1175441 < baseStart_1175441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175442 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1175442 : Nat := 118140960795 + 1175442 * 2 ^ 59
def prefixEnd_1175442 : Nat := 4983230072969 + 3 ^ 40 * 1175442 * 2
def baseEnd_1175442 : Nat := 603566727482295311469247

theorem tailTrace_1175442 : CollatzResearch.WordTrace tailWord_1175442 prefixEnd_1175442 603566727482295311469247 := by
  unfold tailWord_1175442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717972951895464589056145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28581261205054572237483053 10717972951895464589056145)
  ·
    refine ⟨8038479713921598441792109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10717972951895464589056145 8038479713921598441792109)
    ·
      refine ⟨3014429892720599415672041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8038479713921598441792109 3014429892720599415672041)
      ·
        refine ⟨2260822419540449561754031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3014429892720599415672041 2260822419540449561754031)
        ·
          refine ⟨3391233629310674342631047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260822419540449561754031 3391233629310674342631047)
          ·
            refine ⟨5086850443966011513946571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391233629310674342631047 5086850443966011513946571)
            ·
              refine ⟨7630275665949017270919857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086850443966011513946571 7630275665949017270919857)
              ·
                refine ⟨5722706749461762953189893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7630275665949017270919857 5722706749461762953189893)
                ·
                  refine ⟨1073007515524080553723105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5722706749461762953189893 1073007515524080553723105)
                  ·
                    refine ⟨804755636643060415292329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073007515524080553723105 804755636643060415292329)
                    ·
                      refine ⟨603566727482295311469247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804755636643060415292329 603566727482295311469247)
                      ·
                        rfl

theorem cell23_1175442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1175442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175442 prefixEnd_1175442 := by exact prefixLift 1175442
  have htrace : WordTrace (prefixWord ++ tailWord_1175442) baseStart_1175442 baseEnd_1175442 := by
    simpa [prefixWord, tailWord_1175442, baseEnd_1175442] using wordTrace_append hprefix tailTrace_1175442
  have hstable : (prefixWord ++ tailWord_1175442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175442).length < 2 ^ (prefixWord ++ tailWord_1175442).sum := by decide
  have hdescent : baseEnd_1175442 < baseStart_1175442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175470 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1175470 : Nat := 118140960795 + 1175470 * 2 ^ 59
def prefixEnd_1175470 : Nat := 4983230072969 + 3 ^ 40 * 1175470 * 2
def baseEnd_1175470 : Nat := 603581104940621201919119

theorem tailTrace_1175470 : CollatzResearch.WordTrace tailWord_1175470 prefixEnd_1175470 603581104940621201919119 := by
  unfold tailWord_1175470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359114131435052392280483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28581942034320279425495909 5359114131435052392280483)
  ·
    refine ⟨8038671197152578588420725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5359114131435052392280483 8038671197152578588420725)
    ·
      refine ⟨753625424733054242664443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8038671197152578588420725 753625424733054242664443)
      ·
        refine ⟨1130438137099581363996665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753625424733054242664443 1130438137099581363996665)
        ·
          refine ⟨847828602824686022997499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130438137099581363996665 847828602824686022997499)
          ·
            refine ⟨1271742904237029034496249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847828602824686022997499 1271742904237029034496249)
            ·
              refine ⟨953807178177771775872187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271742904237029034496249 953807178177771775872187)
              ·
                refine ⟨1430710767266657663808281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 953807178177771775872187 1430710767266657663808281)
                ·
                  refine ⟨1073033075449993247856211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430710767266657663808281 1073033075449993247856211)
                  ·
                    refine ⟨1609549613174989871784317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073033075449993247856211 1609549613174989871784317)
                    ·
                      refine ⟨603581104940621201919119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609549613174989871784317 603581104940621201919119)
                      ·
                        rfl

theorem cell23_1175470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1175470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175470 prefixEnd_1175470 := by exact prefixLift 1175470
  have htrace : WordTrace (prefixWord ++ tailWord_1175470) baseStart_1175470 baseEnd_1175470 := by
    simpa [prefixWord, tailWord_1175470, baseEnd_1175470] using wordTrace_append hprefix tailTrace_1175470
  have hstable : (prefixWord ++ tailWord_1175470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175470).length < 2 ^ (prefixWord ++ tailWord_1175470).sum := by decide
  have hdescent : baseEnd_1175470 < baseStart_1175470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175471 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_1175471 : Nat := 118140960795 + 1175471 * 2 ^ 59
def prefixEnd_1175471 : Nat := 4983230072969 + 3 ^ 40 * 1175471 * 2
def baseEnd_1175471 : Nat := 603581618421275698006613

theorem tailTrace_1175471 : CollatzResearch.WordTrace tailWord_1175471 prefixEnd_1175471 603581618421275698006613 := by
  unfold tailWord_1175471
  simp only [CollatzResearch.WordTrace]
  refine ⟨42872949524476796309030267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28581966349651197539353511 42872949524476796309030267)
  ·
    refine ⟨64309424286715194463545401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42872949524476796309030267 64309424286715194463545401)
    ·
      refine ⟨48232068215036395847659051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64309424286715194463545401 48232068215036395847659051)
      ·
        refine ⟨72348102322554593771488577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48232068215036395847659051 72348102322554593771488577)
        ·
          refine ⟨54261076741915945328616433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72348102322554593771488577 54261076741915945328616433)
          ·
            refine ⟨40695807556436958996462325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54261076741915945328616433 40695807556436958996462325)
            ·
              refine ⟨3815231958415964905918343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40695807556436958996462325 3815231958415964905918343)
              ·
                refine ⟨5722847937623947358877515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815231958415964905918343 5722847937623947358877515)
                ·
                  refine ⟨8584271906435921038316273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5722847937623947358877515 8584271906435921038316273)
                  ·
                    refine ⟨6438203929826940778737205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8584271906435921038316273 6438203929826940778737205)
                    ·
                      refine ⟨603581618421275698006613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6438203929826940778737205 603581618421275698006613)
                      ·
                        rfl

theorem cell23_1175471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_1175471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175471 prefixEnd_1175471 := by exact prefixLift 1175471
  have htrace : WordTrace (prefixWord ++ tailWord_1175471) baseStart_1175471 baseEnd_1175471 := by
    simpa [prefixWord, tailWord_1175471, baseEnd_1175471] using wordTrace_append hprefix tailTrace_1175471
  have hstable : (prefixWord ++ tailWord_1175471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175471).length < 2 ^ (prefixWord ++ tailWord_1175471).sum := by decide
  have hdescent : baseEnd_1175471 < baseStart_1175471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175476 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1175476 : Nat := 118140960795 + 1175476 * 2 ^ 59
def prefixEnd_1175476 : Nat := 4983230072969 + 3 ^ 40 * 1175476 * 2
def baseEnd_1175476 : Nat := 603584185824548178444091

theorem tailTrace_1175476 : CollatzResearch.WordTrace tailWord_1175476 prefixEnd_1175476 603584185824548178444091 := by
  unfold tailWord_1175476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21436565944729341081481141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28582087926305788108641521 21436565944729341081481141)
  ·
    refine ⟨2009678057318375726388857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21436565944729341081481141 2009678057318375726388857)
    ·
      refine ⟨1507258542988781794791643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2009678057318375726388857 1507258542988781794791643)
      ·
        refine ⟨2260887814483172692187465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507258542988781794791643 2260887814483172692187465)
        ·
          refine ⟨1695665860862379519140599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260887814483172692187465 1695665860862379519140599)
          ·
            refine ⟨2543498791293569278710899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695665860862379519140599 2543498791293569278710899)
            ·
              refine ⟨3815248186940353918066349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543498791293569278710899 3815248186940353918066349)
              ·
                refine ⟨1430718070102632719274881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3815248186940353918066349 1430718070102632719274881)
                ·
                  refine ⟨1073038552576974539456161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1430718070102632719274881 1073038552576974539456161)
                  ·
                    refine ⟨804778914432730904592121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073038552576974539456161 804778914432730904592121)
                    ·
                      refine ⟨603584185824548178444091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804778914432730904592121 603584185824548178444091)
                      ·
                        rfl

theorem cell23_1175476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1175476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175476 prefixEnd_1175476 := by exact prefixLift 1175476
  have htrace : WordTrace (prefixWord ++ tailWord_1175476) baseStart_1175476 baseEnd_1175476 := by
    simpa [prefixWord, tailWord_1175476, baseEnd_1175476] using wordTrace_append hprefix tailTrace_1175476
  have hstable : (prefixWord ++ tailWord_1175476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175476).length < 2 ^ (prefixWord ++ tailWord_1175476).sum := by decide
  have hdescent : baseEnd_1175476 < baseStart_1175476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175498 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1175498 : Nat := 118140960795 + 1175498 * 2 ^ 59
def prefixEnd_1175498 : Nat := 4983230072969 + 3 ^ 40 * 1175498 * 2
def baseEnd_1175498 : Nat := 603595482398947092368989

theorem tailTrace_1175498 : CollatzResearch.WordTrace tailWord_1175498 prefixEnd_1175498 603595482398947092368989 := by
  unfold tailWord_1175498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718483573844744980065787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28582622863585986613508765 10718483573844744980065787)
  ·
    refine ⟨16077725360767117470098681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718483573844744980065787 16077725360767117470098681)
    ·
      refine ⟨12058294020575338102574011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16077725360767117470098681 12058294020575338102574011)
      ·
        refine ⟨18087441030863007153861017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058294020575338102574011 18087441030863007153861017)
        ·
          refine ⟨13565580773147255365395763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18087441030863007153861017 13565580773147255365395763)
          ·
            refine ⟨20348371159720883048093645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13565580773147255365395763 20348371159720883048093645)
            ·
              refine ⟨7630639184895331143035117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20348371159720883048093645 7630639184895331143035117)
              ·
                refine ⟨2861489694335749178638169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7630639184895331143035117 2861489694335749178638169)
                ·
                  refine ⟨2146117270751811883978627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861489694335749178638169 2146117270751811883978627)
                  ·
                    refine ⟨3219175906127717825967941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146117270751811883978627 3219175906127717825967941)
                    ·
                      refine ⟨603595482398947092368989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3219175906127717825967941 603595482398947092368989)
                      ·
                        rfl

theorem cell23_1175498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1175498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175498 prefixEnd_1175498 := by exact prefixLift 1175498
  have htrace : WordTrace (prefixWord ++ tailWord_1175498) baseStart_1175498 baseEnd_1175498 := by
    simpa [prefixWord, tailWord_1175498, baseEnd_1175498] using wordTrace_append hprefix tailTrace_1175498
  have hstable : (prefixWord ++ tailWord_1175498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175498).length < 2 ^ (prefixWord ++ tailWord_1175498).sum := by decide
  have hdescent : baseEnd_1175498 < baseStart_1175498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175511 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1175511 : Nat := 118140960795 + 1175511 * 2 ^ 59
def prefixEnd_1175511 : Nat := 4983230072969 + 3 ^ 40 * 1175511 * 2
def baseEnd_1175511 : Nat := 603602157647455541506429

theorem tailTrace_1175511 : CollatzResearch.WordTrace tailWord_1175511 prefixEnd_1175511 603602157647455541506429 := by
  unfold tailWord_1175511
  simp only [CollatzResearch.WordTrace]
  refine ⟨42874408444331883140486387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28582938962887922093657591 42874408444331883140486387)
  ·
    refine ⟨64311612666497824710729581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42874408444331883140486387 64311612666497824710729581)
    ·
      refine ⟨24116854749936684266523593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64311612666497824710729581 24116854749936684266523593)
      ·
        refine ⟨18087641062452513199892695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24116854749936684266523593 18087641062452513199892695)
        ·
          refine ⟨27131461593678769799839043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087641062452513199892695 27131461593678769799839043)
          ·
            refine ⟨40697192390518154699758565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27131461593678769799839043 40697192390518154699758565)
            ·
              refine ⟨7630723573222154006204731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40697192390518154699758565 7630723573222154006204731)
              ·
                refine ⟨11446085359833231009307097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630723573222154006204731 11446085359833231009307097)
                ·
                  refine ⟨8584564019874923256980323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11446085359833231009307097 8584564019874923256980323)
                  ·
                    refine ⟨12876846029812384885470485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8584564019874923256980323 12876846029812384885470485)
                    ·
                      refine ⟨603602157647455541506429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12876846029812384885470485 603602157647455541506429)
                      ·
                        rfl

theorem cell23_1175511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1175511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175511 prefixEnd_1175511 := by exact prefixLift 1175511
  have htrace : WordTrace (prefixWord ++ tailWord_1175511) baseStart_1175511 baseEnd_1175511 := by
    simpa [prefixWord, tailWord_1175511, baseEnd_1175511] using wordTrace_append hprefix tailTrace_1175511
  have hstable : (prefixWord ++ tailWord_1175511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175511).length < 2 ^ (prefixWord ++ tailWord_1175511).sum := by decide
  have hdescent : baseEnd_1175511 < baseStart_1175511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175521 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 8]
def baseStart_1175521 : Nat := 118140960795 + 1175521 * 2 ^ 59
def prefixEnd_1175521 : Nat := 4983230072969 + 3 ^ 40 * 1175521 * 2
def baseEnd_1175521 : Nat := 67067476939333389153487

theorem tailTrace_1175521 : CollatzResearch.WordTrace tailWord_1175521 prefixEnd_1175521 67067476939333389153487 := by
  unfold tailWord_1175521
  simp only [CollatzResearch.WordTrace]
  refine ⟨42874773174295654848350417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28583182116197103232233611 42874773174295654848350417)
  ·
    refine ⟨32156079880721741136262813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42874773174295654848350417 32156079880721741136262813)
    ·
      refine ⟨12058529955270652926098555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32156079880721741136262813 12058529955270652926098555)
      ·
        refine ⟨18087794932905979389147833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058529955270652926098555 18087794932905979389147833)
        ·
          refine ⟨13565846199679484541860875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18087794932905979389147833 13565846199679484541860875)
          ·
            refine ⟨20348769299519226812791313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13565846199679484541860875 20348769299519226812791313)
            ·
              refine ⟨15261576974639420109593485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20348769299519226812791313 15261576974639420109593485)
              ·
                refine ⟨5723091365489782541097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15261576974639420109593485 5723091365489782541097557)
                ·
                  refine ⟨67067476939333389153487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5723091365489782541097557 67067476939333389153487)
                  ·
                    rfl

theorem cell23_1175521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 8].length) (baseStart_1175521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175521 prefixEnd_1175521 := by exact prefixLift 1175521
  have htrace : WordTrace (prefixWord ++ tailWord_1175521) baseStart_1175521 baseEnd_1175521 := by
    simpa [prefixWord, tailWord_1175521, baseEnd_1175521] using wordTrace_append hprefix tailTrace_1175521
  have hstable : (prefixWord ++ tailWord_1175521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175521).length < 2 ^ (prefixWord ++ tailWord_1175521).sum := by decide
  have hdescent : baseEnd_1175521 < baseStart_1175521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175542 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1175542 : Nat := 118140960795 + 1175542 * 2 ^ 59
def prefixEnd_1175542 : Nat := 4983230072969 + 3 ^ 40 * 1175542 * 2
def baseEnd_1175542 : Nat := 201206025182581640072929

theorem tailTrace_1175542 : CollatzResearch.WordTrace tailWord_1175542 prefixEnd_1175542 201206025182581640072929 := by
  unfold tailWord_1175542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679721194201223464679055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28583692738146383623243253 2679721194201223464679055)
  ·
    refine ⟨4019581791301835197018583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679721194201223464679055 4019581791301835197018583)
    ·
      refine ⟨6029372686952752795527875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019581791301835197018583 6029372686952752795527875)
      ·
        refine ⟨9044059030429129193291813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029372686952752795527875 9044059030429129193291813)
        ·
          refine ⟨1695761068205461723742215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9044059030429129193291813 1695761068205461723742215)
          ·
            refine ⟨2543641602308192585613323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695761068205461723742215 2543641602308192585613323)
            ·
              refine ⟨3815462403462288878419985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543641602308192585613323 3815462403462288878419985)
              ·
                refine ⟨2861596802596716658814989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815462403462288878419985 2861596802596716658814989)
                ·
                  refine ⟨1073098800973768747055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2861596802596716658814989 1073098800973768747055621)
                  ·
                    refine ⟨201206025182581640072929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073098800973768747055621 201206025182581640072929)
                    ·
                      rfl

theorem cell23_1175542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1175542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175542 prefixEnd_1175542 := by exact prefixLift 1175542
  have htrace : WordTrace (prefixWord ++ tailWord_1175542) baseStart_1175542 baseEnd_1175542 := by
    simpa [prefixWord, tailWord_1175542, baseEnd_1175542] using wordTrace_append hprefix tailTrace_1175542
  have hstable : (prefixWord ++ tailWord_1175542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175542).length < 2 ^ (prefixWord ++ tailWord_1175542).sum := by decide
  have hdescent : baseEnd_1175542 < baseStart_1175542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175561 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_1175561 : Nat := 118140960795 + 1175561 * 2 ^ 59
def prefixEnd_1175561 : Nat := 4983230072969 + 3 ^ 40 * 1175561 * 2
def baseEnd_1175561 : Nat := 603627831680180345881199

theorem tailTrace_1175561 : CollatzResearch.WordTrace tailWord_1175561 prefixEnd_1175561 603627831680180345881199 := by
  unfold tailWord_1175561
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876232094150741679806537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28584154729433827786537691 42876232094150741679806537)
  ·
    refine ⟨32157174070613056259854903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42876232094150741679806537 32157174070613056259854903)
    ·
      refine ⟨48235761105919584389782355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32157174070613056259854903 48235761105919584389782355)
      ·
        refine ⟨72353641658879376584673533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48235761105919584389782355 72353641658879376584673533)
        ·
          refine ⟨27132615622079766219252575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72353641658879376584673533 27132615622079766219252575)
          ·
            refine ⟨40698923433119649328878863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27132615622079766219252575 40698923433119649328878863)
            ·
              refine ⟨61048385149679473993318295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40698923433119649328878863 61048385149679473993318295)
              ·
                refine ⟨91572577724519210989977443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61048385149679473993318295 91572577724519210989977443)
                ·
                  refine ⟨137358866586778816484966165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91572577724519210989977443 137358866586778816484966165)
                  ·
                    refine ⟨6438696871255257022732789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137358866586778816484966165 6438696871255257022732789)
                    ·
                      refine ⟨603627831680180345881199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6438696871255257022732789 603627831680180345881199)
                      ·
                        rfl

theorem cell23_1175561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_1175561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175561 prefixEnd_1175561 := by exact prefixLift 1175561
  have htrace : WordTrace (prefixWord ++ tailWord_1175561) baseStart_1175561 baseEnd_1175561 := by
    simpa [prefixWord, tailWord_1175561, baseEnd_1175561] using wordTrace_append hprefix tailTrace_1175561
  have hstable : (prefixWord ++ tailWord_1175561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175561).length < 2 ^ (prefixWord ++ tailWord_1175561).sum := by decide
  have hdescent : baseEnd_1175561 < baseStart_1175561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175568 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_1175568 : Nat := 118140960795 + 1175568 * 2 ^ 59
def prefixEnd_1175568 : Nat := 4983230072969 + 3 ^ 40 * 1175568 * 2
def baseEnd_1175568 : Nat := 201210475348253939497889

theorem tailTrace_1175568 : CollatzResearch.WordTrace tailWord_1175568 prefixEnd_1175568 201210475348253939497889 := by
  unfold tailWord_1175568
  simp only [CollatzResearch.WordTrace]
  refine ⟨21438243702562690937655679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28584324936750254583540905 21438243702562690937655679)
  ·
    refine ⟨32157365553844036406483519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21438243702562690937655679 32157365553844036406483519)
    ·
      refine ⟨48236048330766054609725279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32157365553844036406483519 48236048330766054609725279)
      ·
        refine ⟨72354072496149081914587919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48236048330766054609725279 72354072496149081914587919)
        ·
          refine ⟨108531108744223622871881879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72354072496149081914587919 108531108744223622871881879)
          ·
            refine ⟨162796663116335434307822819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108531108744223622871881879 162796663116335434307822819)
            ·
              refine ⟨244194994674503151461734229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162796663116335434307822819 244194994674503151461734229)
              ·
                refine ⟨1430830046920916903096099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 244194994674503151461734229 1430830046920916903096099)
                ·
                  refine ⟨2146245070381375354644149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430830046920916903096099 2146245070381375354644149)
                  ·
                    refine ⟨201210475348253939497889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2146245070381375354644149 201210475348253939497889)
                    ·
                      rfl

theorem cell23_1175568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_1175568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175568 prefixEnd_1175568 := by exact prefixLift 1175568
  have htrace : WordTrace (prefixWord ++ tailWord_1175568) baseStart_1175568 baseEnd_1175568 := by
    simpa [prefixWord, tailWord_1175568, baseEnd_1175568] using wordTrace_append hprefix tailTrace_1175568
  have hstable : (prefixWord ++ tailWord_1175568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175568).length < 2 ^ (prefixWord ++ tailWord_1175568).sum := by decide
  have hdescent : baseEnd_1175568 < baseStart_1175568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175572 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1175572 : Nat := 118140960795 + 1175572 * 2 ^ 59
def prefixEnd_1175572 : Nat := 4983230072969 + 3 ^ 40 * 1175572 * 2
def baseEnd_1175572 : Nat := 67070386663042200315961

theorem tailTrace_1175572 : CollatzResearch.WordTrace tailWord_1175572 prefixEnd_1175572 67070386663042200315961 := by
  unfold tailWord_1175572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21438316648555445279228485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28584422198073927038971313 21438316648555445279228485)
  ·
    refine ⟨4019684371604145989855341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21438316648555445279228485 4019684371604145989855341)
    ·
      refine ⟨1507381639351554746195753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4019684371604145989855341 1507381639351554746195753)
      ·
        refine ⟨1130536229513666059646815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1507381639351554746195753 1130536229513666059646815)
        ·
          refine ⟨1695804344270499089470223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130536229513666059646815 1695804344270499089470223)
          ·
            refine ⟨2543706516405748634205335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695804344270499089470223 2543706516405748634205335)
            ·
              refine ⟨3815559774608622951308003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543706516405748634205335 3815559774608622951308003)
              ·
                refine ⟨5723339661912934426962005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815559774608622951308003 5723339661912934426962005)
                ·
                  refine ⟨67070386663042200315961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5723339661912934426962005 67070386663042200315961)
                  ·
                    rfl

theorem cell23_1175572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1175572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175572 prefixEnd_1175572 := by exact prefixLift 1175572
  have htrace : WordTrace (prefixWord ++ tailWord_1175572) baseStart_1175572 baseEnd_1175572 := by
    simpa [prefixWord, tailWord_1175572, baseEnd_1175572] using wordTrace_append hprefix tailTrace_1175572
  have hstable : (prefixWord ++ tailWord_1175572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175572).length < 2 ^ (prefixWord ++ tailWord_1175572).sum := by decide
  have hdescent : baseEnd_1175572 < baseStart_1175572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175605 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1175605 : Nat := 118140960795 + 1175605 * 2 ^ 59
def prefixEnd_1175605 : Nat := 4983230072969 + 3 ^ 40 * 1175605 * 2
def baseEnd_1175605 : Nat := 603650424828978173730997

theorem tailTrace_1175605 : CollatzResearch.WordTrace tailWord_1175605 prefixEnd_1175605 603650424828978173730997 := by
  unfold tailWord_1175605
  simp only [CollatzResearch.WordTrace]
  refine ⟨42877836905991337194408269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28585224603994224796272179 42877836905991337194408269)
  ·
    refine ⟨16079188839746751447903101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42877836905991337194408269 16079188839746751447903101)
    ·
      refine ⟨6029695814905031792963663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16079188839746751447903101 6029695814905031792963663)
      ·
        refine ⟨9044543722357547689445495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029695814905031792963663 9044543722357547689445495)
        ·
          refine ⟨13566815583536321534168243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044543722357547689445495 13566815583536321534168243)
          ·
            refine ⟨20350223375304482301252365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13566815583536321534168243 20350223375304482301252365)
            ·
              refine ⟨7631333765739180862969637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20350223375304482301252365 7631333765739180862969637)
              ·
                refine ⟨1430875081076096411806807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7631333765739180862969637 1430875081076096411806807)
                ·
                  refine ⟨2146312621614144617710211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430875081076096411806807 2146312621614144617710211)
                  ·
                    refine ⟨3219468932421216926565317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146312621614144617710211 3219468932421216926565317)
                    ·
                      refine ⟨603650424828978173730997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3219468932421216926565317 603650424828978173730997)
                      ·
                        rfl

theorem cell23_1175605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1175605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175605 prefixEnd_1175605 := by exact prefixLift 1175605
  have htrace : WordTrace (prefixWord ++ tailWord_1175605) baseStart_1175605 baseEnd_1175605 := by
    simpa [prefixWord, tailWord_1175605, baseEnd_1175605] using wordTrace_append hprefix tailTrace_1175605
  have hstable : (prefixWord ++ tailWord_1175605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175605).length < 2 ^ (prefixWord ++ tailWord_1175605).sum := by decide
  have hdescent : baseEnd_1175605 < baseStart_1175605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175611 : List Nat := [1, 1, 1, 1, 1, 2, 1, 15]
def baseStart_1175611 : Nat := 118140960795 + 1175611 * 2 ^ 59
def prefixEnd_1175611 : Nat := 4983230072969 + 3 ^ 40 * 1175611 * 2
def baseEnd_1175611 : Nat := 22357537248626116676147

theorem tailTrace_1175611 : CollatzResearch.WordTrace tailWord_1175611 prefixEnd_1175611 22357537248626116676147 := by
  unfold tailWord_1175611
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878055743969600219126687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28585370495979733479417791 42878055743969600219126687)
  ·
    refine ⟨64317083615954400328690031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42878055743969600219126687 64317083615954400328690031)
    ·
      refine ⟨96475625423931600493035047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64317083615954400328690031 96475625423931600493035047)
      ·
        refine ⟨144713438135897400739552571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96475625423931600493035047 144713438135897400739552571)
        ·
          refine ⟨217070157203846101109328857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144713438135897400739552571 217070157203846101109328857)
          ·
            refine ⟨162802617902884575831996643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217070157203846101109328857 162802617902884575831996643)
            ·
              refine ⟨244203926854326863747994965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162802617902884575831996643 244203926854326863747994965)
              ·
                refine ⟨22357537248626116676147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 244203926854326863747994965 22357537248626116676147)
                ·
                  rfl

theorem cell23_1175611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 15].length) (baseStart_1175611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175611 prefixEnd_1175611 := by exact prefixLift 1175611
  have htrace : WordTrace (prefixWord ++ tailWord_1175611) baseStart_1175611 baseEnd_1175611 := by
    simpa [prefixWord, tailWord_1175611, baseEnd_1175611] using wordTrace_append hprefix tailTrace_1175611
  have hstable : (prefixWord ++ tailWord_1175611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175611).length < 2 ^ (prefixWord ++ tailWord_1175611).sum := by decide
  have hdescent : baseEnd_1175611 < baseStart_1175611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175625 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 3]
def baseStart_1175625 : Nat := 118140960795 + 1175625 * 2 ^ 59
def prefixEnd_1175625 : Nat := 4983230072969 + 3 ^ 40 * 1175625 * 2
def baseEnd_1175625 : Nat := 603660694442068095480905

theorem tailTrace_1175625 : CollatzResearch.WordTrace tailWord_1175625 prefixEnd_1175625 603660694442068095480905 := by
  unfold tailWord_1175625
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878566365918880610136329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28585710910612587073424219 42878566365918880610136329)
  ·
    refine ⟨32158924774439160457602247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42878566365918880610136329 32158924774439160457602247)
    ·
      refine ⟨48238387161658740686403371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32158924774439160457602247 48238387161658740686403371)
      ·
        refine ⟨72357580742488111029605057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48238387161658740686403371 72357580742488111029605057)
        ·
          refine ⟨54268185556866083272203793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72357580742488111029605057 54268185556866083272203793)
          ·
            refine ⟨40701139167649562454152845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54268185556866083272203793 40701139167649562454152845)
            ·
              refine ⟨15262927187868585920307317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40701139167649562454152845 15262927187868585920307317)
              ·
                refine ⟨1430899423862679930028811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15262927187868585920307317 1430899423862679930028811)
                ·
                  refine ⟨2146349135794019895043217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430899423862679930028811 2146349135794019895043217)
                  ·
                    refine ⟨1609761851845514921282413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146349135794019895043217 1609761851845514921282413)
                    ·
                      refine ⟨603660694442068095480905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609761851845514921282413 603660694442068095480905)
                      ·
                        rfl

theorem cell23_1175625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_1175625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175625 prefixEnd_1175625 := by exact prefixLift 1175625
  have htrace : WordTrace (prefixWord ++ tailWord_1175625) baseStart_1175625 baseEnd_1175625 := by
    simpa [prefixWord, tailWord_1175625, baseEnd_1175625] using wordTrace_append hprefix tailTrace_1175625
  have hstable : (prefixWord ++ tailWord_1175625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175625).length < 2 ^ (prefixWord ++ tailWord_1175625).sum := by decide
  have hdescent : baseEnd_1175625 < baseStart_1175625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175639 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_1175639 : Nat := 118140960795 + 1175639 * 2 ^ 59
def prefixEnd_1175639 : Nat := 4983230072969 + 3 ^ 40 * 1175639 * 2
def baseEnd_1175639 : Nat := 603667883171231040705841

theorem tailTrace_1175639 : CollatzResearch.WordTrace tailWord_1175639 prefixEnd_1175639 603667883171231040705841 := by
  unfold tailWord_1175639
  simp only [CollatzResearch.WordTrace]
  refine ⟨42879076987868161001145971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28586051325245440667430647 42879076987868161001145971)
  ·
    refine ⟨64318615481802241501718957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42879076987868161001145971 64318615481802241501718957)
    ·
      refine ⟨24119480805675840563144609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64318615481802241501718957 24119480805675840563144609)
      ·
        refine ⟨18089610604256880422358457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24119480805675840563144609 18089610604256880422358457)
        ·
          refine ⟨13567207953192660316768843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18089610604256880422358457 13567207953192660316768843)
          ·
            refine ⟨20350811929788990475153265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13567207953192660316768843 20350811929788990475153265)
            ·
              refine ⟨15263108947341742856364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20350811929788990475153265 15263108947341742856364949)
              ·
                refine ⟨715458231906644196392107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15263108947341742856364949 715458231906644196392107)
                ·
                  refine ⟨1073187347859966294588161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715458231906644196392107 1073187347859966294588161)
                  ·
                    refine ⟨804890510894974720941121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073187347859966294588161 804890510894974720941121)
                    ·
                      refine ⟨603667883171231040705841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804890510894974720941121 603667883171231040705841)
                      ·
                        rfl

theorem cell23_1175639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_1175639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175639 prefixEnd_1175639 := by exact prefixLift 1175639
  have htrace : WordTrace (prefixWord ++ tailWord_1175639) baseStart_1175639 baseEnd_1175639 := by
    simpa [prefixWord, tailWord_1175639, baseEnd_1175639] using wordTrace_append hprefix tailTrace_1175639
  have hstable : (prefixWord ++ tailWord_1175639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175639).length < 2 ^ (prefixWord ++ tailWord_1175639).sum := by decide
  have hdescent : baseEnd_1175639 < baseStart_1175639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175645 : List Nat := [1, 4, 4, 1, 1, 1, 1, 10]
def baseStart_1175645 : Nat := 118140960795 + 1175645 * 2 ^ 59
def prefixEnd_1175645 : Nat := 4983230072969 + 3 ^ 40 * 1175645 * 2
def baseEnd_1175645 : Nat := 22358183853894741378919

theorem tailTrace_1175645 : CollatzResearch.WordTrace tailWord_1175645 prefixEnd_1175645 22358183853894741378919 := by
  unfold tailWord_1175645
  simp only [CollatzResearch.WordTrace]
  refine ⟨42879295825846424025864389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28586197217230949350576259 42879295825846424025864389)
  ·
    refine ⟨8039867967346204504849573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42879295825846424025864389 8039867967346204504849573)
    ·
      refine ⟨1507475243877413344659295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8039867967346204504849573 1507475243877413344659295)
      ·
        refine ⟨2261212865816120016988943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507475243877413344659295 2261212865816120016988943)
        ·
          refine ⟨3391819298724180025483415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261212865816120016988943 3391819298724180025483415)
          ·
            refine ⟨5087728948086270038225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3391819298724180025483415 5087728948086270038225123)
            ·
              refine ⟨7631593422129405057337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5087728948086270038225123 7631593422129405057337685)
              ·
                refine ⟨22358183853894741378919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7631593422129405057337685 22358183853894741378919)
                ·
                  rfl

theorem cell23_1175645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 10].length) (baseStart_1175645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175645 prefixEnd_1175645 := by exact prefixLift 1175645
  have htrace : WordTrace (prefixWord ++ tailWord_1175645) baseStart_1175645 baseEnd_1175645 := by
    simpa [prefixWord, tailWord_1175645, baseEnd_1175645] using wordTrace_append hprefix tailTrace_1175645
  have hstable : (prefixWord ++ tailWord_1175645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175645).length < 2 ^ (prefixWord ++ tailWord_1175645).sum := by decide
  have hdescent : baseEnd_1175645 < baseStart_1175645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175655 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1175655 : Nat := 118140960795 + 1175655 * 2 ^ 59
def prefixEnd_1175655 : Nat := 4983230072969 + 3 ^ 40 * 1175655 * 2
def baseEnd_1175655 : Nat := 603676098861702978105767

theorem tailTrace_1175655 : CollatzResearch.WordTrace tailWord_1175655 prefixEnd_1175655 603676098861702978105767 := by
  unfold tailWord_1175655
  simp only [CollatzResearch.WordTrace]
  refine ⟨42879660555810195733728419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28586440370540130489152279 42879660555810195733728419)
  ·
    refine ⟨64319490833715293600592629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42879660555810195733728419 64319490833715293600592629)
    ·
      refine ⟨6029952265660808775055559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64319490833715293600592629 6029952265660808775055559)
      ·
        refine ⟨9044928398491213162583339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029952265660808775055559 9044928398491213162583339)
        ·
          refine ⟨13567392597736819743875009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9044928398491213162583339 13567392597736819743875009)
          ·
            refine ⟨10175544448302614807906257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13567392597736819743875009 10175544448302614807906257)
            ·
              refine ⟨7631658336226961105929693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10175544448302614807906257 7631658336226961105929693)
              ·
                refine ⟨2861871876085110414723635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7631658336226961105929693 2861871876085110414723635)
                ·
                  refine ⟨4292807814127665622085453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861871876085110414723635 4292807814127665622085453)
                  ·
                    refine ⟨1609802930297874608282045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4292807814127665622085453 1609802930297874608282045)
                    ·
                      refine ⟨603676098861702978105767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609802930297874608282045 603676098861702978105767)
                      ·
                        rfl

theorem cell23_1175655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1175655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175655 prefixEnd_1175655 := by exact prefixLift 1175655
  have htrace : WordTrace (prefixWord ++ tailWord_1175655) baseStart_1175655 baseEnd_1175655 := by
    simpa [prefixWord, tailWord_1175655, baseEnd_1175655] using wordTrace_append hprefix tailTrace_1175655
  have hstable : (prefixWord ++ tailWord_1175655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175655).length < 2 ^ (prefixWord ++ tailWord_1175655).sum := by decide
  have hdescent : baseEnd_1175655 < baseStart_1175655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175712 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2]
def baseStart_1175712 : Nat := 118140960795 + 1175712 * 2 ^ 59
def prefixEnd_1175712 : Nat := 4983230072969 + 3 ^ 40 * 1175712 * 2
def baseEnd_1175712 : Nat := 603705367259009255093005

theorem tailTrace_1175712 : CollatzResearch.WordTrace tailWord_1175712 prefixEnd_1175712 603705367259009255093005 := by
  unfold tailWord_1175712
  simp only [CollatzResearch.WordTrace]
  refine ⟨21440869758301847234276695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28587826344402462979035593 21440869758301847234276695)
  ·
    refine ⟨32161304637452770851415043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21440869758301847234276695 32161304637452770851415043)
    ·
      refine ⟨48241956956179156277122565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32161304637452770851415043 48241956956179156277122565)
      ·
        refine ⟨9045366929283591801960481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48241956956179156277122565 9045366929283591801960481)
        ·
          refine ⟨6784025196962693851470361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9045366929283591801960481 6784025196962693851470361)
          ·
            refine ⟨5088018897722020388602771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6784025196962693851470361 5088018897722020388602771)
            ·
              refine ⟨7632028346583030582904157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088018897722020388602771 7632028346583030582904157)
              ·
                refine ⟨2862010629968636468589059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7632028346583030582904157 2862010629968636468589059)
                ·
                  refine ⟨4293015944952954702883589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862010629968636468589059 4293015944952954702883589)
                  ·
                    refine ⟨804940489678679006790673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293015944952954702883589 804940489678679006790673)
                    ·
                      refine ⟨603705367259009255093005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 804940489678679006790673 603705367259009255093005)
                      ·
                        rfl

theorem cell23_1175712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_1175712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175712 prefixEnd_1175712 := by exact prefixLift 1175712
  have htrace : WordTrace (prefixWord ++ tailWord_1175712) baseStart_1175712 baseEnd_1175712 := by
    simpa [prefixWord, tailWord_1175712, baseEnd_1175712] using wordTrace_append hprefix tailTrace_1175712
  have hstable : (prefixWord ++ tailWord_1175712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175712).length < 2 ^ (prefixWord ++ tailWord_1175712).sum := by decide
  have hdescent : baseEnd_1175712 < baseStart_1175712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175762 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1175762 : Nat := 118140960795 + 1175762 * 2 ^ 59
def prefixEnd_1175762 : Nat := 4983230072969 + 3 ^ 40 * 1175762 * 2
def baseEnd_1175762 : Nat := 603731041291734059467775

theorem tailTrace_1175762 : CollatzResearch.WordTrace tailWord_1175762 prefixEnd_1175762 603731041291734059467775 := by
  unfold tailWord_1175762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10720890791605638251968385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28589042110948368671915693 10720890791605638251968385)
  ·
    refine ⟨8040668093704228688976289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10720890791605638251968385 8040668093704228688976289)
    ·
      refine ⟨6030501070278171516732217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8040668093704228688976289 6030501070278171516732217)
      ·
        refine ⟨4522875802708628637549163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6030501070278171516732217 4522875802708628637549163)
        ·
          refine ⟨6784313704062942956323745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522875802708628637549163 6784313704062942956323745)
          ·
            refine ⟨5088235278047207217242809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6784313704062942956323745 5088235278047207217242809)
            ·
              refine ⟨3816176458535405412932107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088235278047207217242809 3816176458535405412932107)
              ·
                refine ⟨5724264687803108119398161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3816176458535405412932107 5724264687803108119398161)
                ·
                  refine ⟨4293198515852331089548621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5724264687803108119398161 4293198515852331089548621)
                  ·
                    refine ⟨1609949443444624158580733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4293198515852331089548621 1609949443444624158580733)
                    ·
                      refine ⟨603731041291734059467775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1609949443444624158580733 603731041291734059467775)
                      ·
                        rfl

theorem cell23_1175762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1175762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175762 prefixEnd_1175762 := by exact prefixLift 1175762
  have htrace : WordTrace (prefixWord ++ tailWord_1175762) baseStart_1175762 baseEnd_1175762 := by
    simpa [prefixWord, tailWord_1175762, baseEnd_1175762] using wordTrace_append hprefix tailTrace_1175762
  have hstable : (prefixWord ++ tailWord_1175762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175762).length < 2 ^ (prefixWord ++ tailWord_1175762).sum := by decide
  have hdescent : baseEnd_1175762 < baseStart_1175762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175802 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1175802 : Nat := 118140960795 + 1175802 * 2 ^ 59
def prefixEnd_1175802 : Nat := 4983230072969 + 3 ^ 40 * 1175802 * 2
def baseEnd_1175802 : Nat := 603751580517913902967591

theorem tailTrace_1175802 : CollatzResearch.WordTrace tailWord_1175802 prefixEnd_1175802 603751580517913902967591 := by
  unfold tailWord_1175802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10721255521569409959832415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28590014724185093226219773 10721255521569409959832415)
  ·
    refine ⟨16081883282354114939748623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10721255521569409959832415 16081883282354114939748623)
    ·
      refine ⟨24122824923531172409622935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16081883282354114939748623 24122824923531172409622935)
      ·
        refine ⟨36184237385296758614434403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24122824923531172409622935 36184237385296758614434403)
        ·
          refine ⟨54276356077945137921651605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36184237385296758614434403 54276356077945137921651605)
          ·
            refine ⟨2544204191153678340077419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54276356077945137921651605 2544204191153678340077419)
            ·
              refine ⟨3816306286730517510116129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544204191153678340077419 3816306286730517510116129)
              ·
                refine ⟨2862229715047888132587097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816306286730517510116129 2862229715047888132587097)
                ·
                  refine ⟨2146672286285916099440323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862229715047888132587097 2146672286285916099440323)
                  ·
                    refine ⟨3220008429428874149160485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146672286285916099440323 3220008429428874149160485)
                    ·
                      refine ⟨603751580517913902967591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3220008429428874149160485 603751580517913902967591)
                      ·
                        rfl

theorem cell23_1175802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1175802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175802 prefixEnd_1175802 := by exact prefixLift 1175802
  have htrace : WordTrace (prefixWord ++ tailWord_1175802) baseStart_1175802 baseEnd_1175802 := by
    simpa [prefixWord, tailWord_1175802, baseEnd_1175802] using wordTrace_append hprefix tailTrace_1175802
  have hstable : (prefixWord ++ tailWord_1175802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175802).length < 2 ^ (prefixWord ++ tailWord_1175802).sum := by decide
  have hdescent : baseEnd_1175802 < baseStart_1175802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175822 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_1175822 : Nat := 118140960795 + 1175822 * 2 ^ 59
def prefixEnd_1175822 : Nat := 4983230072969 + 3 ^ 40 * 1175822 * 2
def baseEnd_1175822 : Nat := 603761850131003824717499

theorem tailTrace_1175822 : CollatzResearch.WordTrace tailWord_1175822 prefixEnd_1175822 603761850131003824717499 := by
  unfold tailWord_1175822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360718943275647906882215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28590501030803455503371813 5360718943275647906882215)
  ·
    refine ⟨8041078414913471860323323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5360718943275647906882215 8041078414913471860323323)
    ·
      refine ⟨12061617622370207790484985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8041078414913471860323323 12061617622370207790484985)
      ·
        refine ⟨9046213216777655842863739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12061617622370207790484985 9046213216777655842863739)
        ·
          refine ⟨13569319825166483764295609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046213216777655842863739 13569319825166483764295609)
          ·
            refine ⟨10176989868874862823221707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13569319825166483764295609 10176989868874862823221707)
            ·
              refine ⟨15265484803312294234832561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10176989868874862823221707 15265484803312294234832561)
              ·
                refine ⟨11449113602484220676124421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15265484803312294234832561 11449113602484220676124421)
                ·
                  refine ⟨2146708800465791376773329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11449113602484220676124421 2146708800465791376773329)
                  ·
                    refine ⟨1610031600349343532579997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146708800465791376773329 1610031600349343532579997)
                    ·
                      refine ⟨603761850131003824717499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610031600349343532579997 603761850131003824717499)
                      ·
                        rfl

theorem cell23_1175822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_1175822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175822 prefixEnd_1175822 := by exact prefixLift 1175822
  have htrace : WordTrace (prefixWord ++ tailWord_1175822) baseStart_1175822 baseEnd_1175822 := by
    simpa [prefixWord, tailWord_1175822, baseEnd_1175822] using wordTrace_append hprefix tailTrace_1175822
  have hstable : (prefixWord ++ tailWord_1175822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175822).length < 2 ^ (prefixWord ++ tailWord_1175822).sum := by decide
  have hdescent : baseEnd_1175822 < baseStart_1175822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175835 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3]
def baseStart_1175835 : Nat := 118140960795 + 1175835 * 2 ^ 59
def prefixEnd_1175835 : Nat := 4983230072969 + 3 ^ 40 * 1175835 * 2
def baseEnd_1175835 : Nat := 603768525379512273854939

theorem tailTrace_1175835 : CollatzResearch.WordTrace tailWord_1175835 prefixEnd_1175835 603768525379512273854939 := by
  unfold tailWord_1175835
  simp only [CollatzResearch.WordTrace]
  refine ⟨42886225695158086475280959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28590817130105390983520639 42886225695158086475280959)
  ·
    refine ⟨64329338542737129712921439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42886225695158086475280959 64329338542737129712921439)
    ·
      refine ⟨96494007814105694569382159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64329338542737129712921439 96494007814105694569382159)
      ·
        refine ⟨144741011721158541854073239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96494007814105694569382159 144741011721158541854073239)
        ·
          refine ⟨217111517581737812781109859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144741011721158541854073239 217111517581737812781109859)
          ·
            refine ⟨325667276372606719171664789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217111517581737812781109859 325667276372606719171664789)
            ·
              refine ⟨15265653579965939961171787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 325667276372606719171664789 15265653579965939961171787)
              ·
                refine ⟨22898480369948909941757681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15265653579965939961171787 22898480369948909941757681)
                ·
                  refine ⟨17173860277461682456318261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22898480369948909941757681 17173860277461682456318261)
                  ·
                    refine ⟨1610049401012032730279837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17173860277461682456318261 1610049401012032730279837)
                    ·
                      refine ⟨603768525379512273854939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610049401012032730279837 603768525379512273854939)
                      ·
                        rfl

theorem cell23_1175835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 3].length) (baseStart_1175835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175835 prefixEnd_1175835 := by exact prefixLift 1175835
  have htrace : WordTrace (prefixWord ++ tailWord_1175835) baseStart_1175835 baseEnd_1175835 := by
    simpa [prefixWord, tailWord_1175835, baseEnd_1175835] using wordTrace_append hprefix tailTrace_1175835
  have hstable : (prefixWord ++ tailWord_1175835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175835).length < 2 ^ (prefixWord ++ tailWord_1175835).sum := by decide
  have hdescent : baseEnd_1175835 < baseStart_1175835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175839 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1175839 : Nat := 118140960795 + 1175839 * 2 ^ 59
def prefixEnd_1175839 : Nat := 4983230072969 + 3 ^ 40 * 1175839 * 2
def baseEnd_1175839 : Nat := 603770579302130258204921

theorem tailTrace_1175839 : CollatzResearch.WordTrace tailWord_1175839 prefixEnd_1175839 603770579302130258204921 := by
  unfold tailWord_1175839
  simp only [CollatzResearch.WordTrace]
  refine ⟨42886371587143595158426571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28590914391429063438951047 42886371587143595158426571)
  ·
    refine ⟨64329557380715392737639857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42886371587143595158426571 64329557380715392737639857)
    ·
      refine ⟨48247168035536544553229893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64329557380715392737639857 48247168035536544553229893)
      ·
        refine ⟨9046344006663102103730605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48247168035536544553229893 9046344006663102103730605)
        ·
          refine ⟨3392379002498663288898977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9046344006663102103730605 3392379002498663288898977)
          ·
            refine ⟨2544284251873997466674233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392379002498663288898977 2544284251873997466674233)
            ·
              refine ⟨1908213188905498100005675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544284251873997466674233 1908213188905498100005675)
              ·
                refine ⟨2862319783358247150008513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908213188905498100005675 2862319783358247150008513)
                ·
                  refine ⟨2146739837518685362506385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862319783358247150008513 2146739837518685362506385)
                  ·
                    refine ⟨1610054878139014021879789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2146739837518685362506385 1610054878139014021879789)
                    ·
                      refine ⟨603770579302130258204921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610054878139014021879789 603770579302130258204921)
                      ·
                        rfl

theorem cell23_1175839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1175839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175839 prefixEnd_1175839 := by exact prefixLift 1175839
  have htrace : WordTrace (prefixWord ++ tailWord_1175839) baseStart_1175839 baseEnd_1175839 := by
    simpa [prefixWord, tailWord_1175839, baseEnd_1175839] using wordTrace_append hprefix tailTrace_1175839
  have hstable : (prefixWord ++ tailWord_1175839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175839).length < 2 ^ (prefixWord ++ tailWord_1175839).sum := by decide
  have hdescent : baseEnd_1175839 < baseStart_1175839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175905 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1175905 : Nat := 118140960795 + 1175905 * 2 ^ 59
def prefixEnd_1175905 : Nat := 4983230072969 + 3 ^ 40 * 1175905 * 2
def baseEnd_1175905 : Nat := 603804469025326999979617

theorem tailTrace_1175905 : CollatzResearch.WordTrace tailWord_1175905 prefixEnd_1175905 603804469025326999979617 := by
  unfold tailWord_1175905
  simp only [CollatzResearch.WordTrace]
  refine ⟨42888778804904488430329169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28592519203269658953552779 42888778804904488430329169)
  ·
    refine ⟨32166584103678366322746877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42888778804904488430329169 32166584103678366322746877)
    ·
      refine ⟨12062469038879387371030079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32166584103678366322746877 12062469038879387371030079)
      ·
        refine ⟨18093703558319081056545119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12062469038879387371030079 18093703558319081056545119)
        ·
          refine ⟨27140555337478621584817679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18093703558319081056545119 27140555337478621584817679)
          ·
            refine ⟨40710833006217932377226519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27140555337478621584817679 40710833006217932377226519)
            ·
              refine ⟨61066249509326898565839779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40710833006217932377226519 61066249509326898565839779)
              ·
                refine ⟨91599374263990347848759669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61066249509326898565839779 91599374263990347848759669)
                ·
                  refine ⟨8587441337249095110821219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91599374263990347848759669 8587441337249095110821219)
                  ·
                    refine ⟨12881162005873642666231829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8587441337249095110821219 12881162005873642666231829)
                    ·
                      refine ⟨603804469025326999979617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12881162005873642666231829 603804469025326999979617)
                      ·
                        rfl

theorem cell23_1175905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1175905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175905 prefixEnd_1175905 := by exact prefixLift 1175905
  have htrace : WordTrace (prefixWord ++ tailWord_1175905) baseStart_1175905 baseEnd_1175905 := by
    simpa [prefixWord, tailWord_1175905, baseEnd_1175905] using wordTrace_append hprefix tailTrace_1175905
  have hstable : (prefixWord ++ tailWord_1175905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175905).length < 2 ^ (prefixWord ++ tailWord_1175905).sum := by decide
  have hdescent : baseEnd_1175905 < baseStart_1175905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175906 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1175906 : Nat := 118140960795 + 1175906 * 2 ^ 59
def prefixEnd_1175906 : Nat := 4983230072969 + 3 ^ 40 * 1175906 * 2
def baseEnd_1175906 : Nat := 201268327501993832022371

theorem tailTrace_1175906 : CollatzResearch.WordTrace tailWord_1175906 prefixEnd_1175906 201268327501993832022371 := by
  unfold tailWord_1175906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722203819475216400278893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28592543518600577067410381 10722203819475216400278893)
  ·
    refine ⟨4020826432303206150104585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10722203819475216400278893 4020826432303206150104585)
    ·
      refine ⟨3015619824227404612578439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4020826432303206150104585 3015619824227404612578439)
      ·
        refine ⟨4523429736341106918867659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015619824227404612578439 4523429736341106918867659)
        ·
          refine ⟨6785144604511660378301489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523429736341106918867659 6785144604511660378301489)
          ·
            refine ⟨5088858453383745283726117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6785144604511660378301489 5088858453383745283726117)
            ·
              refine ⟨954160960009452240698647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5088858453383745283726117 954160960009452240698647)
              ·
                refine ⟨1431241440014178361047971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954160960009452240698647 1431241440014178361047971)
                ·
                  refine ⟨2146862160021267541571957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431241440014178361047971 2146862160021267541571957)
                  ·
                    refine ⟨201268327501993832022371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2146862160021267541571957 201268327501993832022371)
                    ·
                      rfl

theorem cell23_1175906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1175906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175906 prefixEnd_1175906 := by exact prefixLift 1175906
  have htrace : WordTrace (prefixWord ++ tailWord_1175906) baseStart_1175906 baseEnd_1175906 := by
    simpa [prefixWord, tailWord_1175906, baseEnd_1175906] using wordTrace_append hprefix tailTrace_1175906
  have hstable : (prefixWord ++ tailWord_1175906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175906).length < 2 ^ (prefixWord ++ tailWord_1175906).sum := by decide
  have hdescent : baseEnd_1175906 < baseStart_1175906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175909 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 4]
def baseStart_1175909 : Nat := 118140960795 + 1175909 * 2 ^ 59
def prefixEnd_1175909 : Nat := 4983230072969 + 3 ^ 40 * 1175909 * 2
def baseEnd_1175909 : Nat := 603806522947944984329599

theorem tailTrace_1175909 : CollatzResearch.WordTrace tailWord_1175909 prefixEnd_1175909 603806522947944984329599 := by
  unfold tailWord_1175909
  simp only [CollatzResearch.WordTrace]
  refine ⟨42888924696889997113474781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28592616464593331408983187 42888924696889997113474781)
  ·
    refine ⟨16083346761333748917553043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42888924696889997113474781 16083346761333748917553043)
    ·
      refine ⟨24125020142000623376329565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16083346761333748917553043 24125020142000623376329565)
      ·
        refine ⟨9046882553250233766123587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24125020142000623376329565 9046882553250233766123587)
        ·
          refine ⟨13570323829875350649185381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046882553250233766123587 13570323829875350649185381)
          ·
            refine ⟨2544435718101628246722259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13570323829875350649185381 2544435718101628246722259)
            ·
              refine ⟨3816653577152442370083389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544435718101628246722259 3816653577152442370083389)
              ·
                refine ⟨1431245091432165888781271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3816653577152442370083389 1431245091432165888781271)
                ·
                  refine ⟨2146867637148248833171907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431245091432165888781271 2146867637148248833171907)
                  ·
                    refine ⟨3220301455722373249757861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2146867637148248833171907 3220301455722373249757861)
                    ·
                      refine ⟨603806522947944984329599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3220301455722373249757861 603806522947944984329599)
                      ·
                        rfl

theorem cell23_1175909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_1175909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175909 prefixEnd_1175909 := by exact prefixLift 1175909
  have htrace : WordTrace (prefixWord ++ tailWord_1175909) baseStart_1175909 baseEnd_1175909 := by
    simpa [prefixWord, tailWord_1175909, baseEnd_1175909] using wordTrace_append hprefix tailTrace_1175909
  have hstable : (prefixWord ++ tailWord_1175909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175909).length < 2 ^ (prefixWord ++ tailWord_1175909).sum := by decide
  have hdescent : baseEnd_1175909 < baseStart_1175909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175935 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_1175935 : Nat := 118140960795 + 1175935 * 2 ^ 59
def prefixEnd_1175935 : Nat := 4983230072969 + 3 ^ 40 * 1175935 * 2
def baseEnd_1175935 : Nat := 603819873444961882604479

theorem tailTrace_1175935 : CollatzResearch.WordTrace tailWord_1175935 prefixEnd_1175935 603819873444961882604479 := by
  unfold tailWord_1175935
  simp only [CollatzResearch.WordTrace]
  refine ⟨42889872994795803553921259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28593248663197202369280839 42889872994795803553921259)
  ·
    refine ⟨64334809492193705330881889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42889872994795803553921259 64334809492193705330881889)
    ·
      refine ⟨48251107119145278998161417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64334809492193705330881889 48251107119145278998161417)
      ·
        refine ⟨36188330339358959248621063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48251107119145278998161417 36188330339358959248621063)
        ·
          refine ⟨54282495509038438872931595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36188330339358959248621063 54282495509038438872931595)
          ·
            refine ⟨81423743263557658309397393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54282495509038438872931595 81423743263557658309397393)
            ·
              refine ⟨61067807447668243732048045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81423743263557658309397393 61067807447668243732048045)
              ·
                refine ⟨22900427792875591399518017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61067807447668243732048045 22900427792875591399518017)
                ·
                  refine ⟨17175320844656693549638513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22900427792875591399518017 17175320844656693549638513)
                  ·
                    refine ⟨12881490633492520162228885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17175320844656693549638513 12881490633492520162228885)
                    ·
                      refine ⟨603819873444961882604479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12881490633492520162228885 603819873444961882604479)
                      ·
                        rfl

theorem cell23_1175935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_1175935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175935 prefixEnd_1175935 := by exact prefixLift 1175935
  have htrace : WordTrace (prefixWord ++ tailWord_1175935) baseStart_1175935 baseEnd_1175935 := by
    simpa [prefixWord, tailWord_1175935, baseEnd_1175935] using wordTrace_append hprefix tailTrace_1175935
  have hstable : (prefixWord ++ tailWord_1175935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175935).length < 2 ^ (prefixWord ++ tailWord_1175935).sum := by decide
  have hdescent : baseEnd_1175935 < baseStart_1175935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175959 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_1175959 : Nat := 118140960795 + 1175959 * 2 ^ 59
def prefixEnd_1175959 : Nat := 4983230072969 + 3 ^ 40 * 1175959 * 2
def baseEnd_1175959 : Nat := 603832196980669788704369

theorem tailTrace_1175959 : CollatzResearch.WordTrace tailWord_1175959 prefixEnd_1175959 603832196980669788704369 := by
  unfold tailWord_1175959
  simp only [CollatzResearch.WordTrace]
  refine ⟨42890748346708855652794931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28593832231139237101863287 42890748346708855652794931)
  ·
    refine ⟨64336122520063283479192397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42890748346708855652794931 64336122520063283479192397)
    ·
      refine ⟨24126045945023731304697149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64336122520063283479192397 24126045945023731304697149)
      ·
        refine ⟨9047267229383899239261431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24126045945023731304697149 9047267229383899239261431)
        ·
          refine ⟨13570900844075848858892147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9047267229383899239261431 13570900844075848858892147)
          ·
            refine ⟨20356351266113773288338221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13570900844075848858892147 20356351266113773288338221)
            ·
              refine ⟨7633631724792664983126833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20356351266113773288338221 7633631724792664983126833)
              ·
                refine ⟨5725223793594498737345125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633631724792664983126833 5725223793594498737345125)
                ·
                  refine ⟨1073479461298968513252211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5725223793594498737345125 1073479461298968513252211)
                  ·
                    refine ⟨1610219191948452769878317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073479461298968513252211 1610219191948452769878317)
                    ·
                      refine ⟨603832196980669788704369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610219191948452769878317 603832196980669788704369)
                      ·
                        rfl

theorem cell23_1175959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_1175959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175959 prefixEnd_1175959 := by exact prefixLift 1175959
  have htrace : WordTrace (prefixWord ++ tailWord_1175959) baseStart_1175959 baseEnd_1175959 := by
    simpa [prefixWord, tailWord_1175959, baseEnd_1175959] using wordTrace_append hprefix tailTrace_1175959
  have hstable : (prefixWord ++ tailWord_1175959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175959).length < 2 ^ (prefixWord ++ tailWord_1175959).sum := by decide
  have hdescent : baseEnd_1175959 < baseStart_1175959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175960 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1175960 : Nat := 118140960795 + 1175960 * 2 ^ 59
def prefixEnd_1175960 : Nat := 4983230072969 + 3 ^ 40 * 1175960 * 2
def baseEnd_1175960 : Nat := 603832710461324284791865

theorem tailTrace_1175960 : CollatzResearch.WordTrace tailWord_1175960 prefixEnd_1175960 603832710461324284791865 := by
  unfold tailWord_1175960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445392409852616411790667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28593856546470155215720889 21445392409852616411790667)
  ·
    refine ⟨32168088614778924617686001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21445392409852616411790667 32168088614778924617686001)
    ·
      refine ⟨24126066461084193463264501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32168088614778924617686001 24126066461084193463264501)
      ·
        refine ⟨2261818730726643137181047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24126066461084193463264501 2261818730726643137181047)
        ·
          refine ⟨3392728096089964705771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261818730726643137181047 3392728096089964705771571)
          ·
            refine ⟨5089092144134947058657357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392728096089964705771571 5089092144134947058657357)
            ·
              refine ⟨1908409554050605146996509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5089092144134947058657357 1908409554050605146996509)
              ·
                refine ⟨715653582768976930123691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908409554050605146996509 715653582768976930123691)
                ·
                  refine ⟨1073480374153465395185537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715653582768976930123691 1073480374153465395185537)
                  ·
                    refine ⟨805110280615099046389153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073480374153465395185537 805110280615099046389153)
                    ·
                      refine ⟨603832710461324284791865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805110280615099046389153 603832710461324284791865)
                      ·
                        rfl

theorem cell23_1175960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1175960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175960 prefixEnd_1175960 := by exact prefixLift 1175960
  have htrace : WordTrace (prefixWord ++ tailWord_1175960) baseStart_1175960 baseEnd_1175960 := by
    simpa [prefixWord, tailWord_1175960, baseEnd_1175960] using wordTrace_append hprefix tailTrace_1175960
  have hstable : (prefixWord ++ tailWord_1175960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175960).length < 2 ^ (prefixWord ++ tailWord_1175960).sum := by decide
  have hdescent : baseEnd_1175960 < baseStart_1175960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1175993 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1175993 : Nat := 118140960795 + 1175993 * 2 ^ 59
def prefixEnd_1175993 : Nat := 4983230072969 + 3 ^ 40 * 1175993 * 2
def baseEnd_1175993 : Nat := 603849655322922655679213

theorem tailTrace_1175993 : CollatzResearch.WordTrace tailWord_1175993 prefixEnd_1175993 603849655322922655679213 := by
  unfold tailWord_1175993
  simp only [CollatzResearch.WordTrace]
  refine ⟨42891988428585679459532633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28594658952390452973021755 42891988428585679459532633)
  ·
    refine ⟨32168991321439259594649475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42891988428585679459532633 32168991321439259594649475)
    ·
      refine ⟨48253486982158889391974213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32168991321439259594649475 48253486982158889391974213)
      ·
        refine ⟨9047528809154791760995165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48253486982158889391974213 9047528809154791760995165)
        ·
          refine ⟨3392823303433046910373187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9047528809154791760995165 3392823303433046910373187)
          ·
            refine ⟨5089234955149570365559781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392823303433046910373187 5089234955149570365559781)
            ·
              refine ⟨954231554090544443542459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5089234955149570365559781 954231554090544443542459)
              ·
                refine ⟨1431347331135816665313689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954231554090544443542459 1431347331135816665313689)
                ·
                  refine ⟨1073510498351862498985267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431347331135816665313689 1073510498351862498985267)
                  ·
                    refine ⟨1610265747527793748477901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073510498351862498985267 1610265747527793748477901)
                    ·
                      refine ⟨603849655322922655679213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610265747527793748477901 603849655322922655679213)
                      ·
                        rfl

theorem cell23_1175993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1175993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1175993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1175993 prefixEnd_1175993 := by exact prefixLift 1175993
  have htrace : WordTrace (prefixWord ++ tailWord_1175993) baseStart_1175993 baseEnd_1175993 := by
    simpa [prefixWord, tailWord_1175993, baseEnd_1175993] using wordTrace_append hprefix tailTrace_1175993
  have hstable : (prefixWord ++ tailWord_1175993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1175993).length < 2 ^ (prefixWord ++ tailWord_1175993).sum := by decide
  have hdescent : baseEnd_1175993 < baseStart_1175993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1175993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176020 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1176020 : Nat := 118140960795 + 1176020 * 2 ^ 59
def prefixEnd_1176020 : Nat := 4983230072969 + 3 ^ 40 * 1176020 * 2
def baseEnd_1176020 : Nat := 603863519300594050041589

theorem tailTrace_1176020 : CollatzResearch.WordTrace tailWord_1176020 prefixEnd_1176020 603863519300594050041589 := by
  unfold tailWord_1176020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21446486599743931535382757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28595315466325242047177009 21446486599743931535382757)
  ·
    refine ⟨4021216237451987162884267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21446486599743931535382757 4021216237451987162884267)
    ·
      refine ⟨6031824356177980744326401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4021216237451987162884267 6031824356177980744326401)
      ·
        refine ⟨4523868267133485558244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6031824356177980744326401 4523868267133485558244801)
        ·
          refine ⟨3392901200350114168683601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4523868267133485558244801 3392901200350114168683601)
          ·
            refine ⟨2544675900262585626512701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392901200350114168683601 2544675900262585626512701)
            ·
              refine ⟨954253462598469609942263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2544675900262585626512701 954253462598469609942263)
              ·
                refine ⟨1431380193897704414913395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954253462598469609942263 1431380193897704414913395)
                ·
                  refine ⟨2147070290846556622370093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431380193897704414913395 2147070290846556622370093)
                  ·
                    refine ⟨805151359067458733388785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147070290846556622370093 805151359067458733388785)
                    ·
                      refine ⟨603863519300594050041589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805151359067458733388785 603863519300594050041589)
                      ·
                        rfl

theorem cell23_1176020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1176020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176020 prefixEnd_1176020 := by exact prefixLift 1176020
  have htrace : WordTrace (prefixWord ++ tailWord_1176020) baseStart_1176020 baseEnd_1176020 := by
    simpa [prefixWord, tailWord_1176020, baseEnd_1176020] using wordTrace_append hprefix tailTrace_1176020
  have hstable : (prefixWord ++ tailWord_1176020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176020).length < 2 ^ (prefixWord ++ tailWord_1176020).sum := by decide
  have hdescent : baseEnd_1176020 < baseStart_1176020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176029 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1176029 : Nat := 118140960795 + 1176029 * 2 ^ 59
def prefixEnd_1176029 : Nat := 4983230072969 + 3 ^ 40 * 1176029 * 2
def baseEnd_1176029 : Nat := 603868140626484514829047

theorem tailTrace_1176029 : CollatzResearch.WordTrace tailWord_1176029 prefixEnd_1176029 603868140626484514829047 := by
  unfold tailWord_1176029
  simp only [CollatzResearch.WordTrace]
  refine ⟨42893301456455257607843141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28595534304303505071895427 42893301456455257607843141)
  ·
    refine ⟨8042494023085360801470589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42893301456455257607843141 8042494023085360801470589)
    ·
      refine ⟨3015935258657010300551471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8042494023085360801470589 3015935258657010300551471)
      ·
        refine ⟨4523902887985515450827207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015935258657010300551471 4523902887985515450827207)
        ·
          refine ⟨6785854331978273176240811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4523902887985515450827207 6785854331978273176240811)
          ·
            refine ⟨10178781497967409764361217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785854331978273176240811 10178781497967409764361217)
            ·
              refine ⟨7634086123475557323270913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178781497967409764361217 7634086123475557323270913)
              ·
                refine ⟨5725564592606667992453185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634086123475557323270913 5725564592606667992453185)
                ·
                  refine ⟨4294173444455000994339889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725564592606667992453185 4294173444455000994339889)
                  ·
                    refine ⟨3220630083341250745754917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4294173444455000994339889 3220630083341250745754917)
                    ·
                      refine ⟨603868140626484514829047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3220630083341250745754917 603868140626484514829047)
                      ·
                        rfl

theorem cell23_1176029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1176029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176029 prefixEnd_1176029 := by exact prefixLift 1176029
  have htrace : WordTrace (prefixWord ++ tailWord_1176029) baseStart_1176029 baseEnd_1176029 := by
    simpa [prefixWord, tailWord_1176029, baseEnd_1176029] using wordTrace_append hprefix tailTrace_1176029
  have hstable : (prefixWord ++ tailWord_1176029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176029).length < 2 ^ (prefixWord ++ tailWord_1176029).sum := by decide
  have hdescent : baseEnd_1176029 < baseStart_1176029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176033 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_1176033 : Nat := 118140960795 + 1176033 * 2 ^ 59
def prefixEnd_1176033 : Nat := 4983230072969 + 3 ^ 40 * 1176033 * 2
def baseEnd_1176033 : Nat := 603870194549102499179029

theorem tailTrace_1176033 : CollatzResearch.WordTrace tailWord_1176033 prefixEnd_1176033 603870194549102499179029 := by
  unfold tailWord_1176033
  simp only [CollatzResearch.WordTrace]
  refine ⟨42893447348440766290988753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28595631565627177527325835 42893447348440766290988753)
  ·
    refine ⟨32170085511330574718241565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42893447348440766290988753 32170085511330574718241565)
    ·
      refine ⟨12063782066748965519340587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32170085511330574718241565 12063782066748965519340587)
      ·
        refine ⟨18095673100123448279010881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12063782066748965519340587 18095673100123448279010881)
        ·
          refine ⟨13571754825092586209258161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18095673100123448279010881 13571754825092586209258161)
          ·
            refine ⟨10178816118819439656943621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13571754825092586209258161 10178816118819439656943621)
            ·
              refine ⟨1908528022278644935676929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10178816118819439656943621 1908528022278644935676929)
              ·
                refine ⟨1431396016708983701757697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908528022278644935676929 1431396016708983701757697)
                ·
                  refine ⟨1073547012531737776318273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431396016708983701757697 1073547012531737776318273)
                  ·
                    refine ⟨805160259398803332238705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073547012531737776318273 805160259398803332238705)
                    ·
                      refine ⟨603870194549102499179029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805160259398803332238705 603870194549102499179029)
                      ·
                        rfl

theorem cell23_1176033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_1176033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176033 prefixEnd_1176033 := by exact prefixLift 1176033
  have htrace : WordTrace (prefixWord ++ tailWord_1176033) baseStart_1176033 baseEnd_1176033 := by
    simpa [prefixWord, tailWord_1176033, baseEnd_1176033] using wordTrace_append hprefix tailTrace_1176033
  have hstable : (prefixWord ++ tailWord_1176033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176033).length < 2 ^ (prefixWord ++ tailWord_1176033).sum := by decide
  have hdescent : baseEnd_1176033 < baseStart_1176033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176049 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_1176049 : Nat := 118140960795 + 1176049 * 2 ^ 59
def prefixEnd_1176049 : Nat := 4983230072969 + 3 ^ 40 * 1176049 * 2
def baseEnd_1176049 : Nat := 603878410239574436578955

theorem tailTrace_1176049 : CollatzResearch.WordTrace tailWord_1176049 prefixEnd_1176049 603878410239574436578955 := by
  unfold tailWord_1176049
  simp only [CollatzResearch.WordTrace]
  refine ⟨42894030916382801023571201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28596020610921867349047467 42894030916382801023571201)
  ·
    refine ⟨32170523187287100767678401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42894030916382801023571201 32170523187287100767678401)
    ·
      refine ⟨24127892390465325575758801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32170523187287100767678401 24127892390465325575758801)
      ·
        refine ⟨18095919292848994181819101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24127892390465325575758801 18095919292848994181819101)
        ·
          refine ⟨6785969734818372818182163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18095919292848994181819101 6785969734818372818182163)
          ·
            refine ⟨10178954602227559227273245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785969734818372818182163 10178954602227559227273245)
            ·
              refine ⟨3817107975835334710227467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10178954602227559227273245 3817107975835334710227467)
              ·
                refine ⟨5725661963753002065341201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817107975835334710227467 5725661963753002065341201)
                ·
                  refine ⟨4294246472814751549005901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5725661963753002065341201 4294246472814751549005901)
                  ·
                    refine ⟨1610342427305531830877213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4294246472814751549005901 1610342427305531830877213)
                    ·
                      refine ⟨603878410239574436578955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610342427305531830877213 603878410239574436578955)
                      ·
                        rfl

theorem cell23_1176049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_1176049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176049 prefixEnd_1176049 := by exact prefixLift 1176049
  have htrace : WordTrace (prefixWord ++ tailWord_1176049) baseStart_1176049 baseEnd_1176049 := by
    simpa [prefixWord, tailWord_1176049, baseEnd_1176049] using wordTrace_append hprefix tailTrace_1176049
  have hstable : (prefixWord ++ tailWord_1176049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176049).length < 2 ^ (prefixWord ++ tailWord_1176049).sum := by decide
  have hdescent : baseEnd_1176049 < baseStart_1176049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176069 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_1176069 : Nat := 118140960795 + 1176069 * 2 ^ 59
def prefixEnd_1176069 : Nat := 4983230072969 + 3 ^ 40 * 1176069 * 2
def baseEnd_1176069 : Nat := 201296226617554786109621

theorem tailTrace_1176069 : CollatzResearch.WordTrace tailWord_1176069 prefixEnd_1176069 201296226617554786109621 := by
  unfold tailWord_1176069
  simp only [CollatzResearch.WordTrace]
  refine ⟨42894760376310344439299261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28596506917540229626199507 42894760376310344439299261)
  ·
    refine ⟨16085535141116379164737223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42894760376310344439299261 16085535141116379164737223)
    ·
      refine ⟨24128302711674568747105835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16085535141116379164737223 24128302711674568747105835)
      ·
        refine ⟨36192454067511853120658753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24128302711674568747105835 36192454067511853120658753)
        ·
          refine ⟨27144340550633889840494065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36192454067511853120658753 27144340550633889840494065)
          ·
            refine ⟨20358255412975417380370549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27144340550633889840494065 20358255412975417380370549)
            ·
              refine ⟨1908586444966445379409739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20358255412975417380370549 1908586444966445379409739)
              ·
                refine ⟨2862879667449668069114609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908586444966445379409739 2862879667449668069114609)
                ·
                  refine ⟨2147159750587251051835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862879667449668069114609 2147159750587251051835957)
                  ·
                    refine ⟨201296226617554786109621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2147159750587251051835957 201296226617554786109621)
                    ·
                      rfl

theorem cell23_1176069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_1176069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176069 prefixEnd_1176069 := by exact prefixLift 1176069
  have htrace : WordTrace (prefixWord ++ tailWord_1176069) baseStart_1176069 baseEnd_1176069 := by
    simpa [prefixWord, tailWord_1176069, baseEnd_1176069] using wordTrace_append hprefix tailTrace_1176069
  have hstable : (prefixWord ++ tailWord_1176069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176069).length < 2 ^ (prefixWord ++ tailWord_1176069).sum := by decide
  have hdescent : baseEnd_1176069 < baseStart_1176069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176089 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 6, 2]
def baseStart_1176089 : Nat := 118140960795 + 1176089 * 2 ^ 59
def prefixEnd_1176089 : Nat := 4983230072969 + 3 ^ 40 * 1176089 * 2
def baseEnd_1176089 : Nat := 603898949465754280078771

theorem tailTrace_1176089 : CollatzResearch.WordTrace tailWord_1176089 prefixEnd_1176089 603898949465754280078771 := by
  unfold tailWord_1176089
  simp only [CollatzResearch.WordTrace]
  refine ⟨42895489836237887855027321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28596993224158591903351547 42895489836237887855027321)
  ·
    refine ⟨32171617377178415891270491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42895489836237887855027321 32171617377178415891270491)
    ·
      refine ⟨48257426065767623836905737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32171617377178415891270491 48257426065767623836905737)
      ·
        refine ⟨36193069549325717877679303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48257426065767623836905737 36193069549325717877679303)
        ·
          refine ⟨54289604323988576816518955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36193069549325717877679303 54289604323988576816518955)
          ·
            refine ⟨81434406485982865224778433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54289604323988576816518955 81434406485982865224778433)
            ·
              refine ⟨61075804864487148918583825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81434406485982865224778433 61075804864487148918583825)
              ·
                refine ⟨45806853648365361688937869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61075804864487148918583825 45806853648365361688937869)
                ·
                  refine ⟨17177570118137010633351701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45806853648365361688937869 17177570118137010633351701)
                  ·
                    refine ⟨805198599287672373438361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17177570118137010633351701 805198599287672373438361)
                    ·
                      refine ⟨603898949465754280078771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805198599287672373438361 603898949465754280078771)
                      ·
                        rfl

theorem cell23_1176089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_1176089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176089 prefixEnd_1176089 := by exact prefixLift 1176089
  have htrace : WordTrace (prefixWord ++ tailWord_1176089) baseStart_1176089 baseEnd_1176089 := by
    simpa [prefixWord, tailWord_1176089, baseEnd_1176089] using wordTrace_append hprefix tailTrace_1176089
  have hstable : (prefixWord ++ tailWord_1176089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176089).length < 2 ^ (prefixWord ++ tailWord_1176089).sum := by decide
  have hdescent : baseEnd_1176089 < baseStart_1176089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176129 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 8]
def baseStart_1176129 : Nat := 118140960795 + 1176129 * 2 ^ 59
def prefixEnd_1176129 : Nat := 4983230072969 + 3 ^ 40 * 1176129 * 2
def baseEnd_1176129 : Nat := 67102165410214902619843

theorem tailTrace_1176129 : CollatzResearch.WordTrace tailWord_1176129 prefixEnd_1176129 67102165410214902619843 := by
  unfold tailWord_1176129
  simp only [CollatzResearch.WordTrace]
  refine ⟨42896948756092974686483441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28597965837395316457655627 42896948756092974686483441)
  ·
    refine ⟨32172711567069731014862581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42896948756092974686483441 32172711567069731014862581)
    ·
      refine ⟨3016191709412787282643367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32172711567069731014862581 3016191709412787282643367)
      ·
        refine ⟨4524287564119180923965051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016191709412787282643367 4524287564119180923965051)
        ·
          refine ⟨6786431346178771385947577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524287564119180923965051 6786431346178771385947577)
          ·
            refine ⟨5089823509634078539460683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6786431346178771385947577 5089823509634078539460683)
            ·
              refine ⟨7634735264451117809191025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089823509634078539460683 7634735264451117809191025)
              ·
                refine ⟨5726051448338338356893269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634735264451117809191025 5726051448338338356893269)
                ·
                  refine ⟨67102165410214902619843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5726051448338338356893269 67102165410214902619843)
                  ·
                    rfl

theorem cell23_1176129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_1176129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176129 prefixEnd_1176129 := by exact prefixLift 1176129
  have htrace : WordTrace (prefixWord ++ tailWord_1176129) baseStart_1176129 baseEnd_1176129 := by
    simpa [prefixWord, tailWord_1176129, baseEnd_1176129] using wordTrace_append hprefix tailTrace_1176129
  have hstable : (prefixWord ++ tailWord_1176129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176129).length < 2 ^ (prefixWord ++ tailWord_1176129).sum := by decide
  have hdescent : baseEnd_1176129 < baseStart_1176129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176133 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_1176133 : Nat := 118140960795 + 1176133 * 2 ^ 59
def prefixEnd_1176133 : Nat := 4983230072969 + 3 ^ 40 * 1176133 * 2
def baseEnd_1176133 : Nat := 201307180871517369309523

theorem tailTrace_1176133 : CollatzResearch.WordTrace tailWord_1176133 prefixEnd_1176133 201307180871517369309523 := by
  unfold tailWord_1176133
  simp only [CollatzResearch.WordTrace]
  refine ⟨42897094648078483369629053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28598063098718988913086035 42897094648078483369629053)
  ·
    refine ⟨16086410493029431263610895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42897094648078483369629053 16086410493029431263610895)
    ·
      refine ⟨24129615739544146895416343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086410493029431263610895 24129615739544146895416343)
      ·
        refine ⟨36194423609316220343124515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24129615739544146895416343 36194423609316220343124515)
        ·
          refine ⟨54291635413974330514686773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36194423609316220343124515 54291635413974330514686773)
          ·
            refine ⟨5089840820060093485751885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54291635413974330514686773 5089840820060093485751885)
            ·
              refine ⟨1908690307522535057156957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5089840820060093485751885 1908690307522535057156957)
              ·
                refine ⟨715758865320950646433859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1908690307522535057156957 715758865320950646433859)
                ·
                  refine ⟨1073638297981425969650789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715758865320950646433859 1073638297981425969650789)
                  ·
                    refine ⟨201307180871517369309523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073638297981425969650789 201307180871517369309523)
                    ·
                      rfl

theorem cell23_1176133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_1176133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176133 prefixEnd_1176133 := by exact prefixLift 1176133
  have htrace : WordTrace (prefixWord ++ tailWord_1176133) baseStart_1176133 baseEnd_1176133 := by
    simpa [prefixWord, tailWord_1176133, baseEnd_1176133] using wordTrace_append hprefix tailTrace_1176133
  have hstable : (prefixWord ++ tailWord_1176133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176133).length < 2 ^ (prefixWord ++ tailWord_1176133).sum := by decide
  have hdescent : baseEnd_1176133 < baseStart_1176133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176176 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_1176176 : Nat := 118140960795 + 1176176 * 2 ^ 59
def prefixEnd_1176176 : Nat := 4983230072969 + 3 ^ 40 * 1176176 * 2
def baseEnd_1176176 : Nat := 201314540760898479896957

theorem tailTrace_1176176 : CollatzResearch.WordTrace tailWord_1176176 prefixEnd_1176176 201314540760898479896957 := by
  unfold tailWord_1176176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449331493461350856722191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28599108657948467808962921 21449331493461350856722191)
  ·
    refine ⟨32173997240192026285083287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21449331493461350856722191 32173997240192026285083287)
    ·
      refine ⟨48260995860288039427624931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32173997240192026285083287 48260995860288039427624931)
      ·
        refine ⟨72391493790432059141437397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48260995860288039427624931 72391493790432059141437397)
        ·
          refine ⟨1696675635713251386127439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72391493790432059141437397 1696675635713251386127439)
          ·
            refine ⟨2545013453569877079191159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696675635713251386127439 2545013453569877079191159)
            ·
              refine ⟨3817520180354815618786739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545013453569877079191159 3817520180354815618786739)
              ·
                refine ⟨5726280270532223428180109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817520180354815618786739 5726280270532223428180109)
                ·
                  refine ⟨2147355101449583785567541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5726280270532223428180109 2147355101449583785567541)
                  ·
                    refine ⟨201314540760898479896957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2147355101449583785567541 201314540760898479896957)
                    ·
                      rfl

theorem cell23_1176176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_1176176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176176 prefixEnd_1176176 := by exact prefixLift 1176176
  have htrace : WordTrace (prefixWord ++ tailWord_1176176) baseStart_1176176 baseEnd_1176176 := by
    simpa [prefixWord, tailWord_1176176, baseEnd_1176176] using wordTrace_append hprefix tailTrace_1176176
  have hstable : (prefixWord ++ tailWord_1176176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176176).length < 2 ^ (prefixWord ++ tailWord_1176176).sum := by decide
  have hdescent : baseEnd_1176176 < baseStart_1176176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176193 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1176193 : Nat := 118140960795 + 1176193 * 2 ^ 59
def prefixEnd_1176193 : Nat := 4983230072969 + 3 ^ 40 * 1176193 * 2
def baseEnd_1176193 : Nat := 201317450484607291059431

theorem tailTrace_1176193 : CollatzResearch.WordTrace tailWord_1176193 prefixEnd_1176193 201317450484607291059431 := by
  unfold tailWord_1176193
  simp only [CollatzResearch.WordTrace]
  refine ⟨42899283027861113616813233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28599522018574075744542155 42899283027861113616813233)
  ·
    refine ⟨32174462270895835212609925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42899283027861113616813233 32174462270895835212609925)
    ·
      refine ⟨6032711675792969102364361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32174462270895835212609925 6032711675792969102364361)
      ·
        refine ⟨4524533756844726826773271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032711675792969102364361 4524533756844726826773271)
        ·
          refine ⟨6786800635267090240159907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524533756844726826773271 6786800635267090240159907)
          ·
            refine ⟨10180200952900635360239861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786800635267090240159907 10180200952900635360239861)
            ·
              refine ⟨954393839334434565022487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10180200952900635360239861 954393839334434565022487)
              ·
                refine ⟨1431590759001651847533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954393839334434565022487 1431590759001651847533731)
                ·
                  refine ⟨2147386138502477771300597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431590759001651847533731 2147386138502477771300597)
                  ·
                    refine ⟨201317450484607291059431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2147386138502477771300597 201317450484607291059431)
                    ·
                      rfl

theorem cell23_1176193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1176193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176193 prefixEnd_1176193 := by exact prefixLift 1176193
  have htrace : WordTrace (prefixWord ++ tailWord_1176193) baseStart_1176193 baseEnd_1176193 := by
    simpa [prefixWord, tailWord_1176193, baseEnd_1176193] using wordTrace_append hprefix tailTrace_1176193
  have hstable : (prefixWord ++ tailWord_1176193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176193).length < 2 ^ (prefixWord ++ tailWord_1176193).sum := by decide
  have hdescent : baseEnd_1176193 < baseStart_1176193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176216 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1176216 : Nat := 118140960795 + 1176216 * 2 ^ 59
def prefixEnd_1176216 : Nat := 4983230072969 + 3 ^ 40 * 1176216 * 2
def baseEnd_1176216 : Nat := 603964161508875283190687

theorem tailTrace_1176216 : CollatzResearch.WordTrace tailWord_1176216 prefixEnd_1176216 603964161508875283190687 := by
  unfold tailWord_1176216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450060953388894272450251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28600081271185192363267001 21450060953388894272450251)
  ·
    refine ⟨32175091430083341408675377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21450060953388894272450251 32175091430083341408675377)
    ·
      refine ⟨24131318572562506056506533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32175091430083341408675377 24131318572562506056506533)
      ·
        refine ⟨4524622232355469885594975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24131318572562506056506533 4524622232355469885594975)
        ·
          refine ⟨6786933348533204828392463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524622232355469885594975 6786933348533204828392463)
          ·
            refine ⟨10180400022799807242588695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6786933348533204828392463 10180400022799807242588695)
            ·
              refine ⟨15270600034199710863883043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10180400022799807242588695 15270600034199710863883043)
              ·
                refine ⟨22905900051299566295824565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15270600034199710863883043 22905900051299566295824565)
                ·
                  refine ⟨2147428129809334340233553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22905900051299566295824565 2147428129809334340233553)
                  ·
                    refine ⟨1610571097357000755175165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2147428129809334340233553 1610571097357000755175165)
                    ·
                      refine ⟨603964161508875283190687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610571097357000755175165 603964161508875283190687)
                      ·
                        rfl

theorem cell23_1176216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1176216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176216 prefixEnd_1176216 := by exact prefixLift 1176216
  have htrace : WordTrace (prefixWord ++ tailWord_1176216) baseStart_1176216 baseEnd_1176216 := by
    simpa [prefixWord, tailWord_1176216, baseEnd_1176216] using wordTrace_append hprefix tailTrace_1176216
  have hstable : (prefixWord ++ tailWord_1176216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176216).length < 2 ^ (prefixWord ++ tailWord_1176216).sum := by decide
  have hdescent : baseEnd_1176216 < baseStart_1176216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176234 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1176234 : Nat := 118140960795 + 1176234 * 2 ^ 59
def prefixEnd_1176234 : Nat := 4983230072969 + 3 ^ 40 * 1176234 * 2
def baseEnd_1176234 : Nat := 603973404160656212765605

theorem tailTrace_1176234 : CollatzResearch.WordTrace tailWord_1176234 prefixEnd_1176234 603973404160656212765605 := by
  unfold tailWord_1176234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725194605178144404763939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28600518947141718412703837 10725194605178144404763939)
  ·
    refine ⟨16087791907767216607145909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10725194605178144404763939 16087791907767216607145909)
    ·
      refine ⟨1508230491353176556919929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16087791907767216607145909 1508230491353176556919929)
      ·
        refine ⟨1131172868514882417689947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1508230491353176556919929 1131172868514882417689947)
        ·
          refine ⟨1696759302772323626534921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131172868514882417689947 1696759302772323626534921)
          ·
            refine ⟨1272569477079242719901191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1696759302772323626534921 1272569477079242719901191)
            ·
              refine ⟨1908854215618864079851787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272569477079242719901191 1908854215618864079851787)
              ·
                refine ⟨2863281323428296119777681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908854215618864079851787 2863281323428296119777681)
                ·
                  refine ⟨2147460992571222089833261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863281323428296119777681 2147460992571222089833261)
                  ·
                    refine ⟨805297872214208283687473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147460992571222089833261 805297872214208283687473)
                    ·
                      refine ⟨603973404160656212765605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805297872214208283687473 603973404160656212765605)
                      ·
                        rfl

theorem cell23_1176234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1176234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176234 prefixEnd_1176234 := by exact prefixLift 1176234
  have htrace : WordTrace (prefixWord ++ tailWord_1176234) baseStart_1176234 baseEnd_1176234 := by
    simpa [prefixWord, tailWord_1176234, baseEnd_1176234] using wordTrace_append hprefix tailTrace_1176234
  have hstable : (prefixWord ++ tailWord_1176234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176234).length < 2 ^ (prefixWord ++ tailWord_1176234).sum := by decide
  have hdescent : baseEnd_1176234 < baseStart_1176234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176247 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_1176247 : Nat := 118140960795 + 1176247 * 2 ^ 59
def prefixEnd_1176247 : Nat := 4983230072969 + 3 ^ 40 * 1176247 * 2
def baseEnd_1176247 : Nat := 603980079409164661903045

theorem tailTrace_1176247 : CollatzResearch.WordTrace tailWord_1176247 prefixEnd_1176247 603980079409164661903045 := by
  unfold tailWord_1176247
  simp only [CollatzResearch.WordTrace]
  refine ⟨42901252569665480839278995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28600835046443653892852663 42901252569665480839278995)
  ·
    refine ⟨64351878854498221258918493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42901252569665480839278995 64351878854498221258918493)
    ·
      refine ⟨24131954570436832972094435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64351878854498221258918493 24131954570436832972094435)
      ·
        refine ⟨36197931855655249458141653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24131954570436832972094435 36197931855655249458141653)
        ·
          refine ⟨848389027866919909175195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36197931855655249458141653 848389027866919909175195)
          ·
            refine ⟨1272583541800379863762793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848389027866919909175195 1272583541800379863762793)
            ·
              refine ⟨954437656350284897822095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272583541800379863762793 954437656350284897822095)
              ·
                refine ⟨1431656484525427346733143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954437656350284897822095 1431656484525427346733143)
                ·
                  refine ⟨2147484726788141020099715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431656484525427346733143 2147484726788141020099715)
                  ·
                    refine ⟨3221227090182211530149573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2147484726788141020099715 3221227090182211530149573)
                    ·
                      refine ⟨603980079409164661903045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3221227090182211530149573 603980079409164661903045)
                      ·
                        rfl

theorem cell23_1176247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_1176247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176247 prefixEnd_1176247 := by exact prefixLift 1176247
  have htrace : WordTrace (prefixWord ++ tailWord_1176247) baseStart_1176247 baseEnd_1176247 := by
    simpa [prefixWord, tailWord_1176247, baseEnd_1176247] using wordTrace_append hprefix tailTrace_1176247
  have hstable : (prefixWord ++ tailWord_1176247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176247).length < 2 ^ (prefixWord ++ tailWord_1176247).sum := by decide
  have hdescent : baseEnd_1176247 < baseStart_1176247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176263 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1176263 : Nat := 118140960795 + 1176263 * 2 ^ 59
def prefixEnd_1176263 : Nat := 4983230072969 + 3 ^ 40 * 1176263 * 2
def baseEnd_1176263 : Nat := 603988295099636599302971

theorem tailTrace_1176263 : CollatzResearch.WordTrace tailWord_1176263 prefixEnd_1176263 603988295099636599302971 := by
  unfold tailWord_1176263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42901836137607515571861443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28601224091738343714574295 42901836137607515571861443)
  ·
    refine ⟨64352754206411273357792165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42901836137607515571861443 64352754206411273357792165)
    ·
      refine ⟨12066141413702113754586031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64352754206411273357792165 12066141413702113754586031)
      ·
        refine ⟨18099212120553170631879047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12066141413702113754586031 18099212120553170631879047)
        ·
          refine ⟨27148818180829755947818571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18099212120553170631879047 27148818180829755947818571)
          ·
            refine ⟨40723227271244633921727857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27148818180829755947818571 40723227271244633921727857)
            ·
              refine ⟨30542420453433475441295893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40723227271244633921727857 30542420453433475441295893)
              ·
                refine ⟨1431675958754694161310745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30542420453433475441295893 1431675958754694161310745)
                ·
                  refine ⟨1073756969066020620983059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431675958754694161310745 1073756969066020620983059)
                  ·
                    refine ⟨1610635453599030931474589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073756969066020620983059 1610635453599030931474589)
                    ·
                      refine ⟨603988295099636599302971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610635453599030931474589 603988295099636599302971)
                      ·
                        rfl

theorem cell23_1176263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1176263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176263 prefixEnd_1176263 := by exact prefixLift 1176263
  have htrace : WordTrace (prefixWord ++ tailWord_1176263) baseStart_1176263 baseEnd_1176263 := by
    simpa [prefixWord, tailWord_1176263, baseEnd_1176263] using wordTrace_append hprefix tailTrace_1176263
  have hstable : (prefixWord ++ tailWord_1176263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176263).length < 2 ^ (prefixWord ++ tailWord_1176263).sum := by decide
  have hdescent : baseEnd_1176263 < baseStart_1176263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176277 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1176277 : Nat := 118140960795 + 1176277 * 2 ^ 59
def prefixEnd_1176277 : Nat := 4983230072969 + 3 ^ 40 * 1176277 * 2
def baseEnd_1176277 : Nat := 603995483828799544527907

theorem tailTrace_1176277 : CollatzResearch.WordTrace tailWord_1176277 prefixEnd_1176277 603995483828799544527907 := by
  unfold tailWord_1176277
  simp only [CollatzResearch.WordTrace]
  refine ⟨42902346759556795962871085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28601564506371197308580723 42902346759556795962871085)
  ·
    refine ⟨16088380034833798486076657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42902346759556795962871085 16088380034833798486076657)
    ·
      refine ⟨12066285026125348864557493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16088380034833798486076657 12066285026125348864557493)
      ·
        refine ⟨1131214221199251456052265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12066285026125348864557493 1131214221199251456052265)
        ·
          refine ⟨848410665899438592039199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1131214221199251456052265 848410665899438592039199)
          ·
            refine ⟨1272615998849157888058799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848410665899438592039199 1272615998849157888058799)
            ·
              refine ⟨1908923998273736832088199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272615998849157888058799 1908923998273736832088199)
              ·
                refine ⟨2863385997410605248132299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908923998273736832088199 2863385997410605248132299)
                ·
                  refine ⟨4295078996115907872198449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863385997410605248132299 4295078996115907872198449)
                  ·
                    refine ⟨3221309247086930904148837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4295078996115907872198449 3221309247086930904148837)
                    ·
                      refine ⟨603995483828799544527907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3221309247086930904148837 603995483828799544527907)
                      ·
                        rfl

theorem cell23_1176277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1176277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176277 prefixEnd_1176277 := by exact prefixLift 1176277
  have htrace : WordTrace (prefixWord ++ tailWord_1176277) baseStart_1176277 baseEnd_1176277 := by
    simpa [prefixWord, tailWord_1176277, baseEnd_1176277] using wordTrace_append hprefix tailTrace_1176277
  have hstable : (prefixWord ++ tailWord_1176277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176277).length < 2 ^ (prefixWord ++ tailWord_1176277).sum := by decide
  have hdescent : baseEnd_1176277 < baseStart_1176277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176306 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1176306 : Nat := 118140960795 + 1176306 * 2 ^ 59
def prefixEnd_1176306 : Nat := 4983230072969 + 3 ^ 40 * 1176306 * 2
def baseEnd_1176306 : Nat := 604010374767779931065273

theorem tailTrace_1176306 : CollatzResearch.WordTrace tailWord_1176306 prefixEnd_1176306 604010374767779931065273 := by
  unfold tailWord_1176306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725851119112933478919193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28602269650967822610451181 10725851119112933478919193)
  ·
    refine ⟨8044388339334700109189395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10725851119112933478919193 8044388339334700109189395)
    ·
      refine ⟨12066582509002050163784093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8044388339334700109189395 12066582509002050163784093)
      ·
        refine ⟨4524968440875768811419035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12066582509002050163784093 4524968440875768811419035)
        ·
          refine ⟨6787452661313653217128553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524968440875768811419035 6787452661313653217128553)
          ·
            refine ⟨5090589495985239912846415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6787452661313653217128553 5090589495985239912846415)
            ·
              refine ⟨7635884243977859869269623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090589495985239912846415 7635884243977859869269623)
              ·
                refine ⟨11453826365966789803904435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635884243977859869269623 11453826365966789803904435)
                ·
                  refine ⟨17180739548950184705856653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11453826365966789803904435 17180739548950184705856653)
                  ·
                    refine ⟨6442777330856319264696245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17180739548950184705856653 6442777330856319264696245)
                    ·
                      refine ⟨604010374767779931065273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6442777330856319264696245 604010374767779931065273)
                      ·
                        rfl

theorem cell23_1176306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1176306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176306 prefixEnd_1176306 := by exact prefixLift 1176306
  have htrace : WordTrace (prefixWord ++ tailWord_1176306) baseStart_1176306 baseEnd_1176306 := by
    simpa [prefixWord, tailWord_1176306, baseEnd_1176306] using wordTrace_append hprefix tailTrace_1176306
  have hstable : (prefixWord ++ tailWord_1176306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176306).length < 2 ^ (prefixWord ++ tailWord_1176306).sum := by decide
  have hdescent : baseEnd_1176306 < baseStart_1176306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176319 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_1176319 : Nat := 118140960795 + 1176319 * 2 ^ 59
def prefixEnd_1176319 : Nat := 4983230072969 + 3 ^ 40 * 1176319 * 2
def baseEnd_1176319 : Nat := 604017050016288380202713

theorem tailTrace_1176319 : CollatzResearch.WordTrace tailWord_1176319 prefixEnd_1176319 604017050016288380202713 := by
  unfold tailWord_1176319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42903878625404637135900011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28602585750269758090600007 42903878625404637135900011)
  ·
    refine ⟨64355817938106955703850017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42903878625404637135900011 64355817938106955703850017)
    ·
      refine ⟨48266863453580216777887513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64355817938106955703850017 48266863453580216777887513)
      ·
        refine ⟨36200147590185162583415635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48266863453580216777887513 36200147590185162583415635)
        ·
          refine ⟨54300221385277743875123453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36200147590185162583415635 54300221385277743875123453)
          ·
            refine ⟨20362583019479153953171295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54300221385277743875123453 20362583019479153953171295)
            ·
              refine ⟨30543874529218730929756943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20362583019479153953171295 30543874529218730929756943)
              ·
                refine ⟨45815811793828096394635415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30543874529218730929756943 45815811793828096394635415)
                ·
                  refine ⟨68723717690742144591953123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45815811793828096394635415 68723717690742144591953123)
                  ·
                    refine ⟨103085576536113216887929685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68723717690742144591953123 103085576536113216887929685)
                    ·
                      refine ⟨604017050016288380202713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 103085576536113216887929685 604017050016288380202713)
                      ·
                        rfl

theorem cell23_1176319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_1176319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176319 prefixEnd_1176319 := by exact prefixLift 1176319
  have htrace : WordTrace (prefixWord ++ tailWord_1176319) baseStart_1176319 baseEnd_1176319 := by
    simpa [prefixWord, tailWord_1176319, baseEnd_1176319] using wordTrace_append hprefix tailTrace_1176319
  have hstable : (prefixWord ++ tailWord_1176319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176319).length < 2 ^ (prefixWord ++ tailWord_1176319).sum := by decide
  have hdescent : baseEnd_1176319 < baseStart_1176319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176337 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_1176337 : Nat := 118140960795 + 1176337 * 2 ^ 59
def prefixEnd_1176337 : Nat := 4983230072969 + 3 ^ 40 * 1176337 * 2
def baseEnd_1176337 : Nat := 604026292668069309777631

theorem tailTrace_1176337 : CollatzResearch.WordTrace tailWord_1176337 prefixEnd_1176337 604026292668069309777631 := by
  unfold tailWord_1176337
  simp only [CollatzResearch.WordTrace]
  refine ⟨42904535139339426210055265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28603023426226284140036843 42904535139339426210055265)
  ·
    refine ⟨32178401354504569657541449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42904535139339426210055265 32178401354504569657541449)
    ·
      refine ⟨24133801015878427243156087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32178401354504569657541449 24133801015878427243156087)
      ·
        refine ⟨36200701523817640864734131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24133801015878427243156087 36200701523817640864734131)
        ·
          refine ⟨54301052285726461297101197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36200701523817640864734131 54301052285726461297101197)
          ·
            refine ⟨20362894607147422986412949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54301052285726461297101197 20362894607147422986412949)
            ·
              refine ⟨954510684710035452488107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20362894607147422986412949 954510684710035452488107)
              ·
                refine ⟨1431766027065053178732161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954510684710035452488107 1431766027065053178732161)
                ·
                  refine ⟨1073824520298789884049121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1431766027065053178732161 1073824520298789884049121)
                  ·
                    refine ⟨805368390224092413036841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1073824520298789884049121 805368390224092413036841)
                    ·
                      refine ⟨604026292668069309777631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805368390224092413036841 604026292668069309777631)
                      ·
                        rfl

theorem cell23_1176337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_1176337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176337 prefixEnd_1176337 := by exact prefixLift 1176337
  have htrace : WordTrace (prefixWord ++ tailWord_1176337) baseStart_1176337 baseEnd_1176337 := by
    simpa [prefixWord, tailWord_1176337, baseEnd_1176337] using wordTrace_append hprefix tailTrace_1176337
  have hstable : (prefixWord ++ tailWord_1176337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176337).length < 2 ^ (prefixWord ++ tailWord_1176337).sum := by decide
  have hdescent : baseEnd_1176337 < baseStart_1176337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176373 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1176373 : Nat := 118140960795 + 1176373 * 2 ^ 59
def prefixEnd_1176373 : Nat := 4983230072969 + 3 ^ 40 * 1176373 * 2
def baseEnd_1176373 : Nat := 201348259323877056309155

theorem tailTrace_1176373 : CollatzResearch.WordTrace tailWord_1176373 prefixEnd_1176373 201348259323877056309155 := by
  unfold tailWord_1176373
  simp only [CollatzResearch.WordTrace]
  refine ⟨42905848167209004358365773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28603898778139336238910515 42905848167209004358365773)
  ·
    refine ⟨16089693062703376634387165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42905848167209004358365773 16089693062703376634387165)
    ·
      refine ⟨6033634898513766237895187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16089693062703376634387165 6033634898513766237895187)
      ·
        refine ⟨9050452347770649356842781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6033634898513766237895187 9050452347770649356842781)
        ·
          refine ⟨3393919630413993508816043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9050452347770649356842781 3393919630413993508816043)
          ·
            refine ⟨5090879445620990263224065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393919630413993508816043 5090879445620990263224065)
            ·
              refine ⟨3818159584215742697418049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5090879445620990263224065 3818159584215742697418049)
              ·
                refine ⟨2863619688161807023063537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818159584215742697418049 2863619688161807023063537)
                ·
                  refine ⟨2147714766121355267297653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863619688161807023063537 2147714766121355267297653)
                  ·
                    refine ⟨201348259323877056309155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2147714766121355267297653 201348259323877056309155)
                    ·
                      rfl

theorem cell23_1176373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1176373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176373 prefixEnd_1176373 := by exact prefixLift 1176373
  have htrace : WordTrace (prefixWord ++ tailWord_1176373) baseStart_1176373 baseEnd_1176373 := by
    simpa [prefixWord, tailWord_1176373, baseEnd_1176373] using wordTrace_append hprefix tailTrace_1176373
  have hstable : (prefixWord ++ tailWord_1176373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176373).length < 2 ^ (prefixWord ++ tailWord_1176373).sum := by decide
  have hdescent : baseEnd_1176373 < baseStart_1176373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176393 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 6, 2]
def baseStart_1176393 : Nat := 118140960795 + 1176393 * 2 ^ 59
def prefixEnd_1176393 : Nat := 4983230072969 + 3 ^ 40 * 1176393 * 2
def baseEnd_1176393 : Nat := 604055047584721090677373

theorem tailTrace_1176393 : CollatzResearch.WordTrace tailWord_1176393 prefixEnd_1176393 604055047584721090677373 := by
  unfold tailWord_1176393
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906577627136547774093833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28604385084757698516062555 42906577627136547774093833)
  ·
    refine ⟨32179933220352410830570375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42906577627136547774093833 32179933220352410830570375)
    ·
      refine ⟨48269899830528616245855563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32179933220352410830570375 48269899830528616245855563)
      ·
        refine ⟨72404849745792924368783345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48269899830528616245855563 72404849745792924368783345)
        ·
          refine ⟨54303637309344693276587509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72404849745792924368783345 54303637309344693276587509)
          ·
            refine ⟨5090965997751064994680079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54303637309344693276587509 5090965997751064994680079)
            ·
              refine ⟨7636448996626597492020119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090965997751064994680079 7636448996626597492020119)
              ·
                refine ⟨11454673494939896238030179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7636448996626597492020119 11454673494939896238030179)
                ·
                  refine ⟨17182010242409844357045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11454673494939896238030179 17182010242409844357045269)
                  ·
                    refine ⟨805406730112961454236497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17182010242409844357045269 805406730112961454236497)
                    ·
                      refine ⟨604055047584721090677373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805406730112961454236497 604055047584721090677373)
                      ·
                        rfl

theorem cell23_1176393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6, 2].length) (baseStart_1176393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176393 prefixEnd_1176393 := by exact prefixLift 1176393
  have htrace : WordTrace (prefixWord ++ tailWord_1176393) baseStart_1176393 baseEnd_1176393 := by
    simpa [prefixWord, tailWord_1176393, baseEnd_1176393] using wordTrace_append hprefix tailTrace_1176393
  have hstable : (prefixWord ++ tailWord_1176393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176393).length < 2 ^ (prefixWord ++ tailWord_1176393).sum := by decide
  have hdescent : baseEnd_1176393 < baseStart_1176393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176410 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1176410 : Nat := 118140960795 + 1176410 * 2 ^ 59
def prefixEnd_1176410 : Nat := 4983230072969 + 3 ^ 40 * 1176410 * 2
def baseEnd_1176410 : Nat := 604063776755847524164795

theorem tailTrace_1176410 : CollatzResearch.WordTrace tailWord_1176410 prefixEnd_1176410 604063776755847524164795 := by
  unfold tailWord_1176410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10726799417018739919365671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28604798445383306451641789 10726799417018739919365671)
  ·
    refine ⟨16090199125528109879048507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10726799417018739919365671 16090199125528109879048507)
    ·
      refine ⟨24135298688292164818572761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16090199125528109879048507 24135298688292164818572761)
      ·
        refine ⟨18101474016219123613929571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24135298688292164818572761 18101474016219123613929571)
        ·
          refine ⟨27152211024328685420894357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18101474016219123613929571 27152211024328685420894357)
          ·
            refine ⟨1272759891765407129104423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27152211024328685420894357 1272759891765407129104423)
            ·
              refine ⟨1909139837648110693656635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1272759891765407129104423 1909139837648110693656635)
              ·
                refine ⟨2863709756472166040484953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909139837648110693656635 2863709756472166040484953)
                ·
                  refine ⟨2147782317354124530363715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2863709756472166040484953 2147782317354124530363715)
                  ·
                    refine ⟨3221673476031186795545573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2147782317354124530363715 3221673476031186795545573)
                    ·
                      refine ⟨604063776755847524164795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3221673476031186795545573 604063776755847524164795)
                      ·
                        rfl

theorem cell23_1176410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1176410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176410 prefixEnd_1176410 := by exact prefixLift 1176410
  have htrace : WordTrace (prefixWord ++ tailWord_1176410) baseStart_1176410 baseEnd_1176410 := by
    simpa [prefixWord, tailWord_1176410, baseEnd_1176410] using wordTrace_append hprefix tailTrace_1176410
  have hstable : (prefixWord ++ tailWord_1176410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176410).length < 2 ^ (prefixWord ++ tailWord_1176410).sum := by decide
  have hdescent : baseEnd_1176410 < baseStart_1176410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176416 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 8]
def baseStart_1176416 : Nat := 118140960795 + 1176416 * 2 ^ 59
def prefixEnd_1176416 : Nat := 4983230072969 + 3 ^ 40 * 1176416 * 2
def baseEnd_1176416 : Nat := 67118539737752722298863

theorem tailTrace_1176416 : CollatzResearch.WordTrace tailWord_1176416 prefixEnd_1176416 67118539737752722298863 := by
  unfold tailWord_1176416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21453708253026611351090551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28604944337368815134787401 21453708253026611351090551)
  ·
    refine ⟨32180562379539917026635827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21453708253026611351090551 32180562379539917026635827)
    ·
      refine ⟨48270843569309875539953741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32180562379539917026635827 48270843569309875539953741)
      ·
        refine ⟨18101566338491203327482653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48270843569309875539953741 18101566338491203327482653)
        ·
          refine ⟨6788087376934201247805995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18101566338491203327482653 6788087376934201247805995)
          ·
            refine ⟨10182131065401301871708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788087376934201247805995 10182131065401301871708993)
            ·
              refine ⟨7636598299050976403781745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10182131065401301871708993 7636598299050976403781745)
              ·
                refine ⟨5727448724288232302836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7636598299050976403781745 5727448724288232302836309)
                ·
                  refine ⟨67118539737752722298863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5727448724288232302836309 67118539737752722298863)
                  ·
                    rfl

theorem cell23_1176416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_1176416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176416 prefixEnd_1176416 := by exact prefixLift 1176416
  have htrace : WordTrace (prefixWord ++ tailWord_1176416) baseStart_1176416 baseEnd_1176416 := by
    simpa [prefixWord, tailWord_1176416, baseEnd_1176416] using wordTrace_append hprefix tailTrace_1176416
  have hstable : (prefixWord ++ tailWord_1176416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176416).length < 2 ^ (prefixWord ++ tailWord_1176416).sum := by decide
  have hdescent : baseEnd_1176416 < baseStart_1176416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176433 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 6]
def baseStart_1176433 : Nat := 118140960795 + 1176433 * 2 ^ 59
def prefixEnd_1176433 : Nat := 4983230072969 + 3 ^ 40 * 1176433 * 2
def baseEnd_1176433 : Nat := 67119509645655659353021

theorem tailTrace_1176433 : CollatzResearch.WordTrace tailWord_1176433 prefixEnd_1176433 67119509645655659353021 := by
  unfold tailWord_1176433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42908036546991634605549953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28605357697994423070366635 42908036546991634605549953)
  ·
    refine ⟨32181027410243725954162465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42908036546991634605549953 32181027410243725954162465)
    ·
      refine ⟨24135770557682794465621849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32181027410243725954162465 24135770557682794465621849)
      ·
        refine ⟨18101827918262095849216387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24135770557682794465621849 18101827918262095849216387)
        ·
          refine ⟨27152741877393143773824581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18101827918262095849216387 27152741877393143773824581)
          ·
            refine ⟨5091139102011214457592109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27152741877393143773824581 5091139102011214457592109)
            ·
              refine ⟨1909177163254205421597041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5091139102011214457592109 1909177163254205421597041)
              ·
                refine ⟨1431882872440654066197781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909177163254205421597041 1431882872440654066197781)
                ·
                  refine ⟨67119509645655659353021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1431882872440654066197781 67119509645655659353021)
                  ·
                    rfl

theorem cell23_1176433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 6].length) (baseStart_1176433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176433 prefixEnd_1176433 := by exact prefixLift 1176433
  have htrace : WordTrace (prefixWord ++ tailWord_1176433) baseStart_1176433 baseEnd_1176433 := by
    simpa [prefixWord, tailWord_1176433, baseEnd_1176433] using wordTrace_append hprefix tailTrace_1176433
  have hstable : (prefixWord ++ tailWord_1176433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176433).length < 2 ^ (prefixWord ++ tailWord_1176433).sum := by decide
  have hdescent : baseEnd_1176433 < baseStart_1176433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176437 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1176437 : Nat := 118140960795 + 1176437 * 2 ^ 59
def prefixEnd_1176437 : Nat := 4983230072969 + 3 ^ 40 * 1176437 * 2
def baseEnd_1176437 : Nat := 201359213577839639509057

theorem tailTrace_1176437 : CollatzResearch.WordTrace tailWord_1176437 prefixEnd_1176437 201359213577839639509057 := by
  unfold tailWord_1176437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42908182438977143288695565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28605454959318095525797043 42908182438977143288695565)
  ·
    refine ⟨16090568414616428733260837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42908182438977143288695565 16090568414616428733260837)
    ·
      refine ⟨3016981577740580387486407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16090568414616428733260837 3016981577740580387486407)
      ·
        refine ⟨4525472366610870581229611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016981577740580387486407 4525472366610870581229611)
        ·
          refine ⟨6788208549916305871844417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525472366610870581229611 6788208549916305871844417)
          ·
            refine ⟨5091156412437229403883313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6788208549916305871844417 5091156412437229403883313)
            ·
              refine ⟨3818367309327922052912485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091156412437229403883313 3818367309327922052912485)
              ·
                refine ⟨715943870498985384921091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3818367309327922052912485 715943870498985384921091)
                ·
                  refine ⟨1073915805748478077381637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 715943870498985384921091 1073915805748478077381637)
                  ·
                    refine ⟨201359213577839639509057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1073915805748478077381637 201359213577839639509057)
                    ·
                      rfl

theorem cell23_1176437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1176437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176437 prefixEnd_1176437 := by exact prefixLift 1176437
  have htrace : WordTrace (prefixWord ++ tailWord_1176437) baseStart_1176437 baseEnd_1176437 := by
    simpa [prefixWord, tailWord_1176437, baseEnd_1176437] using wordTrace_append hprefix tailTrace_1176437
  have hstable : (prefixWord ++ tailWord_1176437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176437).length < 2 ^ (prefixWord ++ tailWord_1176437).sum := by decide
  have hdescent : baseEnd_1176437 < baseStart_1176437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176460 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_1176460 : Nat := 118140960795 + 1176460 * 2 ^ 59
def prefixEnd_1176460 : Nat := 4983230072969 + 3 ^ 40 * 1176460 * 2
def baseEnd_1176460 : Nat := 604089450788572328539565

theorem tailTrace_1176460 : CollatzResearch.WordTrace tailWord_1176460 prefixEnd_1176460 604089450788572328539565 := by
  unfold tailWord_1176460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21454510658946909108391417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28606014211929212144521889 21454510658946909108391417)
  ·
    refine ⟨16090882994210181831293563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21454510658946909108391417 16090882994210181831293563)
    ·
      refine ⟨24136324491315272746940345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16090882994210181831293563 24136324491315272746940345)
      ·
        refine ⟨18102243368486454560205259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24136324491315272746940345 18102243368486454560205259)
        ·
          refine ⟨27153365052729681840307889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18102243368486454560205259 27153365052729681840307889)
          ·
            refine ⟨20365023789547261380230917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27153365052729681840307889 20365023789547261380230917)
            ·
              refine ⟨3818441960540111508793297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20365023789547261380230917 3818441960540111508793297)
              ·
                refine ⟨2863831470405083631594973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818441960540111508793297 2863831470405083631594973)
                ·
                  refine ⟨1073936801401906361848115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2863831470405083631594973 1073936801401906361848115)
                  ·
                    refine ⟨1610905202102859542772173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1073936801401906361848115 1610905202102859542772173)
                    ·
                      refine ⟨604089450788572328539565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1610905202102859542772173 604089450788572328539565)
                      ·
                        rfl

theorem cell23_1176460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_1176460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176460 prefixEnd_1176460 := by exact prefixLift 1176460
  have htrace : WordTrace (prefixWord ++ tailWord_1176460) baseStart_1176460 baseEnd_1176460 := by
    simpa [prefixWord, tailWord_1176460, baseEnd_1176460] using wordTrace_append hprefix tailTrace_1176460
  have hstable : (prefixWord ++ tailWord_1176460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176460).length < 2 ^ (prefixWord ++ tailWord_1176460).sum := by decide
  have hdescent : baseEnd_1176460 < baseStart_1176460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176503 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1176503 : Nat := 118140960795 + 1176503 * 2 ^ 59
def prefixEnd_1176503 : Nat := 4983230072969 + 3 ^ 40 * 1176503 * 2
def baseEnd_1176503 : Nat := 604111530456715660301867

theorem tailTrace_1176503 : CollatzResearch.WordTrace tailWord_1176503 prefixEnd_1176503 604111530456715660301867 := by
  unfold tailWord_1176503
  simp only [CollatzResearch.WordTrace]
  refine ⟨42910589656738036560598163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28607059771158691040398775 42910589656738036560598163)
  ·
    refine ⟨64365884485107054840897245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42910589656738036560598163 64365884485107054840897245)
    ·
      refine ⟨24137206681915145565336467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64365884485107054840897245 24137206681915145565336467)
      ·
        refine ⟨36205810022872718348004701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24137206681915145565336467 36205810022872718348004701)
        ·
          refine ⟨13577178758577269380501763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36205810022872718348004701 13577178758577269380501763)
          ·
            refine ⟨20365768137865904070752645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13577178758577269380501763 20365768137865904070752645)
            ·
              refine ⟨3818581525849857013266121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20365768137865904070752645 3818581525849857013266121)
              ·
                refine ⟨2863936144387392759949591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3818581525849857013266121 2863936144387392759949591)
                ·
                  refine ⟨4295904216581089139924387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863936144387392759949591 4295904216581089139924387)
                  ·
                    refine ⟨6443856324871633709886581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4295904216581089139924387 6443856324871633709886581)
                    ·
                      refine ⟨604111530456715660301867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6443856324871633709886581 604111530456715660301867)
                      ·
                        rfl

theorem cell23_1176503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1176503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176503 prefixEnd_1176503 := by exact prefixLift 1176503
  have htrace : WordTrace (prefixWord ++ tailWord_1176503) baseStart_1176503 baseEnd_1176503 := by
    simpa [prefixWord, tailWord_1176503, baseEnd_1176503] using wordTrace_append hprefix tailTrace_1176503
  have hstable : (prefixWord ++ tailWord_1176503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176503).length < 2 ^ (prefixWord ++ tailWord_1176503).sum := by decide
  have hdescent : baseEnd_1176503 < baseStart_1176503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176530 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1176530 : Nat := 118140960795 + 1176530 * 2 ^ 59
def prefixEnd_1176530 : Nat := 4983230072969 + 3 ^ 40 * 1176530 * 2
def baseEnd_1176530 : Nat := 604125394434387054664243

theorem tailTrace_1176530 : CollatzResearch.WordTrace tailWord_1176530 prefixEnd_1176530 604125394434387054664243 := by
  unfold tailWord_1176530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10727893606910055042957761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28607716285093480114554029 10727893606910055042957761)
  ·
    refine ⟨8045920205182541282218321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10727893606910055042957761 8045920205182541282218321)
    ·
      refine ⟨6034440153886905961663741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8045920205182541282218321 6034440153886905961663741)
      ·
        refine ⟨2262915057707589735623903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6034440153886905961663741 2262915057707589735623903)
        ·
          refine ⟨3394372586561384603435855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262915057707589735623903 3394372586561384603435855)
          ·
            refine ⟨5091558879842076905153783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394372586561384603435855 5091558879842076905153783)
            ·
              refine ⟨7637338319763115357730675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091558879842076905153783 7637338319763115357730675)
              ·
                refine ⟨11456007479644673036596013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637338319763115357730675 11456007479644673036596013)
                ·
                  refine ⟨4296002804866752388723505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11456007479644673036596013 4296002804866752388723505)
                  ·
                    refine ⟨3222002103650064291542629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4296002804866752388723505 3222002103650064291542629)
                    ·
                      refine ⟨604125394434387054664243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3222002103650064291542629 604125394434387054664243)
                      ·
                        rfl

theorem cell23_1176530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1176530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176530 prefixEnd_1176530 := by exact prefixLift 1176530
  have htrace : WordTrace (prefixWord ++ tailWord_1176530) baseStart_1176530 baseEnd_1176530 := by
    simpa [prefixWord, tailWord_1176530, baseEnd_1176530] using wordTrace_append hprefix tailTrace_1176530
  have hstable : (prefixWord ++ tailWord_1176530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176530).length < 2 ^ (prefixWord ++ tailWord_1176530).sum := by decide
  have hdescent : baseEnd_1176530 < baseStart_1176530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176551 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1176551 : Nat := 118140960795 + 1176551 * 2 ^ 59
def prefixEnd_1176551 : Nat := 4983230072969 + 3 ^ 40 * 1176551 * 2
def baseEnd_1176551 : Nat := 604136177528131472501647

theorem tailTrace_1176551 : CollatzResearch.WordTrace tailWord_1176551 prefixEnd_1176551 604136177528131472501647 := by
  unfold tailWord_1176551
  simp only [CollatzResearch.WordTrace]
  refine ⟨42912340360564140758345507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608226907042760505563671 42912340360564140758345507)
  ·
    refine ⟨64368510540846211137518261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42912340360564140758345507 64368510540846211137518261)
    ·
      refine ⟨6034547863204332294142337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64368510540846211137518261 6034547863204332294142337)
      ·
        refine ⟨4525910897403249220606753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034547863204332294142337 4525910897403249220606753)
        ·
          refine ⟨3394433173052436915455065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525910897403249220606753 3394433173052436915455065)
          ·
            refine ⟨2545824879789327686591299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3394433173052436915455065 2545824879789327686591299)
            ·
              refine ⟨3818737319683991529886949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545824879789327686591299 3818737319683991529886949)
              ·
                refine ⟨716013247440748411853803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3818737319683991529886949 716013247440748411853803)
                ·
                  refine ⟨1074019871161122617780705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716013247440748411853803 1074019871161122617780705)
                  ·
                    refine ⟨805514903370841963335529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074019871161122617780705 805514903370841963335529)
                    ·
                      refine ⟨604136177528131472501647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805514903370841963335529 604136177528131472501647)
                      ·
                        rfl

theorem cell23_1176551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1176551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176551 prefixEnd_1176551 := by exact prefixLift 1176551
  have htrace : WordTrace (prefixWord ++ tailWord_1176551) baseStart_1176551 baseEnd_1176551 := by
    simpa [prefixWord, tailWord_1176551, baseEnd_1176551] using wordTrace_append hprefix tailTrace_1176551
  have hstable : (prefixWord ++ tailWord_1176551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176551).length < 2 ^ (prefixWord ++ tailWord_1176551).sum := by decide
  have hdescent : baseEnd_1176551 < baseStart_1176551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176573 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1176573 : Nat := 118140960795 + 1176573 * 2 ^ 59
def prefixEnd_1176573 : Nat := 4983230072969 + 3 ^ 40 * 1176573 * 2
def baseEnd_1176573 : Nat := 604147474102530386426545

theorem tailTrace_1176573 : CollatzResearch.WordTrace tailWord_1176573 prefixEnd_1176573 604147474102530386426545 := by
  unfold tailWord_1176573
  simp only [CollatzResearch.WordTrace]
  refine ⟨42913142766484438515646373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608761844322959010430915 42913142766484438515646373)
  ·
    refine ⟨8046214268715832221683695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42913142766484438515646373 8046214268715832221683695)
    ·
      refine ⟨12069321403073748332525543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8046214268715832221683695 12069321403073748332525543)
      ·
        refine ⟨18103982104610622498788315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12069321403073748332525543 18103982104610622498788315)
        ·
          refine ⟨27155973156915933748182473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18103982104610622498788315 27155973156915933748182473)
          ·
            refine ⟨20366979867686950311136855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27155973156915933748182473 20366979867686950311136855)
            ·
              refine ⟨30550469801530425466705283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20366979867686950311136855 30550469801530425466705283)
              ·
                refine ⟨45825704702295638200057925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30550469801530425466705283 45825704702295638200057925)
                ·
                  refine ⟨8592319631680432162510861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45825704702295638200057925 8592319631680432162510861)
                  ·
                    refine ⟨3222119861880162060941573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8592319631680432162510861 3222119861880162060941573)
                    ·
                      refine ⟨604147474102530386426545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3222119861880162060941573 604147474102530386426545)
                      ·
                        rfl

theorem cell23_1176573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1176573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176573 prefixEnd_1176573 := by exact prefixLift 1176573
  have htrace : WordTrace (prefixWord ++ tailWord_1176573) baseStart_1176573 baseEnd_1176573 := by
    simpa [prefixWord, tailWord_1176573, baseEnd_1176573] using wordTrace_append hprefix tailTrace_1176573
  have hstable : (prefixWord ++ tailWord_1176573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176573).length < 2 ^ (prefixWord ++ tailWord_1176573).sum := by decide
  have hdescent : baseEnd_1176573 < baseStart_1176573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176577 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_1176577 : Nat := 118140960795 + 1176577 * 2 ^ 59
def prefixEnd_1176577 : Nat := 4983230072969 + 3 ^ 40 * 1176577 * 2
def baseEnd_1176577 : Nat := 604149528025148370776527

theorem tailTrace_1176577 : CollatzResearch.WordTrace tailWord_1176577 prefixEnd_1176577 604149528025148370776527 := by
  unfold tailWord_1176577
  simp only [CollatzResearch.WordTrace]
  refine ⟨42913288658469947198791985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28608859105646631465861323 42913288658469947198791985)
  ·
    refine ⟨32184966493852460399093989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42913288658469947198791985 32184966493852460399093989)
    ·
      refine ⟨6034681217597336324830123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32184966493852460399093989 6034681217597336324830123)
      ·
        refine ⟨9052021826396004487245185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6034681217597336324830123 9052021826396004487245185)
        ·
          refine ⟨6789016369797003365433889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9052021826396004487245185 6789016369797003365433889)
          ·
            refine ⟨5091762277347752524075417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789016369797003365433889 5091762277347752524075417)
            ·
              refine ⟨3818821708010814393056563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091762277347752524075417 3818821708010814393056563)
              ·
                refine ⟨5728232562016221589584845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818821708010814393056563 5728232562016221589584845)
                ·
                  refine ⟨2148087210756083096094317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5728232562016221589584845 2148087210756083096094317)
                  ·
                    refine ⟨805532704033531161035369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148087210756083096094317 805532704033531161035369)
                    ·
                      refine ⟨604149528025148370776527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805532704033531161035369 604149528025148370776527)
                      ·
                        rfl

theorem cell23_1176577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_1176577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176577 prefixEnd_1176577 := by exact prefixLift 1176577
  have htrace : WordTrace (prefixWord ++ tailWord_1176577) baseStart_1176577 baseEnd_1176577 := by
    simpa [prefixWord, tailWord_1176577, baseEnd_1176577] using wordTrace_append hprefix tailTrace_1176577
  have hstable : (prefixWord ++ tailWord_1176577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176577).length < 2 ^ (prefixWord ++ tailWord_1176577).sum := by decide
  have hdescent : baseEnd_1176577 < baseStart_1176577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176583 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 8]
def baseStart_1176583 : Nat := 118140960795 + 1176583 * 2 ^ 59
def prefixEnd_1176583 : Nat := 4983230072969 + 3 ^ 40 * 1176583 * 2
def baseEnd_1176583 : Nat := 201384202969691782433833

theorem tailTrace_1176583 : CollatzResearch.WordTrace tailWord_1176583 prefixEnd_1176583 201384202969691782433833 := by
  unfold tailWord_1176583
  simp only [CollatzResearch.WordTrace]
  refine ⟨42913507496448210223510403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28609004997632140149006935 42913507496448210223510403)
  ·
    refine ⟨64370261244672315335265605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42913507496448210223510403 64370261244672315335265605)
    ·
      refine ⟨12069423983376059125362301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64370261244672315335265605 12069423983376059125362301)
      ·
        refine ⟨4526033993766022172010863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12069423983376059125362301 4526033993766022172010863)
        ·
          refine ⟨6789050990649033258016295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526033993766022172010863 6789050990649033258016295)
          ·
            refine ⟨10183576485973549887024443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789050990649033258016295 10183576485973549887024443)
            ·
              refine ⟨15275364728960324830536665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10183576485973549887024443 15275364728960324830536665)
              ·
                refine ⟨11456523546720243622902499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15275364728960324830536665 11456523546720243622902499)
                ·
                  refine ⟨17184785320080365434353749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11456523546720243622902499 17184785320080365434353749)
                  ·
                    refine ⟨201384202969691782433833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17184785320080365434353749 201384202969691782433833)
                    ·
                      rfl

theorem cell23_1176583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_1176583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176583 prefixEnd_1176583 := by exact prefixLift 1176583
  have htrace : WordTrace (prefixWord ++ tailWord_1176583) baseStart_1176583 baseEnd_1176583 := by
    simpa [prefixWord, tailWord_1176583, baseEnd_1176583] using wordTrace_append hprefix tailTrace_1176583
  have hstable : (prefixWord ++ tailWord_1176583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176583).length < 2 ^ (prefixWord ++ tailWord_1176583).sum := by decide
  have hdescent : baseEnd_1176583 < baseStart_1176583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176593 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_1176593 : Nat := 118140960795 + 1176593 * 2 ^ 59
def prefixEnd_1176593 : Nat := 4983230072969 + 3 ^ 40 * 1176593 * 2
def baseEnd_1176593 : Nat := 604157743715620308176453

theorem tailTrace_1176593 : CollatzResearch.WordTrace tailWord_1176593 prefixEnd_1176593 604157743715620308176453 := by
  unfold tailWord_1176593
  simp only [CollatzResearch.WordTrace]
  refine ⟨42913872226411981931374433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28609248150941321287582955 42913872226411981931374433)
  ·
    refine ⟨32185404169808986448530825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42913872226411981931374433 32185404169808986448530825)
    ·
      refine ⟨24139053127356739836398119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32185404169808986448530825 24139053127356739836398119)
      ·
        refine ⟨36208579691035109754597179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24139053127356739836398119 36208579691035109754597179)
        ·
          refine ⟨54312869536552664631895769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36208579691035109754597179 54312869536552664631895769)
          ·
            refine ⟨40734652152414498473921827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54312869536552664631895769 40734652152414498473921827)
            ·
              refine ⟨61101978228621747710882741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40734652152414498473921827 61101978228621747710882741)
              ·
                refine ⟨5728310458933288847895257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61101978228621747710882741 5728310458933288847895257)
                ·
                  refine ⟨4296232844199966635921443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5728310458933288847895257 4296232844199966635921443)
                  ·
                    refine ⟨6444349266299949953882165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4296232844199966635921443 6444349266299949953882165)
                    ·
                      refine ⟨604157743715620308176453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6444349266299949953882165 604157743715620308176453)
                      ·
                        rfl

theorem cell23_1176593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_1176593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176593 prefixEnd_1176593 := by exact prefixLift 1176593
  have htrace : WordTrace (prefixWord ++ tailWord_1176593) baseStart_1176593 baseEnd_1176593 := by
    simpa [prefixWord, tailWord_1176593, baseEnd_1176593] using wordTrace_append hprefix tailTrace_1176593
  have hstable : (prefixWord ++ tailWord_1176593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176593).length < 2 ^ (prefixWord ++ tailWord_1176593).sum := by decide
  have hdescent : baseEnd_1176593 < baseStart_1176593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176643 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 7]
def baseStart_1176643 : Nat := 118140960795 + 1176643 * 2 ^ 59
def prefixEnd_1176643 : Nat := 4983230072969 + 3 ^ 40 * 1176643 * 2
def baseEnd_1176643 : Nat := 201394472582781704183741

theorem tailTrace_1176643 : CollatzResearch.WordTrace tailWord_1176643 prefixEnd_1176643 201394472582781704183741 := by
  unfold tailWord_1176643
  simp only [CollatzResearch.WordTrace]
  refine ⟨42915695876230840470694583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28610463917487226980463055 42915695876230840470694583)
  ·
    refine ⟨64373543814346260706041875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42915695876230840470694583 64373543814346260706041875)
    ·
      refine ⟨96560315721519391059062813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64373543814346260706041875 96560315721519391059062813)
      ·
        refine ⟨36210118395569771647148555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96560315721519391059062813 36210118395569771647148555)
        ·
          refine ⟨54315177593354657470722833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36210118395569771647148555 54315177593354657470722833)
          ·
            refine ⟨40736383195015993103042125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54315177593354657470722833 40736383195015993103042125)
            ·
              refine ⟨15276143698130997413640797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40736383195015993103042125 15276143698130997413640797)
              ·
                refine ⟨5728553886799124030115299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15276143698130997413640797 5728553886799124030115299)
                ·
                  refine ⟨8592830830198686045172949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728553886799124030115299 8592830830198686045172949)
                  ·
                    refine ⟨201394472582781704183741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8592830830198686045172949 201394472582781704183741)
                    ·
                      rfl

theorem cell23_1176643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_1176643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176643 prefixEnd_1176643 := by exact prefixLift 1176643
  have htrace : WordTrace (prefixWord ++ tailWord_1176643) baseStart_1176643 baseEnd_1176643 := by
    simpa [prefixWord, tailWord_1176643, baseEnd_1176643] using wordTrace_append hprefix tailTrace_1176643
  have hstable : (prefixWord ++ tailWord_1176643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176643).length < 2 ^ (prefixWord ++ tailWord_1176643).sum := by decide
  have hdescent : baseEnd_1176643 < baseStart_1176643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176647 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 5]
def baseStart_1176647 : Nat := 118140960795 + 1176647 * 2 ^ 59
def prefixEnd_1176647 : Nat := 4983230072969 + 3 ^ 40 * 1176647 * 2
def baseEnd_1176647 : Nat := 67131719074551455211245

theorem tailTrace_1176647 : CollatzResearch.WordTrace tailWord_1176647 prefixEnd_1176647 67131719074551455211245 := by
  unfold tailWord_1176647
  simp only [CollatzResearch.WordTrace]
  refine ⟨42915841768216349153840195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28610561178810899435893463 42915841768216349153840195)
  ·
    refine ⟨64373762652324523730760293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42915841768216349153840195 64373762652324523730760293)
    ·
      refine ⟨12070080497310848199517555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64373762652324523730760293 12070080497310848199517555)
      ·
        refine ⟨18105120745966272299276333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12070080497310848199517555 18105120745966272299276333)
        ·
          refine ⟨6789420279737352112228625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18105120745966272299276333 6789420279737352112228625)
          ·
            refine ⟨5092065209803014084171469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6789420279737352112228625 5092065209803014084171469)
            ·
              refine ⟨1909524453676130281564301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5092065209803014084171469 1909524453676130281564301)
              ·
                refine ⟨716071670128548855586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909524453676130281564301 716071670128548855586613)
                ·
                  refine ⟨67131719074551455211245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716071670128548855586613 67131719074551455211245)
                  ·
                    rfl

theorem cell23_1176647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 5].length) (baseStart_1176647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176647 prefixEnd_1176647 := by exact prefixLift 1176647
  have htrace : WordTrace (prefixWord ++ tailWord_1176647) baseStart_1176647 baseEnd_1176647 := by
    simpa [prefixWord, tailWord_1176647, baseEnd_1176647] using wordTrace_append hprefix tailTrace_1176647
  have hstable : (prefixWord ++ tailWord_1176647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176647).length < 2 ^ (prefixWord ++ tailWord_1176647).sum := by decide
  have hdescent : baseEnd_1176647 < baseStart_1176647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176660 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1176660 : Nat := 118140960795 + 1176660 * 2 ^ 59
def prefixEnd_1176660 : Nat := 4983230072969 + 3 ^ 40 * 1176660 * 2
def baseEnd_1176660 : Nat := 201397382306490515346215

theorem tailTrace_1176660 : CollatzResearch.WordTrace tailWord_1176660 prefixEnd_1176660 201397382306490515346215 := by
  unfold tailWord_1176660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458157958584626187031717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28610877278112834916042289 21458157958584626187031717)
  ·
    refine ⟨4023404617234617410068447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21458157958584626187031717 4023404617234617410068447)
    ·
      refine ⟨6035106925851926115102671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023404617234617410068447 6035106925851926115102671)
      ·
        refine ⟨9052660388777889172654007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035106925851926115102671 9052660388777889172654007)
        ·
          refine ⟨13578990583166833758981011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9052660388777889172654007 13578990583166833758981011)
          ·
            refine ⟨20368485874750250638471517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13578990583166833758981011 20368485874750250638471517)
            ·
              refine ⟨7638182203031343989426819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20368485874750250638471517 7638182203031343989426819)
              ·
                refine ⟨11457273304547015984140229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7638182203031343989426819 11457273304547015984140229)
                ·
                  refine ⟨2148238744602565497026293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11457273304547015984140229 2148238744602565497026293)
                  ·
                    refine ⟨201397382306490515346215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2148238744602565497026293 201397382306490515346215)
                    ·
                      rfl

theorem cell23_1176660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1176660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176660 prefixEnd_1176660 := by exact prefixLift 1176660
  have htrace : WordTrace (prefixWord ++ tailWord_1176660) baseStart_1176660 baseEnd_1176660 := by
    simpa [prefixWord, tailWord_1176660, baseEnd_1176660] using wordTrace_append hprefix tailTrace_1176660
  have hstable : (prefixWord ++ tailWord_1176660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176660).length < 2 ^ (prefixWord ++ tailWord_1176660).sum := by decide
  have hdescent : baseEnd_1176660 < baseStart_1176660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176683 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_1176683 : Nat := 118140960795 + 1176683 * 2 ^ 59
def prefixEnd_1176683 : Nat := 4983230072969 + 3 ^ 40 * 1176683 * 2
def baseEnd_1176683 : Nat := 604203956974524956051039

theorem tailTrace_1176683 : CollatzResearch.WordTrace tailWord_1176683 prefixEnd_1176683 604203956974524956051039 := by
  unfold tailWord_1176683
  simp only [CollatzResearch.WordTrace]
  refine ⟨42917154796085927302150703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28611436530723951534767135 42917154796085927302150703)
  ·
    refine ⟨64375732194128890953226055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42917154796085927302150703 64375732194128890953226055)
    ·
      refine ⟨96563598291193336429839083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64375732194128890953226055 96563598291193336429839083)
      ·
        refine ⟨144845397436790004644758625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96563598291193336429839083 144845397436790004644758625)
        ·
          refine ⟨108634048077592503483568969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144845397436790004644758625 108634048077592503483568969)
          ·
            refine ⟨81475536058194377612676727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108634048077592503483568969 81475536058194377612676727)
            ·
              refine ⟨122213304087291566419015091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81475536058194377612676727 122213304087291566419015091)
              ·
                refine ⟨183319956130937349628522637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122213304087291566419015091 183319956130937349628522637)
                ·
                  refine ⟨68744983549101506110695989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183319956130937349628522637 68744983549101506110695989)
                  ·
                    refine ⟨6444842207728266197877749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68744983549101506110695989 6444842207728266197877749)
                    ·
                      refine ⟨604203956974524956051039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6444842207728266197877749 604203956974524956051039)
                      ·
                        rfl

theorem cell23_1176683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_1176683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176683 prefixEnd_1176683 := by exact prefixLift 1176683
  have htrace : WordTrace (prefixWord ++ tailWord_1176683) baseStart_1176683 baseEnd_1176683 := by
    simpa [prefixWord, tailWord_1176683, baseEnd_1176683] using wordTrace_append hprefix tailTrace_1176683
  have hstable : (prefixWord ++ tailWord_1176683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176683).length < 2 ^ (prefixWord ++ tailWord_1176683).sum := by decide
  have hdescent : baseEnd_1176683 < baseStart_1176683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176815 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 1, 1, 3]
def baseStart_1176815 : Nat := 118140960795 + 1176815 * 2 ^ 59
def prefixEnd_1176815 : Nat := 4983230072969 + 3 ^ 40 * 1176815 * 2
def baseEnd_1176815 : Nat := 604271736420918439600433

theorem tailTrace_1176815 : CollatzResearch.WordTrace tailWord_1176815 prefixEnd_1176815 604271736420918439600433 := by
  unfold tailWord_1176815
  simp only [CollatzResearch.WordTrace]
  refine ⟨42921969231607713845955899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28614646154405142563970599 42921969231607713845955899)
  ·
    refine ⟨64382953847411570768933849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42921969231607713845955899 64382953847411570768933849)
    ·
      refine ⟨48287215385558678076700387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64382953847411570768933849 48287215385558678076700387)
      ·
        refine ⟨72430823078338017115050581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48287215385558678076700387 72430823078338017115050581)
        ·
          refine ⟨848798707949273638066999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 72430823078338017115050581 848798707949273638066999)
          ·
            refine ⟨1273198061923910457100499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848798707949273638066999 1273198061923910457100499)
            ·
              refine ⟨1909797092885865685650749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273198061923910457100499 1909797092885865685650749)
              ·
                refine ⟨716173909832199632119031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1909797092885865685650749 716173909832199632119031)
                ·
                  refine ⟨1074260864748299448178547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716173909832199632119031 1074260864748299448178547)
                  ·
                    refine ⟨1611391297122449172267821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074260864748299448178547 1611391297122449172267821)
                    ·
                      refine ⟨604271736420918439600433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611391297122449172267821 604271736420918439600433)
                      ·
                        rfl

theorem cell23_1176815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 1, 3].length) (baseStart_1176815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176815 prefixEnd_1176815 := by exact prefixLift 1176815
  have htrace : WordTrace (prefixWord ++ tailWord_1176815) baseStart_1176815 baseEnd_1176815 := by
    simpa [prefixWord, tailWord_1176815, baseEnd_1176815] using wordTrace_append hprefix tailTrace_1176815
  have hstable : (prefixWord ++ tailWord_1176815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176815).length < 2 ^ (prefixWord ++ tailWord_1176815).sum := by decide
  have hdescent : baseEnd_1176815 < baseStart_1176815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176847 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 9, 2]
def baseStart_1176847 : Nat := 118140960795 + 1176847 * 2 ^ 59
def prefixEnd_1176847 : Nat := 4983230072969 + 3 ^ 40 * 1176847 * 2
def baseEnd_1176847 : Nat := 604288167801862314400285

theorem tailTrace_1176847 : CollatzResearch.WordTrace tailWord_1176847 prefixEnd_1176847 604288167801862314400285 := by
  unfold tailWord_1176847
  simp only [CollatzResearch.WordTrace]
  refine ⟨42923136367491783311120795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28615424244994522207413863 42923136367491783311120795)
  ·
    refine ⟨64384704551237674966681193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42923136367491783311120795 64384704551237674966681193)
    ·
      refine ⟨48288528413428256225010895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64384704551237674966681193 48288528413428256225010895)
      ·
        refine ⟨72432792620142384337516343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48288528413428256225010895 72432792620142384337516343)
        ·
          refine ⟨108649188930213576506274515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72432792620142384337516343 108649188930213576506274515)
          ·
            refine ⟨162973783395320364759411773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108649188930213576506274515 162973783395320364759411773)
            ·
              refine ⟨61115168773245136784779415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162973783395320364759411773 61115168773245136784779415)
              ·
                refine ⟨91672753159867705177169123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61115168773245136784779415 91672753159867705177169123)
                ·
                  refine ⟨137509129739801557765753685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91672753159867705177169123 137509129739801557765753685)
                  ·
                    refine ⟨805717557069149752533713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137509129739801557765753685 805717557069149752533713)
                    ·
                      refine ⟨604288167801862314400285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805717557069149752533713 604288167801862314400285)
                      ·
                        rfl

theorem cell23_1176847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9, 2].length) (baseStart_1176847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176847 prefixEnd_1176847 := by exact prefixLift 1176847
  have htrace : WordTrace (prefixWord ++ tailWord_1176847) baseStart_1176847 baseEnd_1176847 := by
    simpa [prefixWord, tailWord_1176847, baseEnd_1176847] using wordTrace_append hprefix tailTrace_1176847
  have hstable : (prefixWord ++ tailWord_1176847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176847).length < 2 ^ (prefixWord ++ tailWord_1176847).sum := by decide
  have hdescent : baseEnd_1176847 < baseStart_1176847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176889 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1176889 : Nat := 118140960795 + 1176889 * 2 ^ 59
def prefixEnd_1176889 : Nat := 4983230072969 + 3 ^ 40 * 1176889 * 2
def baseEnd_1176889 : Nat := 604309733989351150075093

theorem tailTrace_1176889 : CollatzResearch.WordTrace tailWord_1176889 prefixEnd_1176889 604309733989351150075093 := by
  unfold tailWord_1176889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42924668233339624484149721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28616445488893082989433147 42924668233339624484149721)
  ·
    refine ⟨32193501175004718363112291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42924668233339624484149721 32193501175004718363112291)
    ·
      refine ⟨48290251762507077544668437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32193501175004718363112291 48290251762507077544668437)
      ·
        refine ⟨2263605551367519259906333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48290251762507077544668437 2263605551367519259906333)
        ·
          refine ⟨848852081762819722464875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2263605551367519259906333 848852081762819722464875)
          ·
            refine ⟨1273278122644229583697313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848852081762819722464875 1273278122644229583697313)
            ·
              refine ⟨954958591983172187772985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273278122644229583697313 954958591983172187772985)
              ·
                refine ⟨716218943987379140829739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954958591983172187772985 716218943987379140829739)
                ·
                  refine ⟨1074328415981068711244609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716218943987379140829739 1074328415981068711244609)
                  ·
                    refine ⟨805746311985801533433457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074328415981068711244609 805746311985801533433457)
                    ·
                      refine ⟨604309733989351150075093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805746311985801533433457 604309733989351150075093)
                      ·
                        rfl

theorem cell23_1176889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1176889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176889 prefixEnd_1176889 := by exact prefixLift 1176889
  have htrace : WordTrace (prefixWord ++ tailWord_1176889) baseStart_1176889 baseEnd_1176889 := by
    simpa [prefixWord, tailWord_1176889, baseEnd_1176889] using wordTrace_append hprefix tailTrace_1176889
  have hstable : (prefixWord ++ tailWord_1176889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176889).length < 2 ^ (prefixWord ++ tailWord_1176889).sum := by decide
  have hdescent : baseEnd_1176889 < baseStart_1176889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176917 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 9]
def baseStart_1176917 : Nat := 118140960795 + 1176917 * 2 ^ 59
def prefixEnd_1176917 : Nat := 4983230072969 + 3 ^ 40 * 1176917 * 2
def baseEnd_1176917 : Nat := 67147123494186337836107

theorem tailTrace_1176917 : CollatzResearch.WordTrace tailWord_1176917 prefixEnd_1176917 67147123494186337836107 := by
  unfold tailWord_1176917
  simp only [CollatzResearch.WordTrace]
  refine ⟨42925689477238185266169005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28617126318158790177446003 42925689477238185266169005)
  ·
    refine ⟨16097133553964319474813377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42925689477238185266169005 16097133553964319474813377)
    ·
      refine ⟨12072850165473239606110033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16097133553964319474813377 12072850165473239606110033)
      ·
        refine ⟨9054637624104929704582525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12072850165473239606110033 9054637624104929704582525)
        ·
          refine ⟨3395489109039348639218447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9054637624104929704582525 3395489109039348639218447)
          ·
            refine ⟨5093233663559022958827671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395489109039348639218447 5093233663559022958827671)
            ·
              refine ⟨7639850495338534438241507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093233663559022958827671 7639850495338534438241507)
              ·
                refine ⟨11459775743007801657362261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639850495338534438241507 11459775743007801657362261)
                ·
                  refine ⟨67147123494186337836107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11459775743007801657362261 67147123494186337836107)
                  ·
                    rfl

theorem cell23_1176917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_1176917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176917 prefixEnd_1176917 := by exact prefixLift 1176917
  have htrace : WordTrace (prefixWord ++ tailWord_1176917) baseStart_1176917 baseEnd_1176917 := by
    simpa [prefixWord, tailWord_1176917, baseEnd_1176917] using wordTrace_append hprefix tailTrace_1176917
  have hstable : (prefixWord ++ tailWord_1176917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176917).length < 2 ^ (prefixWord ++ tailWord_1176917).sum := by decide
  have hdescent : baseEnd_1176917 < baseStart_1176917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176927 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1176927 : Nat := 118140960795 + 1176927 * 2 ^ 59
def prefixEnd_1176927 : Nat := 4983230072969 + 3 ^ 40 * 1176927 * 2
def baseEnd_1176927 : Nat := 604329246254222001399917

theorem tailTrace_1176927 : CollatzResearch.WordTrace tailWord_1176927 prefixEnd_1176927 604329246254222001399917 := by
  unfold tailWord_1176927
  simp only [CollatzResearch.WordTrace]
  refine ⟨42926054207201956974033035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28617369471467971316022023 42926054207201956974033035)
  ·
    refine ⟨64389081310802935461049553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42926054207201956974033035 64389081310802935461049553)
    ·
      refine ⟨48291810983102201595787165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64389081310802935461049553 48291810983102201595787165)
      ·
        refine ⟨18109429118663325598420187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48291810983102201595787165 18109429118663325598420187)
        ·
          refine ⟨27164143677994988397630281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109429118663325598420187 27164143677994988397630281)
          ·
            refine ⟨20373107758496241298222711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27164143677994988397630281 20373107758496241298222711)
            ·
              refine ⟨30559661637744361947334067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20373107758496241298222711 30559661637744361947334067)
              ·
                refine ⟨45839492456616542921001101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30559661637744361947334067 45839492456616542921001101)
                ·
                  refine ⟨17189809671231203595375413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45839492456616542921001101 17189809671231203595375413)
                  ·
                    refine ⟨1611544656677925337066445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17189809671231203595375413 1611544656677925337066445)
                    ·
                      refine ⟨604329246254222001399917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611544656677925337066445 604329246254222001399917)
                      ·
                        rfl

theorem cell23_1176927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1176927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176927 prefixEnd_1176927 := by exact prefixLift 1176927
  have htrace : WordTrace (prefixWord ++ tailWord_1176927) baseStart_1176927 baseEnd_1176927 := by
    simpa [prefixWord, tailWord_1176927, baseEnd_1176927] using wordTrace_append hprefix tailTrace_1176927
  have hstable : (prefixWord ++ tailWord_1176927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176927).length < 2 ^ (prefixWord ++ tailWord_1176927).sum := by decide
  have hdescent : baseEnd_1176927 < baseStart_1176927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176957 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1176957 : Nat := 118140960795 + 1176957 * 2 ^ 59
def prefixEnd_1176957 : Nat := 4983230072969 + 3 ^ 40 * 1176957 * 2
def baseEnd_1176957 : Nat := 604344650673856884024779

theorem tailTrace_1176957 : CollatzResearch.WordTrace tailWord_1176957 prefixEnd_1176957 604344650673856884024779 := by
  unfold tailWord_1176957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927148397093272097625125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28618098931395514731750083 42927148397093272097625125)
  ·
    refine ⟨8048840324454988518304711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42927148397093272097625125 8048840324454988518304711)
    ·
      refine ⟨12073260486682482777457067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048840324454988518304711 12073260486682482777457067)
      ·
        refine ⟨18109890730023724166185601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12073260486682482777457067 18109890730023724166185601)
        ·
          refine ⟨13582418047517793124639201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18109890730023724166185601 13582418047517793124639201)
          ·
            refine ⟨10186813535638344843479401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13582418047517793124639201 10186813535638344843479401)
            ·
              refine ⟨7640110151728758632609551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10186813535638344843479401 7640110151728758632609551)
              ·
                refine ⟨11460165227593137948914327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640110151728758632609551 11460165227593137948914327)
                ·
                  refine ⟨17190247841389706923371491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460165227593137948914327 17190247841389706923371491)
                  ·
                    refine ⟨25785371762084560385057237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17190247841389706923371491 25785371762084560385057237)
                    ·
                      refine ⟨604344650673856884024779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25785371762084560385057237 604344650673856884024779)
                      ·
                        rfl

theorem cell23_1176957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1176957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176957 prefixEnd_1176957 := by exact prefixLift 1176957
  have htrace : WordTrace (prefixWord ++ tailWord_1176957) baseStart_1176957 baseEnd_1176957 := by
    simpa [prefixWord, tailWord_1176957, baseEnd_1176957] using wordTrace_append hprefix tailTrace_1176957
  have hstable : (prefixWord ++ tailWord_1176957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176957).length < 2 ^ (prefixWord ++ tailWord_1176957).sum := by decide
  have hdescent : baseEnd_1176957 < baseStart_1176957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1176997 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_1176997 : Nat := 118140960795 + 1176997 * 2 ^ 59
def prefixEnd_1176997 : Nat := 4983230072969 + 3 ^ 40 * 1176997 * 2
def baseEnd_1176997 : Nat := 604365189900036727524595

theorem tailTrace_1176997 : CollatzResearch.WordTrace tailWord_1176997 prefixEnd_1176997 604365189900036727524595 := by
  unfold tailWord_1176997
  simp only [CollatzResearch.WordTrace]
  refine ⟨42928607316948358929081245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28619071544632239286054163 42928607316948358929081245)
  ·
    refine ⟨16098227743855634598405467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42928607316948358929081245 16098227743855634598405467)
    ·
      refine ⟨24147341615783451897608201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16098227743855634598405467 24147341615783451897608201)
      ·
        refine ⟨18110506211837588923206151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24147341615783451897608201 18110506211837588923206151)
        ·
          refine ⟨27165759317756383384809227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18110506211837588923206151 27165759317756383384809227)
          ·
            refine ⟨40748638976634575077213841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27165759317756383384809227 40748638976634575077213841)
            ·
              refine ⟨30561479232475931307910381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40748638976634575077213841 30561479232475931307910381)
              ·
                refine ⟨11460554712178474240466393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30561479232475931307910381 11460554712178474240466393)
                ·
                  refine ⟨8595416034133855680349795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11460554712178474240466393 8595416034133855680349795)
                  ·
                    refine ⟨12893124051200783520524693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8595416034133855680349795 12893124051200783520524693)
                    ·
                      refine ⟨604365189900036727524595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12893124051200783520524693 604365189900036727524595)
                      ·
                        rfl

theorem cell23_1176997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_1176997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1176997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1176997 prefixEnd_1176997 := by exact prefixLift 1176997
  have htrace : WordTrace (prefixWord ++ tailWord_1176997) baseStart_1176997 baseEnd_1176997 := by
    simpa [prefixWord, tailWord_1176997, baseEnd_1176997] using wordTrace_append hprefix tailTrace_1176997
  have hstable : (prefixWord ++ tailWord_1176997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1176997).length < 2 ^ (prefixWord ++ tailWord_1176997).sum := by decide
  have hdescent : baseEnd_1176997 < baseStart_1176997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1176997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177004 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_1177004 : Nat := 118140960795 + 1177004 * 2 ^ 59
def prefixEnd_1177004 : Nat := 4983230072969 + 3 ^ 40 * 1177004 * 2
def baseEnd_1177004 : Nat := 604368784264618200137063

theorem tailTrace_1177004 : CollatzResearch.WordTrace tailWord_1177004 prefixEnd_1177004 604368784264618200137063 := by
  unfold tailWord_1177004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464431313961499562293033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28619241751948666083057377 21464431313961499562293033)
  ·
    refine ⟨16098323485471124671719775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21464431313961499562293033 16098323485471124671719775)
    ·
      refine ⟨24147485228206687007579663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16098323485471124671719775 24147485228206687007579663)
      ·
        refine ⟨36221227842310030511369495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24147485228206687007579663 36221227842310030511369495)
        ·
          refine ⟨54331841763465045767054243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36221227842310030511369495 54331841763465045767054243)
          ·
            refine ⟨81497762645197568650581365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54331841763465045767054243 81497762645197568650581365)
            ·
              refine ⟨7640415247987272060992003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81497762645197568650581365 7640415247987272060992003)
              ·
                refine ⟨11460622871980908091488005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640415247987272060992003 11460622871980908091488005)
                ·
                  refine ⟨2148866788496420267154001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11460622871980908091488005 2148866788496420267154001)
                  ·
                    refine ⟨1611650091372315200365501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2148866788496420267154001 1611650091372315200365501)
                    ·
                      refine ⟨604368784264618200137063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611650091372315200365501 604368784264618200137063)
                      ·
                        rfl

theorem cell23_1177004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_1177004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177004 prefixEnd_1177004 := by exact prefixLift 1177004
  have htrace : WordTrace (prefixWord ++ tailWord_1177004) baseStart_1177004 baseEnd_1177004 := by
    simpa [prefixWord, tailWord_1177004, baseEnd_1177004] using wordTrace_append hprefix tailTrace_1177004
  have hstable : (prefixWord ++ tailWord_1177004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177004).length < 2 ^ (prefixWord ++ tailWord_1177004).sum := by decide
  have hdescent : baseEnd_1177004 < baseStart_1177004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177011 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 1, 4]
def baseStart_1177011 : Nat := 118140960795 + 1177011 * 2 ^ 59
def prefixEnd_1177011 : Nat := 4983230072969 + 3 ^ 40 * 1177011 * 2
def baseEnd_1177011 : Nat := 201457459543066557583177

theorem tailTrace_1177011 : CollatzResearch.WordTrace tailWord_1177011 prefixEnd_1177011 201457459543066557583177 := by
  unfold tailWord_1177011
  simp only [CollatzResearch.WordTrace]
  refine ⟨42929117938897639320090887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28619411959265092880060591 42929117938897639320090887)
  ·
    refine ⟨64393676908346458980136331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42929117938897639320090887 64393676908346458980136331)
    ·
      refine ⟨96590515362519688470204497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64393676908346458980136331 96590515362519688470204497)
      ·
        refine ⟨72442886521889766352653373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96590515362519688470204497 72442886521889766352653373)
        ·
          refine ⟨27166082445708662382245015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72442886521889766352653373 27166082445708662382245015)
          ·
            refine ⟨40749123668562993573367523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27166082445708662382245015 40749123668562993573367523)
            ·
              refine ⟨61123685502844490360051285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40749123668562993573367523 61123685502844490360051285)
              ·
                refine ⟨716293189486458871406851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 61123685502844490360051285 716293189486458871406851)
                ·
                  refine ⟨1074439784229688307110277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716293189486458871406851 1074439784229688307110277)
                  ·
                    refine ⟨201457459543066557583177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1074439784229688307110277 201457459543066557583177)
                    ·
                      rfl

theorem cell23_1177011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 4].length) (baseStart_1177011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177011 prefixEnd_1177011 := by exact prefixLift 1177011
  have htrace : WordTrace (prefixWord ++ tailWord_1177011) baseStart_1177011 baseEnd_1177011 := by
    simpa [prefixWord, tailWord_1177011, baseEnd_1177011] using wordTrace_append hprefix tailTrace_1177011
  have hstable : (prefixWord ++ tailWord_1177011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177011).length < 2 ^ (prefixWord ++ tailWord_1177011).sum := by decide
  have hdescent : baseEnd_1177011 < baseStart_1177011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177027 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1177027 : Nat := 118140960795 + 1177027 * 2 ^ 59
def prefixEnd_1177027 : Nat := 4983230072969 + 3 ^ 40 * 1177027 * 2
def baseEnd_1177027 : Nat := 604380594319671610149457

theorem tailTrace_1177027 : CollatzResearch.WordTrace tailWord_1177027 prefixEnd_1177027 604380594319671610149457 := by
  unfold tailWord_1177027
  simp only [CollatzResearch.WordTrace]
  refine ⟨42929701506839674052673335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28619801004559782701782223 42929701506839674052673335)
  ·
    refine ⟨64394552260259511079010003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42929701506839674052673335 64394552260259511079010003)
    ·
      refine ⟨96591828390389266618515005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64394552260259511079010003 96591828390389266618515005)
      ·
        refine ⟨36221935646395974981943127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96591828390389266618515005 36221935646395974981943127)
        ·
          refine ⟨54332903469593962472914691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36221935646395974981943127 54332903469593962472914691)
          ·
            refine ⟨81499355204390943709372037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54332903469593962472914691 81499355204390943709372037)
            ·
              refine ⟨15281129100823301945507257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81499355204390943709372037 15281129100823301945507257)
              ·
                refine ⟨11460846825617476459130443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15281129100823301945507257 11460846825617476459130443)
                ·
                  refine ⟨17191270238426214688695665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460846825617476459130443 17191270238426214688695665)
                  ·
                    refine ⟨12893452678819661016521749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17191270238426214688695665 12893452678819661016521749)
                    ·
                      refine ⟨604380594319671610149457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12893452678819661016521749 604380594319671610149457)
                      ·
                        rfl

theorem cell23_1177027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1177027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177027 prefixEnd_1177027 := by exact prefixLift 1177027
  have htrace : WordTrace (prefixWord ++ tailWord_1177027) baseStart_1177027 baseEnd_1177027 := by
    simpa [prefixWord, tailWord_1177027, baseEnd_1177027] using wordTrace_append hprefix tailTrace_1177027
  have hstable : (prefixWord ++ tailWord_1177027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177027).length < 2 ^ (prefixWord ++ tailWord_1177027).sum := by decide
  have hdescent : baseEnd_1177027 < baseStart_1177027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177047 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1177047 : Nat := 118140960795 + 1177047 * 2 ^ 59
def prefixEnd_1177047 : Nat := 4983230072969 + 3 ^ 40 * 1177047 * 2
def baseEnd_1177047 : Nat := 604390863932761531899365

theorem tailTrace_1177047 : CollatzResearch.WordTrace tailWord_1177047 prefixEnd_1177047 604390863932761531899365 := by
  unfold tailWord_1177047
  simp only [CollatzResearch.WordTrace]
  refine ⟨42930430966767217468401395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28620287311178144978934263 42930430966767217468401395)
  ·
    refine ⟨64395646450150826202602093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42930430966767217468401395 64395646450150826202602093)
    ·
      refine ⟨24148367418806559825975785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64395646450150826202602093 24148367418806559825975785)
      ·
        refine ⟨18111275564104919869481839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24148367418806559825975785 18111275564104919869481839)
        ·
          refine ⟨27166913346157379804222759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18111275564104919869481839 27166913346157379804222759)
          ·
            refine ⟨40750370019236069706334139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27166913346157379804222759 40750370019236069706334139)
            ·
              refine ⟨61125555028854104559501209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40750370019236069706334139 61125555028854104559501209)
              ·
                refine ⟨45844166271640578419625907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61125555028854104559501209 45844166271640578419625907)
                ·
                  refine ⟨68766249407460867629438861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45844166271640578419625907 68766249407460867629438861)
                  ·
                    refine ⟨25787343527797825361039573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68766249407460867629438861 25787343527797825361039573)
                    ·
                      refine ⟨604390863932761531899365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25787343527797825361039573 604390863932761531899365)
                      ·
                        rfl

theorem cell23_1177047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1177047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177047 prefixEnd_1177047 := by exact prefixLift 1177047
  have htrace : WordTrace (prefixWord ++ tailWord_1177047) baseStart_1177047 baseEnd_1177047 := by
    simpa [prefixWord, tailWord_1177047, baseEnd_1177047] using wordTrace_append hprefix tailTrace_1177047
  have hstable : (prefixWord ++ tailWord_1177047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177047).length < 2 ^ (prefixWord ++ tailWord_1177047).sum := by decide
  have hdescent : baseEnd_1177047 < baseStart_1177047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177084 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1177084 : Nat := 118140960795 + 1177084 * 2 ^ 59
def prefixEnd_1177084 : Nat := 4983230072969 + 3 ^ 40 * 1177084 * 2
def baseEnd_1177084 : Nat := 201469954238992629045565

theorem tailTrace_1177084 : CollatzResearch.WordTrace tailWord_1177084 prefixEnd_1177084 201469954238992629045565 := by
  unfold tailWord_1177084
  simp only [CollatzResearch.WordTrace]
  refine ⟨21465890233816586393749153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28621186978422115191665537 21465890233816586393749153)
  ·
    refine ⟨16099417675362439795311865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21465890233816586393749153 16099417675362439795311865)
    ·
      refine ⟨12074563256521829846483899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16099417675362439795311865 12074563256521829846483899)
      ·
        refine ⟨18111844884782744769725849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074563256521829846483899 18111844884782744769725849)
        ·
          refine ⟨13583883663587058577294387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18111844884782744769725849 13583883663587058577294387)
          ·
            refine ⟨20375825495380587865941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583883663587058577294387 20375825495380587865941581)
            ·
              refine ⟨7640934560767720449728093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20375825495380587865941581 7640934560767720449728093)
              ·
                refine ⟨2865350460287895168648035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7640934560767720449728093 2865350460287895168648035)
                ·
                  refine ⟨4298025690431842752972053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865350460287895168648035 4298025690431842752972053)
                  ·
                    refine ⟨201469954238992629045565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4298025690431842752972053 201469954238992629045565)
                    ·
                      rfl

theorem cell23_1177084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1177084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177084 prefixEnd_1177084 := by exact prefixLift 1177084
  have htrace : WordTrace (prefixWord ++ tailWord_1177084) baseStart_1177084 baseEnd_1177084 := by
    simpa [prefixWord, tailWord_1177084, baseEnd_1177084] using wordTrace_append hprefix tailTrace_1177084
  have hstable : (prefixWord ++ tailWord_1177084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177084).length < 2 ^ (prefixWord ++ tailWord_1177084).sum := by decide
  have hdescent : baseEnd_1177084 < baseStart_1177084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177095 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1177095 : Nat := 118140960795 + 1177095 * 2 ^ 59
def prefixEnd_1177095 : Nat := 4983230072969 + 3 ^ 40 * 1177095 * 2
def baseEnd_1177095 : Nat := 604415511004177344099145

theorem tailTrace_1177095 : CollatzResearch.WordTrace tailWord_1177095 prefixEnd_1177095 604415511004177344099145 := by
  unfold tailWord_1177095
  simp only [CollatzResearch.WordTrace]
  refine ⟨42932181670593321666148739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28621454447062214444099159 42932181670593321666148739)
  ·
    refine ⟨64398272505889982499223109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42932181670593321666148739 64398272505889982499223109)
    ·
      refine ⟨12074676094854371718604333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64398272505889982499223109 12074676094854371718604333)
      ·
        refine ⟨4528003535570389394476625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12074676094854371718604333 4528003535570389394476625)
        ·
          refine ⟨3396002651677792045857469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4528003535570389394476625 3396002651677792045857469)
          ·
            refine ⟨1273500994379172017196551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3396002651677792045857469 1273500994379172017196551)
            ·
              refine ⟨1910251491568758025794827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273500994379172017196551 1910251491568758025794827)
              ·
                refine ⟨2865377237353137038692241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910251491568758025794827 2865377237353137038692241)
                ·
                  refine ⟨2149032928014852779019181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865377237353137038692241 2149032928014852779019181)
                  ·
                    refine ⟨805887348005569792132193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149032928014852779019181 805887348005569792132193)
                    ·
                      refine ⟨604415511004177344099145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805887348005569792132193 604415511004177344099145)
                      ·
                        rfl

theorem cell23_1177095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1177095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177095 prefixEnd_1177095 := by exact prefixLift 1177095
  have htrace : WordTrace (prefixWord ++ tailWord_1177095) baseStart_1177095 baseEnd_1177095 := by
    simpa [prefixWord, tailWord_1177095, baseEnd_1177095] using wordTrace_append hprefix tailTrace_1177095
  have hstable : (prefixWord ++ tailWord_1177095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177095).length < 2 ^ (prefixWord ++ tailWord_1177095).sum := by decide
  have hdescent : baseEnd_1177095 < baseStart_1177095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177102 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_1177102 : Nat := 118140960795 + 1177102 * 2 ^ 59
def prefixEnd_1177102 : Nat := 4983230072969 + 3 ^ 40 * 1177102 * 2
def baseEnd_1177102 : Nat := 604419105368758816711613

theorem tailTrace_1177102 : CollatzResearch.WordTrace tailWord_1177102 prefixEnd_1177102 604419105368758816711613 := by
  unfold tailWord_1177102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5366554622695995232706695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28621624654378641241102373 5366554622695995232706695)
  ·
    refine ⟨8049831934043992849060043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5366554622695995232706695 8049831934043992849060043)
    ·
      refine ⟨12074747901065989273590065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049831934043992849060043 12074747901065989273590065)
      ·
        refine ⟨9056060925799491955192549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12074747901065989273590065 9056060925799491955192549)
        ·
          refine ⟨1698011423587404741598603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9056060925799491955192549 1698011423587404741598603)
          ·
            refine ⟨2547017135381107112397905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698011423587404741598603 2547017135381107112397905)
            ·
              refine ⟨1910262851535830334298429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547017135381107112397905 1910262851535830334298429)
              ·
                refine ⟨716348569325936375361911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1910262851535830334298429 716348569325936375361911)
                ·
                  refine ⟨1074522853988904563042867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716348569325936375361911 1074522853988904563042867)
                  ·
                    refine ⟨1611784280983356844564301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074522853988904563042867 1611784280983356844564301)
                    ·
                      refine ⟨604419105368758816711613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611784280983356844564301 604419105368758816711613)
                      ·
                        rfl

theorem cell23_1177102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_1177102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177102 prefixEnd_1177102 := by exact prefixLift 1177102
  have htrace : WordTrace (prefixWord ++ tailWord_1177102) baseStart_1177102 baseEnd_1177102 := by
    simpa [prefixWord, tailWord_1177102, baseEnd_1177102] using wordTrace_append hprefix tailTrace_1177102
  have hstable : (prefixWord ++ tailWord_1177102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177102).length < 2 ^ (prefixWord ++ tailWord_1177102).sum := by decide
  have hdescent : baseEnd_1177102 < baseStart_1177102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177128 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1177128 : Nat := 118140960795 + 1177128 * 2 ^ 59
def prefixEnd_1177128 : Nat := 4983230072969 + 3 ^ 40 * 1177128 * 2
def baseEnd_1177128 : Nat := 604432455865775714986493

theorem tailTrace_1177128 : CollatzResearch.WordTrace tailWord_1177128 prefixEnd_1177128 604432455865775714986493 := by
  unfold tailWord_1177128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21466692639736884151050019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28622256852982512201400025 21466692639736884151050019)
  ·
    refine ⟨32200038959605326226575029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21466692639736884151050019 32200038959605326226575029)
    ·
      refine ⟨3018753652462999333741409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32200038959605326226575029 3018753652462999333741409)
      ·
        refine ⟨2264065239347249500306057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3018753652462999333741409 2264065239347249500306057)
        ·
          refine ⟨1698048929510437125229543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2264065239347249500306057 1698048929510437125229543)
          ·
            refine ⟨2547073394265655687844315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698048929510437125229543 2547073394265655687844315)
            ·
              refine ⟨3820610091398483531766473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547073394265655687844315 3820610091398483531766473)
              ·
                refine ⟨2865457568548862648824855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3820610091398483531766473 2865457568548862648824855)
                ·
                  refine ⟨4298186352823293973237283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865457568548862648824855 4298186352823293973237283)
                  ·
                    refine ⟨6447279529234940959855925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298186352823293973237283 6447279529234940959855925)
                    ·
                      refine ⟨604432455865775714986493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6447279529234940959855925 604432455865775714986493)
                      ·
                        rfl

theorem cell23_1177128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1177128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177128 prefixEnd_1177128 := by exact prefixLift 1177128
  have htrace : WordTrace (prefixWord ++ tailWord_1177128) baseStart_1177128 baseEnd_1177128 := by
    simpa [prefixWord, tailWord_1177128, baseEnd_1177128] using wordTrace_append hprefix tailTrace_1177128
  have hstable : (prefixWord ++ tailWord_1177128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177128).length < 2 ^ (prefixWord ++ tailWord_1177128).sum := by decide
  have hdescent : baseEnd_1177128 < baseStart_1177128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177148 : List Nat := [2, 2, 2, 2, 4, 2, 2, 7]
def baseStart_1177148 : Nat := 118140960795 + 1177148 * 2 ^ 59
def prefixEnd_1177148 : Nat := 4983230072969 + 3 ^ 40 * 1177148 * 2
def baseEnd_1177148 : Nat := 22386767610328356916163

theorem tailTrace_1177148 : CollatzResearch.WordTrace tailWord_1177148 prefixEnd_1177148 22386767610328356916163 := by
  unfold tailWord_1177148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467057369700655858914049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28622743159600874478552065 21467057369700655858914049)
  ·
    refine ⟨16100293027275491894185537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21467057369700655858914049 16100293027275491894185537)
    ·
      refine ⟨12075219770456618920639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16100293027275491894185537 12075219770456618920639153)
      ·
        refine ⟨9056414827842464190479365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12075219770456618920639153 9056414827842464190479365)
        ·
          refine ⟨1698077780220462035714881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9056414827842464190479365 1698077780220462035714881)
          ·
            refine ⟨1273558335165346526786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698077780220462035714881 1273558335165346526786161)
            ·
              refine ⟨955168751374009895089621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273558335165346526786161 955168751374009895089621)
              ·
                refine ⟨22386767610328356916163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 955168751374009895089621 22386767610328356916163)
                ·
                  rfl

theorem cell23_1177148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 7].length) (baseStart_1177148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177148 prefixEnd_1177148 := by exact prefixLift 1177148
  have htrace : WordTrace (prefixWord ++ tailWord_1177148) baseStart_1177148 baseEnd_1177148 := by
    simpa [prefixWord, tailWord_1177148, baseEnd_1177148] using wordTrace_append hprefix tailTrace_1177148
  have hstable : (prefixWord ++ tailWord_1177148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177148).length < 2 ^ (prefixWord ++ tailWord_1177148).sum := by decide
  have hdescent : baseEnd_1177148 < baseStart_1177148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177159 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_1177159 : Nat := 118140960795 + 1177159 * 2 ^ 59
def prefixEnd_1177159 : Nat := 4983230072969 + 3 ^ 40 * 1177159 * 2
def baseEnd_1177159 : Nat := 604448373766065093698851

theorem tailTrace_1177159 : CollatzResearch.WordTrace tailWord_1177159 prefixEnd_1177159 604448373766065093698851 := by
  unfold tailWord_1177159
  simp only [CollatzResearch.WordTrace]
  refine ⟨42934515942361460596478531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28623010628240973730985687 42934515942361460596478531)
  ·
    refine ⟨64401773913542190894717797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42934515942361460596478531 64401773913542190894717797)
    ·
      refine ⟨12075332608789160792759587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64401773913542190894717797 12075332608789160792759587)
      ·
        refine ⟨18112998913183741189139381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12075332608789160792759587 18112998913183741189139381)
        ·
          refine ⟨1698093648110975736481817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18112998913183741189139381 1698093648110975736481817)
          ·
            refine ⟨1273570236083231802361363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698093648110975736481817 1273570236083231802361363)
            ·
              refine ⟨1910355354124847703542045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273570236083231802361363 1910355354124847703542045)
              ·
                refine ⟨716383257796817888828267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1910355354124847703542045 716383257796817888828267)
                ·
                  refine ⟨1074574886695226833242401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716383257796817888828267 1074574886695226833242401)
                  ·
                    refine ⟨805931165021420124931801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1074574886695226833242401 805931165021420124931801)
                    ·
                      refine ⟨604448373766065093698851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805931165021420124931801 604448373766065093698851)
                      ·
                        rfl

theorem cell23_1177159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_1177159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177159 prefixEnd_1177159 := by exact prefixLift 1177159
  have htrace : WordTrace (prefixWord ++ tailWord_1177159) baseStart_1177159 baseEnd_1177159 := by
    simpa [prefixWord, tailWord_1177159, baseEnd_1177159] using wordTrace_append hprefix tailTrace_1177159
  have hstable : (prefixWord ++ tailWord_1177159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177159).length < 2 ^ (prefixWord ++ tailWord_1177159).sum := by decide
  have hdescent : baseEnd_1177159 < baseStart_1177159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177168 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2]
def baseStart_1177168 : Nat := 118140960795 + 1177168 * 2 ^ 59
def prefixEnd_1177168 : Nat := 4983230072969 + 3 ^ 40 * 1177168 * 2
def baseEnd_1177168 : Nat := 604452995091955558486309

theorem tailTrace_1177168 : CollatzResearch.WordTrace tailWord_1177168 prefixEnd_1177168 604452995091955558486309 := by
  unfold tailWord_1177168
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467422099664427566778079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28623229466219236755704105 21467422099664427566778079)
  ·
    refine ⟨32201133149496641350167119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21467422099664427566778079 32201133149496641350167119)
    ·
      refine ⟨48301699724244962025250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32201133149496641350167119 48301699724244962025250679)
      ·
        refine ⟨72452549586367443037876019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48301699724244962025250679 72452549586367443037876019)
        ·
          refine ⟨108678824379551164556814029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72452549586367443037876019 108678824379551164556814029)
          ·
            refine ⟨40754559142331686708805261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108678824379551164556814029 40754559142331686708805261)
            ·
              refine ⟨15282959678374382515801973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40754559142331686708805261 15282959678374382515801973)
              ·
                refine ⟨1432777469847598360856435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15282959678374382515801973 1432777469847598360856435)
                ·
                  refine ⟨2149166204771397541284653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432777469847598360856435 2149166204771397541284653)
                  ·
                    refine ⟨805937326789274077981745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149166204771397541284653 805937326789274077981745)
                    ·
                      refine ⟨604452995091955558486309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805937326789274077981745 604452995091955558486309)
                      ·
                        rfl

theorem cell23_1177168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2].length) (baseStart_1177168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177168 prefixEnd_1177168 := by exact prefixLift 1177168
  have htrace : WordTrace (prefixWord ++ tailWord_1177168) baseStart_1177168 baseEnd_1177168 := by
    simpa [prefixWord, tailWord_1177168, baseEnd_1177168] using wordTrace_append hprefix tailTrace_1177168
  have hstable : (prefixWord ++ tailWord_1177168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177168).length < 2 ^ (prefixWord ++ tailWord_1177168).sum := by decide
  have hdescent : baseEnd_1177168 < baseStart_1177168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177184 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1177184 : Nat := 118140960795 + 1177184 * 2 ^ 59
def prefixEnd_1177184 : Nat := 4983230072969 + 3 ^ 40 * 1177184 * 2
def baseEnd_1177184 : Nat := 604461210782427495886235

theorem tailTrace_1177184 : CollatzResearch.WordTrace tailWord_1177184 prefixEnd_1177184 604461210782427495886235 := by
  unfold tailWord_1177184
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467713883635444933069303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28623618511513926577425737 21467713883635444933069303)
  ·
    refine ⟨32201570825453167399603955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21467713883635444933069303 32201570825453167399603955)
    ·
      refine ⟨48302356238179751099405933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32201570825453167399603955 48302356238179751099405933)
      ·
        refine ⟨18113383589317406662277225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48302356238179751099405933 18113383589317406662277225)
        ·
          refine ⟨13585037691988054996707919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18113383589317406662277225 13585037691988054996707919)
          ·
            refine ⟨20377556537982082495061879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13585037691988054996707919 20377556537982082495061879)
            ·
              refine ⟨30566334806973123742592819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20377556537982082495061879 30566334806973123742592819)
              ·
                refine ⟨45849502210459685613889229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30566334806973123742592819 45849502210459685613889229)
                ·
                  refine ⟨17193563328922382105208461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45849502210459685613889229 17193563328922382105208461)
                  ·
                    refine ⟨6447586248345893289453173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17193563328922382105208461 6447586248345893289453173)
                    ·
                      refine ⟨604461210782427495886235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6447586248345893289453173 604461210782427495886235)
                      ·
                        rfl

theorem cell23_1177184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1177184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177184 prefixEnd_1177184 := by exact prefixLift 1177184
  have htrace : WordTrace (prefixWord ++ tailWord_1177184) baseStart_1177184 baseEnd_1177184 := by
    simpa [prefixWord, tailWord_1177184, baseEnd_1177184] using wordTrace_append hprefix tailTrace_1177184
  have hstable : (prefixWord ++ tailWord_1177184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177184).length < 2 ^ (prefixWord ++ tailWord_1177184).sum := by decide
  have hdescent : baseEnd_1177184 < baseStart_1177184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177192 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1177192 : Nat := 118140960795 + 1177192 * 2 ^ 59
def prefixEnd_1177192 : Nat := 4983230072969 + 3 ^ 40 * 1177192 * 2
def baseEnd_1177192 : Nat := 604465318627663464586199

theorem tailTrace_1177192 : CollatzResearch.WordTrace tailWord_1177192 prefixEnd_1177192 604465318627663464586199 := by
  unfold tailWord_1177192
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467859775620953616214915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28623813034161271488286553 21467859775620953616214915)
  ·
    refine ⟨32201789663431430424322373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21467859775620953616214915 32201789663431430424322373)
    ·
      refine ⟨6037835561893393204560445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32201789663431430424322373 6037835561893393204560445)
      ·
        refine ⟨2264188335710022451710167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6037835561893393204560445 2264188335710022451710167)
        ·
          refine ⟨3396282503565033677565251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264188335710022451710167 3396282503565033677565251)
          ·
            refine ⟨5094423755347550516347877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396282503565033677565251 5094423755347550516347877)
            ·
              refine ⟨955204454127665721815227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5094423755347550516347877 955204454127665721815227)
              ·
                refine ⟨1432806681191498582722841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955204454127665721815227 1432806681191498582722841)
                ·
                  refine ⟨1074605010893623937042131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1432806681191498582722841 1074605010893623937042131)
                  ·
                    refine ⟨1611907516340435905563197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074605010893623937042131 1611907516340435905563197)
                    ·
                      refine ⟨604465318627663464586199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611907516340435905563197 604465318627663464586199)
                      ·
                        rfl

theorem cell23_1177192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1177192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177192 prefixEnd_1177192 := by exact prefixLift 1177192
  have htrace : WordTrace (prefixWord ++ tailWord_1177192) baseStart_1177192 baseEnd_1177192 := by
    simpa [prefixWord, tailWord_1177192, baseEnd_1177192] using wordTrace_append hprefix tailTrace_1177192
  have hstable : (prefixWord ++ tailWord_1177192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177192).length < 2 ^ (prefixWord ++ tailWord_1177192).sum := by decide
  have hdescent : baseEnd_1177192 < baseStart_1177192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177202 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1177202 : Nat := 118140960795 + 1177202 * 2 ^ 59
def prefixEnd_1177202 : Nat := 4983230072969 + 3 ^ 40 * 1177202 * 2
def baseEnd_1177202 : Nat := 604470453434208425461153

theorem tailTrace_1177202 : CollatzResearch.WordTrace tailWord_1177202 prefixEnd_1177202 604470453434208425461153 := by
  unfold tailWord_1177202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734021070301419735073465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28624056187470452626862573 10734021070301419735073465)
  ·
    refine ⟨8050515802726064801305099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10734021070301419735073465 8050515802726064801305099)
    ·
      refine ⟨12075773704089097201957649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8050515802726064801305099 12075773704089097201957649)
      ·
        refine ⟨9056830278066822901468237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12075773704089097201957649 9056830278066822901468237)
        ·
          refine ⟨3396311354275058588050589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9056830278066822901468237 3396311354275058588050589)
          ·
            refine ⟨1273616757853146970518971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3396311354275058588050589 1273616757853146970518971)
            ·
              refine ⟨1910425136779720455778457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273616757853146970518971 1910425136779720455778457)
              ·
                refine ⟨1432818852584790341833843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910425136779720455778457 1432818852584790341833843)
                ·
                  refine ⟨2149228278877185512750765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432818852584790341833843 2149228278877185512750765)
                  ·
                    refine ⟨805960604578944567281537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149228278877185512750765 805960604578944567281537)
                    ·
                      refine ⟨604470453434208425461153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 805960604578944567281537 604470453434208425461153)
                      ·
                        rfl

theorem cell23_1177202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1177202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177202 prefixEnd_1177202 := by exact prefixLift 1177202
  have htrace : WordTrace (prefixWord ++ tailWord_1177202) baseStart_1177202 baseEnd_1177202 := by
    simpa [prefixWord, tailWord_1177202, baseEnd_1177202] using wordTrace_append hprefix tailTrace_1177202
  have hstable : (prefixWord ++ tailWord_1177202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177202).length < 2 ^ (prefixWord ++ tailWord_1177202).sum := by decide
  have hdescent : baseEnd_1177202 < baseStart_1177202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177248 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1177248 : Nat := 118140960795 + 1177248 * 2 ^ 59
def prefixEnd_1177248 : Nat := 4983230072969 + 3 ^ 40 * 1177248 * 2
def baseEnd_1177248 : Nat := 604494073544315245485941

theorem tailTrace_1177248 : CollatzResearch.WordTrace tailWord_1177248 prefixEnd_1177248 604494073544315245485941 := by
  unfold tailWord_1177248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468881019519514398234199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28625174692692685864312265 21468881019519514398234199)
  ·
    refine ⟨32203321529279271597351299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21468881019519514398234199 32203321529279271597351299)
    ·
      refine ⟨48304982293918907396026949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32203321529279271597351299 48304982293918907396026949)
      ·
        refine ⟨9057184180109795136755053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48304982293918907396026949 9057184180109795136755053)
        ·
          refine ⟨3396444067541173176283145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9057184180109795136755053 3396444067541173176283145)
          ·
            refine ⟨2547333050655879882212359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396444067541173176283145 2547333050655879882212359)
            ·
              refine ⟨3820999575983819823318539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547333050655879882212359 3820999575983819823318539)
              ·
                refine ⟨5731499363975729734977809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820999575983819823318539 5731499363975729734977809)
                ·
                  refine ⟨4298624522981797301233357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731499363975729734977809 4298624522981797301233357)
                  ·
                    refine ⟨1611984196118173987962509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4298624522981797301233357 1611984196118173987962509)
                    ·
                      refine ⟨604494073544315245485941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1611984196118173987962509 604494073544315245485941)
                      ·
                        rfl

theorem cell23_1177248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1177248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177248 prefixEnd_1177248 := by exact prefixLift 1177248
  have htrace : WordTrace (prefixWord ++ tailWord_1177248) baseStart_1177248 baseEnd_1177248 := by
    simpa [prefixWord, tailWord_1177248, baseEnd_1177248] using wordTrace_append hprefix tailTrace_1177248
  have hstable : (prefixWord ++ tailWord_1177248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177248).length < 2 ^ (prefixWord ++ tailWord_1177248).sum := by decide
  have hdescent : baseEnd_1177248 < baseStart_1177248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177288 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_1177288 : Nat := 118140960795 + 1177288 * 2 ^ 59
def prefixEnd_1177288 : Nat := 4983230072969 + 3 ^ 40 * 1177288 * 2
def baseEnd_1177288 : Nat := 604514612770495088985757

theorem tailTrace_1177288 : CollatzResearch.WordTrace tailWord_1177288 prefixEnd_1177288 604514612770495088985757 := by
  unfold tailWord_1177288
  simp only [CollatzResearch.WordTrace]
  refine ⟨21469610479447057813962259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28626147305929410418616345 21469610479447057813962259)
  ·
    refine ⟨32204415719170586720943389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21469610479447057813962259 32204415719170586720943389)
    ·
      refine ⟨12076655894688970020353771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32204415719170586720943389 12076655894688970020353771)
      ·
        refine ⟨18114983842033455030530657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076655894688970020353771 18114983842033455030530657)
        ·
          refine ⟨13586237881525091272897993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18114983842033455030530657 13586237881525091272897993)
          ·
            refine ⟨10189678411143818454673495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13586237881525091272897993 10189678411143818454673495)
            ·
              refine ⟨15284517616715727682010243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10189678411143818454673495 15284517616715727682010243)
              ·
                refine ⟨22926776425073591523015365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15284517616715727682010243 22926776425073591523015365)
                ·
                  refine ⟨4298770579701298410565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22926776425073591523015365 4298770579701298410565381)
                  ·
                    refine ⟨806019483693993451981009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298770579701298410565381 806019483693993451981009)
                    ·
                      refine ⟨604514612770495088985757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806019483693993451981009 604514612770495088985757)
                      ·
                        rfl

theorem cell23_1177288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_1177288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177288 prefixEnd_1177288 := by exact prefixLift 1177288
  have htrace : WordTrace (prefixWord ++ tailWord_1177288) baseStart_1177288 baseEnd_1177288 := by
    simpa [prefixWord, tailWord_1177288, baseEnd_1177288] using wordTrace_append hprefix tailTrace_1177288
  have hstable : (prefixWord ++ tailWord_1177288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177288).length < 2 ^ (prefixWord ++ tailWord_1177288).sum := by decide
  have hdescent : baseEnd_1177288 < baseStart_1177288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177321 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_1177321 : Nat := 118140960795 + 1177321 * 2 ^ 59
def prefixEnd_1177321 : Nat := 4983230072969 + 3 ^ 40 * 1177321 * 2
def baseEnd_1177321 : Nat := 604531557632093459873105

theorem tailTrace_1177321 : CollatzResearch.WordTrace tailWord_1177321 prefixEnd_1177321 604531557632093459873105 := by
  unfold tailWord_1177321
  simp only [CollatzResearch.WordTrace]
  refine ⟨42940424567774562263875817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28626949711849708175917211 42940424567774562263875817)
  ·
    refine ⟨32205318425830921697906863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42940424567774562263875817 32205318425830921697906863)
    ·
      refine ⟨48307977638746382546860295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32205318425830921697906863 48307977638746382546860295)
      ·
        refine ⟨72461966458119573820290443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48307977638746382546860295 72461966458119573820290443)
        ·
          refine ⟨108692949687179360730435665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72461966458119573820290443 108692949687179360730435665)
          ·
            refine ⟨81519712265384520547826749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108692949687179360730435665 81519712265384520547826749)
            ·
              refine ⟨30569892099519195205435031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81519712265384520547826749 30569892099519195205435031)
              ·
                refine ⟨45854838149278792808152547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30569892099519195205435031 45854838149278792808152547)
                ·
                  refine ⟨68782257223918189212228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45854838149278792808152547 68782257223918189212228821)
                  ·
                    refine ⟨1612084153685582559661613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68782257223918189212228821 1612084153685582559661613)
                    ·
                      refine ⟨604531557632093459873105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612084153685582559661613 604531557632093459873105)
                      ·
                        rfl

theorem cell23_1177321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_1177321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177321 prefixEnd_1177321 := by exact prefixLift 1177321
  have htrace : WordTrace (prefixWord ++ tailWord_1177321) baseStart_1177321 baseEnd_1177321 := by
    simpa [prefixWord, tailWord_1177321, baseEnd_1177321] using wordTrace_append hprefix tailTrace_1177321
  have hstable : (prefixWord ++ tailWord_1177321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177321).length < 2 ^ (prefixWord ++ tailWord_1177321).sum := by decide
  have hdescent : baseEnd_1177321 < baseStart_1177321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177342 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1177342 : Nat := 118140960795 + 1177342 * 2 ^ 59
def prefixEnd_1177342 : Nat := 4983230072969 + 3 ^ 40 * 1177342 * 2
def baseEnd_1177342 : Nat := 604542340725837877710509

theorem tailTrace_1177342 : CollatzResearch.WordTrace tailWord_1177342 prefixEnd_1177342 604542340725837877710509 := by
  unfold tailWord_1177342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367648812587310356298785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28627460333798988566926853 5367648812587310356298785)
  ·
    refine ⟨4025736609440482767224089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367648812587310356298785 4025736609440482767224089)
    ·
      refine ⟨3019302457080362075418067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4025736609440482767224089 3019302457080362075418067)
      ·
        refine ⟨4528953685620543113127101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019302457080362075418067 4528953685620543113127101)
        ·
          refine ⟨1698357632107703667422663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4528953685620543113127101 1698357632107703667422663)
          ·
            refine ⟨2547536448161555501133995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698357632107703667422663 2547536448161555501133995)
            ·
              refine ⟨3821304672242333251700993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547536448161555501133995 3821304672242333251700993)
              ·
                refine ⟨2865978504181749938775745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821304672242333251700993 2865978504181749938775745)
                ·
                  refine ⟨2149483878136312454081809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865978504181749938775745 2149483878136312454081809)
                  ·
                    refine ⟨1612112908602234340561357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2149483878136312454081809 1612112908602234340561357)
                    ·
                      refine ⟨604542340725837877710509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612112908602234340561357 604542340725837877710509)
                      ·
                        rfl

theorem cell23_1177342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1177342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177342 prefixEnd_1177342 := by exact prefixLift 1177342
  have htrace : WordTrace (prefixWord ++ tailWord_1177342) baseStart_1177342 baseEnd_1177342 := by
    simpa [prefixWord, tailWord_1177342, baseEnd_1177342] using wordTrace_append hprefix tailTrace_1177342
  have hstable : (prefixWord ++ tailWord_1177342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177342).length < 2 ^ (prefixWord ++ tailWord_1177342).sum := by decide
  have hdescent : baseEnd_1177342 < baseStart_1177342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177355 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 3]
def baseStart_1177355 : Nat := 118140960795 + 1177355 * 2 ^ 59
def prefixEnd_1177355 : Nat := 4983230072969 + 3 ^ 40 * 1177355 * 2
def baseEnd_1177355 : Nat := 604549015974346326847949

theorem tailTrace_1177355 : CollatzResearch.WordTrace tailWord_1177355 prefixEnd_1177355 604549015974346326847949 := by
  unfold tailWord_1177355
  simp only [CollatzResearch.WordTrace]
  refine ⟨42941664649651386070613519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28627776433100924047075679 42941664649651386070613519)
  ·
    refine ⟨64412496974477079105920279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42941664649651386070613519 64412496974477079105920279)
    ·
      refine ⟨96618745461715618658880419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64412496974477079105920279 96618745461715618658880419)
      ·
        refine ⟨144928118192573427988320629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96618745461715618658880419 144928118192573427988320629)
        ·
          refine ⟨13587011080553758873905059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144928118192573427988320629 13587011080553758873905059)
          ·
            refine ⟨20380516620830638310857589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587011080553758873905059 20380516620830638310857589)
            ·
              refine ⟨1910673433202872341642899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20380516620830638310857589 1910673433202872341642899)
              ·
                refine ⟨2866010149804308512464349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910673433202872341642899 2866010149804308512464349)
                ·
                  refine ⟨1074753806176615692174131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2866010149804308512464349 1074753806176615692174131)
                  ·
                    refine ⟨1612130709264923538261197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074753806176615692174131 1612130709264923538261197)
                    ·
                      refine ⟨604549015974346326847949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612130709264923538261197 604549015974346326847949)
                      ·
                        rfl

theorem cell23_1177355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 3].length) (baseStart_1177355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177355 prefixEnd_1177355 := by exact prefixLift 1177355
  have htrace : WordTrace (prefixWord ++ tailWord_1177355) baseStart_1177355 baseEnd_1177355 := by
    simpa [prefixWord, tailWord_1177355, baseEnd_1177355] using wordTrace_append hprefix tailTrace_1177355
  have hstable : (prefixWord ++ tailWord_1177355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177355).length < 2 ^ (prefixWord ++ tailWord_1177355).sum := by decide
  have hdescent : baseEnd_1177355 < baseStart_1177355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177361 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_1177361 : Nat := 118140960795 + 1177361 * 2 ^ 59
def prefixEnd_1177361 : Nat := 4983230072969 + 3 ^ 40 * 1177361 * 2
def baseEnd_1177361 : Nat := 604552096858273303372921

theorem tailTrace_1177361 : CollatzResearch.WordTrace tailWord_1177361 prefixEnd_1177361 604552096858273303372921 := by
  unfold tailWord_1177361
  simp only [CollatzResearch.WordTrace]
  refine ⟨42941883487629649095331937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28627922325086432730221291 42941883487629649095331937)
  ·
    refine ⟨32206412615722236821498953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42941883487629649095331937 32206412615722236821498953)
    ·
      refine ⟨24154809461791677616124215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32206412615722236821498953 24154809461791677616124215)
      ·
        refine ⟨36232214192687516424186323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24154809461791677616124215 36232214192687516424186323)
        ·
          refine ⟨54348321289031274636279485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36232214192687516424186323 54348321289031274636279485)
          ·
            refine ⟨20380620483386727988604807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54348321289031274636279485 20380620483386727988604807)
            ·
              refine ⟨30570930725080091982907211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20380620483386727988604807 30570930725080091982907211)
              ·
                refine ⟨45856396087620137974360817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30570930725080091982907211 45856396087620137974360817)
                ·
                  refine ⟨34392297065715103480770613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45856396087620137974360817 34392297065715103480770613)
                  ·
                    refine ⟨3224277849910790951322245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34392297065715103480770613 3224277849910790951322245)
                    ·
                      refine ⟨604552096858273303372921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3224277849910790951322245 604552096858273303372921)
                      ·
                        rfl

theorem cell23_1177361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_1177361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177361 prefixEnd_1177361 := by exact prefixLift 1177361
  have htrace : WordTrace (prefixWord ++ tailWord_1177361) baseStart_1177361 baseEnd_1177361 := by
    simpa [prefixWord, tailWord_1177361, baseEnd_1177361] using wordTrace_append hprefix tailTrace_1177361
  have hstable : (prefixWord ++ tailWord_1177361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177361).length < 2 ^ (prefixWord ++ tailWord_1177361).sum := by decide
  have hdescent : baseEnd_1177361 < baseStart_1177361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177362 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_1177362 : Nat := 118140960795 + 1177362 * 2 ^ 59
def prefixEnd_1177362 : Nat := 4983230072969 + 3 ^ 40 * 1177362 * 2
def baseEnd_1177362 : Nat := 67172512259880866606713

theorem tailTrace_1177362 : CollatzResearch.WordTrace tailWord_1177362 prefixEnd_1177362 67172512259880866606713 := by
  unfold tailWord_1177362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10735479990156506566529585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28627946640417350844078893 10735479990156506566529585)
  ·
    refine ⟨8051609992617379924897189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10735479990156506566529585 8051609992617379924897189)
    ·
      refine ⟨1509676873615758735918223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8051609992617379924897189 1509676873615758735918223)
      ·
        refine ⟨2264515310423638103877335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509676873615758735918223 2264515310423638103877335)
        ·
          refine ⟨3396772965635457155816003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264515310423638103877335 3396772965635457155816003)
          ·
            refine ⟨5095159448453185733724005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396772965635457155816003 5095159448453185733724005)
            ·
              refine ⟨955342396584972325073251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5095159448453185733724005 955342396584972325073251)
              ·
                refine ⟨1433013594877458487609877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955342396584972325073251 1433013594877458487609877)
                ·
                  refine ⟨67172512259880866606713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1433013594877458487609877 67172512259880866606713)
                  ·
                    rfl

theorem cell23_1177362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_1177362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177362 prefixEnd_1177362 := by exact prefixLift 1177362
  have htrace : WordTrace (prefixWord ++ tailWord_1177362) baseStart_1177362 baseEnd_1177362 := by
    simpa [prefixWord, tailWord_1177362, baseEnd_1177362] using wordTrace_append hprefix tailTrace_1177362
  have hstable : (prefixWord ++ tailWord_1177362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177362).length < 2 ^ (prefixWord ++ tailWord_1177362).sum := by decide
  have hdescent : baseEnd_1177362 < baseStart_1177362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177388 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_1177388 : Nat := 118140960795 + 1177388 * 2 ^ 59
def prefixEnd_1177388 : Nat := 4983230072969 + 3 ^ 40 * 1177388 * 2
def baseEnd_1177388 : Nat := 201521986945314899245099

theorem tailTrace_1177388 : CollatzResearch.WordTrace tailWord_1177388 prefixEnd_1177388 201521986945314899245099 := by
  unfold tailWord_1177388
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471434129265916353282409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28628578839021221804376545 21471434129265916353282409)
  ·
    refine ⟨16103575596949437264961807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21471434129265916353282409 16103575596949437264961807)
    ·
      refine ⟨24155363395424155897442711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103575596949437264961807 24155363395424155897442711)
      ·
        refine ⟨36233045093136233846164067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24155363395424155897442711 36233045093136233846164067)
        ·
          refine ⟨54349567639704350769246101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36233045093136233846164067 54349567639704350769246101)
          ·
            refine ⟨2547635983111141442308411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54349567639704350769246101 2547635983111141442308411)
            ·
              refine ⟨3821453974666712163462617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547635983111141442308411 3821453974666712163462617)
              ·
                refine ⟨2866090481000034122596963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821453974666712163462617 2866090481000034122596963)
                ·
                  refine ⟨4299135721500051183895445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866090481000034122596963 4299135721500051183895445)
                  ·
                    refine ⟨201521986945314899245099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4299135721500051183895445 201521986945314899245099)
                    ·
                      rfl

theorem cell23_1177388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_1177388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177388 prefixEnd_1177388 := by exact prefixLift 1177388
  have htrace : WordTrace (prefixWord ++ tailWord_1177388) baseStart_1177388 baseEnd_1177388 := by
    simpa [prefixWord, tailWord_1177388, baseEnd_1177388] using wordTrace_append hprefix tailTrace_1177388
  have hstable : (prefixWord ++ tailWord_1177388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177388).length < 2 ^ (prefixWord ++ tailWord_1177388).sum := by decide
  have hdescent : baseEnd_1177388 < baseStart_1177388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177406 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_1177406 : Nat := 118140960795 + 1177406 * 2 ^ 59
def prefixEnd_1177406 : Nat := 4983230072969 + 3 ^ 40 * 1177406 * 2
def baseEnd_1177406 : Nat := 604575203487725627310215

theorem tailTrace_1177406 : CollatzResearch.WordTrace tailWord_1177406 prefixEnd_1177406 604575203487725627310215 := by
  unfold tailWord_1177406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367940596558327722590009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28629016514977747853813381 5367940596558327722590009)
  ·
    refine ⟨4025955447418745791942507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367940596558327722590009 4025955447418745791942507)
    ·
      refine ⟨6038933171128118687913761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025955447418745791942507 6038933171128118687913761)
      ·
        refine ⟨4529199878346089015935321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038933171128118687913761 4529199878346089015935321)
        ·
          refine ⟨3396899908759566761951491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529199878346089015935321 3396899908759566761951491)
          ·
            refine ⟨5095349863139350142927237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396899908759566761951491 5095349863139350142927237)
            ·
              refine ⟨955378099338628151798857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5095349863139350142927237 955378099338628151798857)
              ·
                refine ⟨716533574503971113849143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 955378099338628151798857 716533574503971113849143)
                ·
                  refine ⟨1074800361755956670773715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716533574503971113849143 1074800361755956670773715)
                  ·
                    refine ⟨1612200542633935006160573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074800361755956670773715 1612200542633935006160573)
                    ·
                      refine ⟨604575203487725627310215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612200542633935006160573 604575203487725627310215)
                      ·
                        rfl

theorem cell23_1177406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_1177406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177406 prefixEnd_1177406 := by exact prefixLift 1177406
  have htrace : WordTrace (prefixWord ++ tailWord_1177406) baseStart_1177406 baseEnd_1177406 := by
    simpa [prefixWord, tailWord_1177406, baseEnd_1177406] using wordTrace_append hprefix tailTrace_1177406
  have hstable : (prefixWord ++ tailWord_1177406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177406).length < 2 ^ (prefixWord ++ tailWord_1177406).sum := by decide
  have hdescent : baseEnd_1177406 < baseStart_1177406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177425 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_1177425 : Nat := 118140960795 + 1177425 * 2 ^ 59
def prefixEnd_1177425 : Nat := 4983230072969 + 3 ^ 40 * 1177425 * 2
def baseEnd_1177425 : Nat := 604584959620161052972627

theorem tailTrace_1177425 : CollatzResearch.WordTrace tailWord_1177425 prefixEnd_1177425 604584959620161052972627 := by
  unfold tailWord_1177425
  simp only [CollatzResearch.WordTrace]
  refine ⟨42944217759397788025661729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28629478506265192017107819 42944217759397788025661729)
  ·
    refine ⟨32208163319548341019246297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42944217759397788025661729 32208163319548341019246297)
    ·
      refine ⟨24156122489661255764434723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32208163319548341019246297 24156122489661255764434723)
      ·
        refine ⟨36234183734491883646652085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24156122489661255764434723 36234183734491883646652085)
        ·
          refine ⟨3396954725108614091873633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36234183734491883646652085 3396954725108614091873633)
          ·
            refine ⟨2547716043831460568905225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396954725108614091873633 2547716043831460568905225)
            ·
              refine ⟨1910787032873595426678919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547716043831460568905225 1910787032873595426678919)
              ·
                refine ⟨2866180549310393140018379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910787032873595426678919 2866180549310393140018379)
                ·
                  refine ⟨4299270823965589710027569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866180549310393140018379 4299270823965589710027569)
                  ·
                    refine ⟨3224453117974192282520677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299270823965589710027569 3224453117974192282520677)
                    ·
                      refine ⟨604584959620161052972627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3224453117974192282520677 604584959620161052972627)
                      ·
                        rfl

theorem cell23_1177425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_1177425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177425 prefixEnd_1177425 := by exact prefixLift 1177425
  have htrace : WordTrace (prefixWord ++ tailWord_1177425) baseStart_1177425 baseEnd_1177425 := by
    simpa [prefixWord, tailWord_1177425, baseEnd_1177425] using wordTrace_append hprefix tailTrace_1177425
  have hstable : (prefixWord ++ tailWord_1177425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177425).length < 2 ^ (prefixWord ++ tailWord_1177425).sum := by decide
  have hdescent : baseEnd_1177425 < baseStart_1177425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177445 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1177445 : Nat := 118140960795 + 1177445 * 2 ^ 59
def prefixEnd_1177445 : Nat := 4983230072969 + 3 ^ 40 * 1177445 * 2
def baseEnd_1177445 : Nat := 604595229233250974722535

theorem tailTrace_1177445 : CollatzResearch.WordTrace tailWord_1177445 prefixEnd_1177445 604595229233250974722535 := by
  unfold tailWord_1177445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42944947219325331441389789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28629964812883554294259859 42944947219325331441389789)
  ·
    refine ⟨16104355207246999290521171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42944947219325331441389789 16104355207246999290521171)
    ·
      refine ⟨24156532810870498935781757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16104355207246999290521171 24156532810870498935781757)
      ·
        refine ⟨9058699804076437100918159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24156532810870498935781757 9058699804076437100918159)
        ·
          refine ⟨13588049706114655651377239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058699804076437100918159 13588049706114655651377239)
          ·
            refine ⟨20382074559171983477065859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13588049706114655651377239 20382074559171983477065859)
            ·
              refine ⟨30573111838757975215598789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20382074559171983477065859 30573111838757975215598789)
              ·
                refine ⟨5732458469767120352924773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30573111838757975215598789 5732458469767120352924773)
                ·
                  refine ⟨1074835963081335066173395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5732458469767120352924773 1074835963081335066173395)
                  ·
                    refine ⟨1612253944622002599260093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1074835963081335066173395 1612253944622002599260093)
                    ·
                      refine ⟨604595229233250974722535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612253944622002599260093 604595229233250974722535)
                      ·
                        rfl

theorem cell23_1177445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1177445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177445 prefixEnd_1177445 := by exact prefixLift 1177445
  have htrace : WordTrace (prefixWord ++ tailWord_1177445) baseStart_1177445 baseEnd_1177445 := by
    simpa [prefixWord, tailWord_1177445, baseEnd_1177445] using wordTrace_append hprefix tailTrace_1177445
  have hstable : (prefixWord ++ tailWord_1177445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177445).length < 2 ^ (prefixWord ++ tailWord_1177445).sum := by decide
  have hdescent : baseEnd_1177445 < baseStart_1177445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177479 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_1177479 : Nat := 118140960795 + 1177479 * 2 ^ 59
def prefixEnd_1177479 : Nat := 4983230072969 + 3 ^ 40 * 1177479 * 2
def baseEnd_1177479 : Nat := 604612687575503841697379

theorem tailTrace_1177479 : CollatzResearch.WordTrace tailWord_1177479 prefixEnd_1177479 604612687575503841697379 := by
  unfold tailWord_1177479
  simp only [CollatzResearch.WordTrace]
  refine ⟨42946187301202155248127491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28630791534134770165418327 42946187301202155248127491)
  ·
    refine ⟨64419280951803232872191237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42946187301202155248127491 64419280951803232872191237)
    ·
      refine ⟨12078615178463106163535857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64419280951803232872191237 12078615178463106163535857)
      ·
        refine ⟨9058961383847329622651893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12078615178463106163535857 9058961383847329622651893)
        ·
          refine ⟨849277629735687152123615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9058961383847329622651893 849277629735687152123615)
          ·
            refine ⟨1273916444603530728185423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849277629735687152123615 1273916444603530728185423)
            ·
              refine ⟨1910874666905296092278135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273916444603530728185423 1910874666905296092278135)
              ·
                refine ⟨2866312000357944138417203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910874666905296092278135 2866312000357944138417203)
                ·
                  refine ⟨4299468000536916207625805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866312000357944138417203 4299468000536916207625805)
                  ·
                    refine ⟨1612300500201343577859677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4299468000536916207625805 1612300500201343577859677)
                    ·
                      refine ⟨604612687575503841697379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612300500201343577859677 604612687575503841697379)
                      ·
                        rfl

theorem cell23_1177479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_1177479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177479 prefixEnd_1177479 := by exact prefixLift 1177479
  have htrace : WordTrace (prefixWord ++ tailWord_1177479) baseStart_1177479 baseEnd_1177479 := by
    simpa [prefixWord, tailWord_1177479, baseEnd_1177479] using wordTrace_append hprefix tailTrace_1177479
  have hstable : (prefixWord ++ tailWord_1177479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177479).length < 2 ^ (prefixWord ++ tailWord_1177479).sum := by decide
  have hdescent : baseEnd_1177479 < baseStart_1177479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_1177488 : Nat := 118140960795 + 1177488 * 2 ^ 59
def prefixEnd_1177488 : Nat := 4983230072969 + 3 ^ 40 * 1177488 * 2
def baseEnd_1177488 : Nat := 604617308901394306484837

theorem tailTrace_1177488 : CollatzResearch.WordTrace tailWord_1177488 prefixEnd_1177488 604617308901394306484837 := by
  unfold tailWord_1177488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21473257779084774892602559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28631010372113033190136745 21473257779084774892602559)
  ·
    refine ⟨32209886668627162338903839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21473257779084774892602559 32209886668627162338903839)
    ·
      refine ⟨48314830002940743508355759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32209886668627162338903839 48314830002940743508355759)
      ·
        refine ⟨72472245004411115262533639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48314830002940743508355759 72472245004411115262533639)
        ·
          refine ⟨108708367506616672893800459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72472245004411115262533639 108708367506616672893800459)
          ·
            refine ⟨163062551259925009340700689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108708367506616672893800459 163062551259925009340700689)
            ·
              refine ⟨122296913444943757005525517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163062551259925009340700689 122296913444943757005525517)
              ·
                refine ⟨45861342541853908877072069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122296913444943757005525517 45861342541853908877072069)
                ·
                  refine ⟨8599001726597607914451013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45861342541853908877072069 8599001726597607914451013)
                  ·
                    refine ⟨1612312823737051483959565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8599001726597607914451013 1612312823737051483959565)
                    ·
                      refine ⟨604617308901394306484837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612312823737051483959565 604617308901394306484837)
                      ·
                        rfl

theorem cell23_1177488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_1177488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177488 prefixEnd_1177488 := by exact prefixLift 1177488
  have htrace : WordTrace (prefixWord ++ tailWord_1177488) baseStart_1177488 baseEnd_1177488 := by
    simpa [prefixWord, tailWord_1177488, baseEnd_1177488] using wordTrace_append hprefix tailTrace_1177488
  have hstable : (prefixWord ++ tailWord_1177488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177488).length < 2 ^ (prefixWord ++ tailWord_1177488).sum := by decide
  have hdescent : baseEnd_1177488 < baseStart_1177488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177525 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 7]
def baseStart_1177525 : Nat := 118140960795 + 1177525 * 2 ^ 59
def prefixEnd_1177525 : Nat := 4983230072969 + 3 ^ 40 * 1177525 * 2
def baseEnd_1177525 : Nat := 67181811965067851302463

theorem tailTrace_1177525 : CollatzResearch.WordTrace tailWord_1177525 prefixEnd_1177525 67181811965067851302463 := by
  unfold tailWord_1177525
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947865059035505104302029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28631910039357003402868019 42947865059035505104302029)
  ·
    refine ⟨16105449397138314414113261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42947865059035505104302029 16105449397138314414113261)
    ·
      refine ⟨6039543523926867905292473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16105449397138314414113261 6039543523926867905292473)
      ·
        refine ⟨4529657642945150928969355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6039543523926867905292473 4529657642945150928969355)
        ·
          refine ⟨6794486464417726393454033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529657642945150928969355 6794486464417726393454033)
          ·
            refine ⟨5095864848313294795090525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6794486464417726393454033 5095864848313294795090525)
            ·
              refine ⟨1910949318117485548158947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5095864848313294795090525 1910949318117485548158947)
              ·
                refine ⟨2866423977176228322238421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910949318117485548158947 2866423977176228322238421)
                ·
                  refine ⟨67181811965067851302463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2866423977176228322238421 67181811965067851302463)
                  ·
                    rfl

theorem cell23_1177525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_1177525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177525 prefixEnd_1177525 := by exact prefixLift 1177525
  have htrace : WordTrace (prefixWord ++ tailWord_1177525) baseStart_1177525 baseEnd_1177525 := by
    simpa [prefixWord, tailWord_1177525, baseEnd_1177525] using wordTrace_append hprefix tailTrace_1177525
  have hstable : (prefixWord ++ tailWord_1177525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177525).length < 2 ^ (prefixWord ++ tailWord_1177525).sum := by decide
  have hdescent : baseEnd_1177525 < baseStart_1177525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177545 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 5, 2]
def baseStart_1177545 : Nat := 118140960795 + 1177545 * 2 ^ 59
def prefixEnd_1177545 : Nat := 4983230072969 + 3 ^ 40 * 1177545 * 2
def baseEnd_1177545 : Nat := 604646577298700583472075

theorem tailTrace_1177545 : CollatzResearch.WordTrace tailWord_1177545 prefixEnd_1177545 604646577298700583472075 := by
  unfold tailWord_1177545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42948594518963048520030089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28632396345975365680020059 42948594518963048520030089)
  ·
    refine ⟨32211445889222286390022567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42948594518963048520030089 32211445889222286390022567)
    ·
      refine ⟨48317168833833429585033851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32211445889222286390022567 48317168833833429585033851)
      ·
        refine ⟨72475753250750144377550777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48317168833833429585033851 72475753250750144377550777)
        ·
          refine ⟨54356814938062608283163083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72475753250750144377550777 54356814938062608283163083)
          ·
            refine ⟨81535222407093912424744625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54356814938062608283163083 81535222407093912424744625)
            ·
              refine ⟨61151416805320434318558469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81535222407093912424744625 61151416805320434318558469)
              ·
                refine ⟨11465890650997581434729713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61151416805320434318558469 11465890650997581434729713)
                ·
                  refine ⟨8599417988248186076047285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11465890650997581434729713 8599417988248186076047285)
                  ·
                    refine ⟨806195436398267444629433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8599417988248186076047285 806195436398267444629433)
                    ·
                      refine ⟨604646577298700583472075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 806195436398267444629433 604646577298700583472075)
                      ·
                        rfl

theorem cell23_1177545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5, 2].length) (baseStart_1177545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177545 prefixEnd_1177545 := by exact prefixLift 1177545
  have htrace : WordTrace (prefixWord ++ tailWord_1177545) baseStart_1177545 baseEnd_1177545 := by
    simpa [prefixWord, tailWord_1177545, baseEnd_1177545] using wordTrace_append hprefix tailTrace_1177545
  have hstable : (prefixWord ++ tailWord_1177545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177545).length < 2 ^ (prefixWord ++ tailWord_1177545).sum := by decide
  have hdescent : baseEnd_1177545 < baseStart_1177545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177595 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3]
def baseStart_1177595 : Nat := 118140960795 + 1177595 * 2 ^ 59
def prefixEnd_1177595 : Nat := 4983230072969 + 3 ^ 40 * 1177595 * 2
def baseEnd_1177595 : Nat := 604672251331425387846845

theorem tailTrace_1177595 : CollatzResearch.WordTrace tailWord_1177595 prefixEnd_1177595 604672251331425387846845 := by
  unfold tailWord_1177595
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950418168781907059350239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28633612112521271372900159 42950418168781907059350239)
  ·
    refine ⟨64425627253172860589025359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42950418168781907059350239 64425627253172860589025359)
    ·
      refine ⟨96638440879759290883538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64425627253172860589025359 96638440879759290883538039)
      ·
        refine ⟨144957661319638936325307059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96638440879759290883538039 144957661319638936325307059)
        ·
          refine ⟨217436491979458404487960589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144957661319638936325307059 217436491979458404487960589)
          ·
            refine ⟨81538684492296901682985221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217436491979458404487960589 81538684492296901682985221)
            ·
              refine ⟨15288503342305669065559729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81538684492296901682985221 15288503342305669065559729)
              ·
                refine ⟨11466377506729251799169797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15288503342305669065559729 11466377506729251799169797)
                ·
                  refine ⟨2149945782511734712344337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11466377506729251799169797 2149945782511734712344337)
                  ·
                    refine ⟨1612459336883801034258253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2149945782511734712344337 1612459336883801034258253)
                    ·
                      refine ⟨604672251331425387846845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612459336883801034258253 604672251331425387846845)
                      ·
                        rfl

theorem cell23_1177595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].length) (baseStart_1177595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177595 prefixEnd_1177595 := by exact prefixLift 1177595
  have htrace : WordTrace (prefixWord ++ tailWord_1177595) baseStart_1177595 baseEnd_1177595 := by
    simpa [prefixWord, tailWord_1177595, baseEnd_1177595] using wordTrace_append hprefix tailTrace_1177595
  have hstable : (prefixWord ++ tailWord_1177595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177595).length < 2 ^ (prefixWord ++ tailWord_1177595).sum := by decide
  have hdescent : baseEnd_1177595 < baseStart_1177595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177676 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1177676 : Nat := 118140960795 + 1177676 * 2 ^ 59
def prefixEnd_1177676 : Nat := 4983230072969 + 3 ^ 40 * 1177676 * 2
def baseEnd_1177676 : Nat := 604713843264439570933973

theorem tailTrace_1177676 : CollatzResearch.WordTrace tailWord_1177676 prefixEnd_1177676 604713843264439570933973 := by
  unfold tailWord_1177676
  simp only [CollatzResearch.WordTrace]
  refine ⟨21476686240744228946524441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28635581654325638595365921 21476686240744228946524441)
  ·
    refine ⟨16107514680558171709893331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21476686240744228946524441 16107514680558171709893331)
    ·
      refine ⟨24161272020837257564839997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107514680558171709893331 24161272020837257564839997)
      ·
        refine ⟨9060477007813971586814999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24161272020837257564839997 9060477007813971586814999)
        ·
          refine ⟨13590715511720957380222499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060477007813971586814999 13590715511720957380222499)
          ·
            refine ⟨20386073267581436070333749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13590715511720957380222499 20386073267581436070333749)
            ·
              refine ⟨1911194368835759631593789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20386073267581436070333749 1911194368835759631593789)
              ·
                refine ⟨716697888313409861847671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911194368835759631593789 716697888313409861847671)
                ·
                  refine ⟨1075046832470114792771507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716697888313409861847671 1075046832470114792771507)
                  ·
                    refine ⟨1612570248705172189157261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075046832470114792771507 1612570248705172189157261)
                    ·
                      refine ⟨604713843264439570933973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612570248705172189157261 604713843264439570933973)
                      ·
                        rfl

theorem cell23_1177676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1177676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177676 prefixEnd_1177676 := by exact prefixLift 1177676
  have htrace : WordTrace (prefixWord ++ tailWord_1177676) baseStart_1177676 baseEnd_1177676 := by
    simpa [prefixWord, tailWord_1177676, baseEnd_1177676] using wordTrace_append hprefix tailTrace_1177676
  have hstable : (prefixWord ++ tailWord_1177676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177676).length < 2 ^ (prefixWord ++ tailWord_1177676).sum := by decide
  have hdescent : baseEnd_1177676 < baseStart_1177676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177693 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1177693 : Nat := 118140960795 + 1177693 * 2 ^ 59
def prefixEnd_1177693 : Nat := 4983230072969 + 3 ^ 40 * 1177693 * 2
def baseEnd_1177693 : Nat := 604722572435566004421395

theorem tailTrace_1177693 : CollatzResearch.WordTrace tailWord_1177693 prefixEnd_1177693 604722572435566004421395 := by
  unfold tailWord_1177693
  simp only [CollatzResearch.WordTrace]
  refine ⟨42953992522426869796417733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28635995014951246530945155 42953992522426869796417733)
  ·
    refine ⟨8053873597955038086828325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42953992522426869796417733 8053873597955038086828325)
    ·
      refine ⟨1510101299616569641280311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8053873597955038086828325 1510101299616569641280311)
      ·
        refine ⟨2265151949424854461920467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510101299616569641280311 2265151949424854461920467)
        ·
          refine ⟨3397727924137281692880701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265151949424854461920467 3397727924137281692880701)
          ·
            refine ⟨1274147971551480634830263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3397727924137281692880701 1274147971551480634830263)
            ·
              refine ⟨1911221957327220952245395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274147971551480634830263 1911221957327220952245395)
              ·
                refine ⟨2866832935990831428368093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911221957327220952245395 2866832935990831428368093)
                ·
                  refine ⟨1075062350996561785638035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2866832935990831428368093 1075062350996561785638035)
                  ·
                    refine ⟨1612593526494842678457053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1075062350996561785638035 1612593526494842678457053)
                    ·
                      refine ⟨604722572435566004421395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612593526494842678457053 604722572435566004421395)
                      ·
                        rfl

theorem cell23_1177693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1177693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177693 prefixEnd_1177693 := by exact prefixLift 1177693
  have htrace : WordTrace (prefixWord ++ tailWord_1177693) baseStart_1177693 baseEnd_1177693 := by
    simpa [prefixWord, tailWord_1177693, baseEnd_1177693] using wordTrace_append hprefix tailTrace_1177693
  have hstable : (prefixWord ++ tailWord_1177693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177693).length < 2 ^ (prefixWord ++ tailWord_1177693).sum := by decide
  have hdescent : baseEnd_1177693 < baseStart_1177693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177695 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1177695 : Nat := 118140960795 + 1177695 * 2 ^ 59
def prefixEnd_1177695 : Nat := 4983230072969 + 3 ^ 40 * 1177695 * 2
def baseEnd_1177695 : Nat := 604723599396874996596385

theorem tailTrace_1177695 : CollatzResearch.WordTrace tailWord_1177695 prefixEnd_1177695 604723599396874996596385 := by
  unfold tailWord_1177695
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954065468419624137990539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28636043645613082758660359 42954065468419624137990539)
  ·
    refine ⟨64431098202629436206985809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42954065468419624137990539 64431098202629436206985809)
    ·
      refine ⟨48323323651972077155239357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64431098202629436206985809 48323323651972077155239357)
      ·
        refine ⟨18121246369489528933214759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48323323651972077155239357 18121246369489528933214759)
        ·
          refine ⟨27181869554234293399822139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18121246369489528933214759 27181869554234293399822139)
          ·
            refine ⟨40772804331351440099733209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27181869554234293399822139 40772804331351440099733209)
            ·
              refine ⟨30579603248513580074799907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40772804331351440099733209 30579603248513580074799907)
              ·
                refine ⟨45869404872770370112199861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30579603248513580074799907 45869404872770370112199861)
                ·
                  refine ⟨4300256706822222198018737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45869404872770370112199861 4300256706822222198018737)
                  ·
                    refine ⟨3225192530116666648514053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300256706822222198018737 3225192530116666648514053)
                    ·
                      refine ⟨604723599396874996596385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3225192530116666648514053 604723599396874996596385)
                      ·
                        rfl

theorem cell23_1177695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1177695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177695 prefixEnd_1177695 := by exact prefixLift 1177695
  have htrace : WordTrace (prefixWord ++ tailWord_1177695) baseStart_1177695 baseEnd_1177695 := by
    simpa [prefixWord, tailWord_1177695, baseEnd_1177695] using wordTrace_append hprefix tailTrace_1177695
  have hstable : (prefixWord ++ tailWord_1177695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177695).length < 2 ^ (prefixWord ++ tailWord_1177695).sum := by decide
  have hdescent : baseEnd_1177695 < baseStart_1177695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177705 : List Nat := [1, 2, 1, 1, 1, 5, 4, 8]
def baseStart_1177705 : Nat := 118140960795 + 1177705 * 2 ^ 59
def prefixEnd_1177705 : Nat := 4983230072969 + 3 ^ 40 * 1177705 * 2
def baseEnd_1177705 : Nat := 22397360526052591017457

theorem tailTrace_1177705 : CollatzResearch.WordTrace tailWord_1177705 prefixEnd_1177705 22397360526052591017457 := by
  unfold tailWord_1177705
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954430198383395845854569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28636286798922263897236379 42954430198383395845854569)
  ·
    refine ⟨32215822648787546884390927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42954430198383395845854569 32215822648787546884390927)
    ·
      refine ⟨48323733973181320326586391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32215822648787546884390927 48323733973181320326586391)
      ·
        refine ⟨72485600959771980489879587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48323733973181320326586391 72485600959771980489879587)
        ·
          refine ⟨108728401439657970734819381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72485600959771980489879587 108728401439657970734819381)
          ·
            refine ⟨10193287634967934756389317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108728401439657970734819381 10193287634967934756389317)
            ·
              refine ⟨1911241431556487766822997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10193287634967934756389317 1911241431556487766822997)
              ·
                refine ⟨22397360526052591017457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1911241431556487766822997 22397360526052591017457)
                ·
                  rfl

theorem cell23_1177705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 8].length) (baseStart_1177705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177705 prefixEnd_1177705 := by exact prefixLift 1177705
  have htrace : WordTrace (prefixWord ++ tailWord_1177705) baseStart_1177705 baseEnd_1177705 := by
    simpa [prefixWord, tailWord_1177705, baseEnd_1177705] using wordTrace_append hprefix tailTrace_1177705
  have hstable : (prefixWord ++ tailWord_1177705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177705).length < 2 ^ (prefixWord ++ tailWord_1177705).sum := by decide
  have hdescent : baseEnd_1177705 < baseStart_1177705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177709 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1177709 : Nat := 118140960795 + 1177709 * 2 ^ 59
def prefixEnd_1177709 : Nat := 4983230072969 + 3 ^ 40 * 1177709 * 2
def baseEnd_1177709 : Nat := 201576929375345980607107

theorem tailTrace_1177709 : CollatzResearch.WordTrace tailWord_1177709 prefixEnd_1177709 201576929375345980607107 := by
  unfold tailWord_1177709
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954576090368904529000181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28636384060245936352666787 42954576090368904529000181)
  ·
    refine ⟨4026991508472084799593767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42954576090368904529000181 4026991508472084799593767)
    ·
      refine ⟨6040487262708127199390651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4026991508472084799593767 6040487262708127199390651)
      ·
        refine ⟨9060730894062190799085977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040487262708127199390651 9060730894062190799085977)
        ·
          refine ⟨6795548170546643099314483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9060730894062190799085977 6795548170546643099314483)
          ·
            refine ⟨10193322255819964648971725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795548170546643099314483 10193322255819964648971725)
            ·
              refine ⟨3822495845932486743364397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10193322255819964648971725 3822495845932486743364397)
              ·
                refine ⟨1433435942224682528761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3822495845932486743364397 1433435942224682528761649)
                ·
                  refine ⟨1075076956668511896571237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1433435942224682528761649 1075076956668511896571237)
                  ·
                    refine ⟨201576929375345980607107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1075076956668511896571237 201576929375345980607107)
                    ·
                      rfl

theorem cell23_1177709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1177709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177709 prefixEnd_1177709 := by exact prefixLift 1177709
  have htrace : WordTrace (prefixWord ++ tailWord_1177709) baseStart_1177709 baseEnd_1177709 := by
    simpa [prefixWord, tailWord_1177709, baseEnd_1177709] using wordTrace_append hprefix tailTrace_1177709
  have hstable : (prefixWord ++ tailWord_1177709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177709).length < 2 ^ (prefixWord ++ tailWord_1177709).sum := by decide
  have hdescent : baseEnd_1177709 < baseStart_1177709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177719 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_1177719 : Nat := 118140960795 + 1177719 * 2 ^ 59
def prefixEnd_1177719 : Nat := 4983230072969 + 3 ^ 40 * 1177719 * 2
def baseEnd_1177719 : Nat := 604735922932582902696275

theorem tailTrace_1177719 : CollatzResearch.WordTrace tailWord_1177719 prefixEnd_1177719 604735922932582902696275 := by
  unfold tailWord_1177719
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954940820332676236864211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28636627213555117491242807 42954940820332676236864211)
  ·
    refine ⟨64432411230499014355296317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42954940820332676236864211 64432411230499014355296317)
    ·
      refine ⟨24162154211437130383236119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64432411230499014355296317 24162154211437130383236119)
      ·
        refine ⟨36243231317155695574854179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24162154211437130383236119 36243231317155695574854179)
        ·
          refine ⟨54364846975733543362281269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36243231317155695574854179 54364846975733543362281269)
          ·
            refine ⟨5096704403975019690213869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54364846975733543362281269 5096704403975019690213869)
            ·
              refine ⟨1911264151490632383830201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5096704403975019690213869 1911264151490632383830201)
              ·
                refine ⟨1433448113617974287872651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911264151490632383830201 1433448113617974287872651)
                ·
                  refine ⟨2150172170426961431808977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433448113617974287872651 2150172170426961431808977)
                  ·
                    refine ⟨1612629127820221073856733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2150172170426961431808977 1612629127820221073856733)
                    ·
                      refine ⟨604735922932582902696275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1612629127820221073856733 604735922932582902696275)
                      ·
                        rfl

theorem cell23_1177719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_1177719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177719 prefixEnd_1177719 := by exact prefixLift 1177719
  have htrace : WordTrace (prefixWord ++ tailWord_1177719) baseStart_1177719 baseEnd_1177719 := by
    simpa [prefixWord, tailWord_1177719, baseEnd_1177719] using wordTrace_append hprefix tailTrace_1177719
  have hstable : (prefixWord ++ tailWord_1177719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177719).length < 2 ^ (prefixWord ++ tailWord_1177719).sum := by decide
  have hdescent : baseEnd_1177719 < baseStart_1177719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177729 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1177729 : Nat := 118140960795 + 1177729 * 2 ^ 59
def prefixEnd_1177729 : Nat := 4983230072969 + 3 ^ 40 * 1177729 * 2
def baseEnd_1177729 : Nat := 604741057739127863571229

theorem tailTrace_1177729 : CollatzResearch.WordTrace tailWord_1177729 prefixEnd_1177729 604741057739127863571229 := by
  unfold tailWord_1177729
  simp only [CollatzResearch.WordTrace]
  refine ⟨42955305550296447944728241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28636870366864298629818827 42955305550296447944728241)
  ·
    refine ⟨32216479162722335958546181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42955305550296447944728241 32216479162722335958546181)
    ·
      refine ⟨6040589843010437992227409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32216479162722335958546181 6040589843010437992227409)
      ·
        refine ⟨4530442382257828494170557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6040589843010437992227409 4530442382257828494170557)
        ·
          refine ⟨1698915893346685685313959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4530442382257828494170557 1698915893346685685313959)
          ·
            refine ⟨2548373840020028527970939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698915893346685685313959 2548373840020028527970939)
            ·
              refine ⟨3822560760030042791956409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548373840020028527970939 3822560760030042791956409)
              ·
                refine ⟨2866920570022532093967307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822560760030042791956409 2866920570022532093967307)
                ·
                  refine ⟨4300380855033798140950961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866920570022532093967307 4300380855033798140950961)
                  ·
                    refine ⟨3225285641275348605713221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300380855033798140950961 3225285641275348605713221)
                    ·
                      refine ⟨604741057739127863571229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3225285641275348605713221 604741057739127863571229)
                      ·
                        rfl

theorem cell23_1177729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1177729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177729 prefixEnd_1177729 := by exact prefixLift 1177729
  have htrace : WordTrace (prefixWord ++ tailWord_1177729) baseStart_1177729 baseEnd_1177729 := by
    simpa [prefixWord, tailWord_1177729, baseEnd_1177729] using wordTrace_append hprefix tailTrace_1177729
  have hstable : (prefixWord ++ tailWord_1177729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177729).length < 2 ^ (prefixWord ++ tailWord_1177729).sum := by decide
  have hdescent : baseEnd_1177729 < baseStart_1177729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177755 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_1177755 : Nat := 118140960795 + 1177755 * 2 ^ 59
def prefixEnd_1177755 : Nat := 4983230072969 + 3 ^ 40 * 1177755 * 2
def baseEnd_1177755 : Nat := 604754408236144761846109

theorem tailTrace_1177755 : CollatzResearch.WordTrace tailWord_1177755 prefixEnd_1177755 604754408236144761846109 := by
  unfold tailWord_1177755
  simp only [CollatzResearch.WordTrace]
  refine ⟨42956253848202254385174719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28637502565468169590116479 42956253848202254385174719)
  ·
    refine ⟨64434380772303381577762079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42956253848202254385174719 64434380772303381577762079)
    ·
      refine ⟨96651571158455072366643119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64434380772303381577762079 96651571158455072366643119)
      ·
        refine ⟨144977356737682608549964679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96651571158455072366643119 144977356737682608549964679)
        ·
          refine ⟨217466035106523912824947019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144977356737682608549964679 217466035106523912824947019)
          ·
            refine ⟨326199052659785869237420529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217466035106523912824947019 326199052659785869237420529)
            ·
              refine ⟨244649289494839401928065397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326199052659785869237420529 244649289494839401928065397)
              ·
                refine ⟨22935870890141193930756131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 244649289494839401928065397 22935870890141193930756131)
                ·
                  refine ⟨34403806335211790896134197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22935870890141193930756131 34403806335211790896134197)
                  ·
                    refine ⟨3225356843926105396512581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34403806335211790896134197 3225356843926105396512581)
                    ·
                      refine ⟨604754408236144761846109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3225356843926105396512581 604754408236144761846109)
                      ·
                        rfl

theorem cell23_1177755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_1177755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177755 prefixEnd_1177755 := by exact prefixLift 1177755
  have htrace : WordTrace (prefixWord ++ tailWord_1177755) baseStart_1177755 baseEnd_1177755 := by
    simpa [prefixWord, tailWord_1177755, baseEnd_1177755] using wordTrace_append hprefix tailTrace_1177755
  have hstable : (prefixWord ++ tailWord_1177755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177755).length < 2 ^ (prefixWord ++ tailWord_1177755).sum := by decide
  have hdescent : baseEnd_1177755 < baseStart_1177755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177802 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1177802 : Nat := 118140960795 + 1177802 * 2 ^ 59
def prefixEnd_1177802 : Nat := 4983230072969 + 3 ^ 40 * 1177802 * 2
def baseEnd_1177802 : Nat := 604778541826906077958393

theorem tailTrace_1177802 : CollatzResearch.WordTrace tailWord_1177802 prefixEnd_1177802 604778541826906077958393 := by
  unfold tailWord_1177802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739492019757995353033915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28638645386021320941423773 10739492019757995353033915)
  ·
    refine ⟨16109238029636993029550873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10739492019757995353033915 16109238029636993029550873)
    ·
      refine ⟨12081928522227744772163155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16109238029636993029550873 12081928522227744772163155)
      ·
        refine ⟨18122892783341617158244733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12081928522227744772163155 18122892783341617158244733)
        ·
          refine ⟨6796084793753106434341775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18122892783341617158244733 6796084793753106434341775)
          ·
            refine ⟨10194127190629659651512663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796084793753106434341775 10194127190629659651512663)
            ·
              refine ⟨15291190785944489477268995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194127190629659651512663 15291190785944489477268995)
              ·
                refine ⟨22936786178916734215903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15291190785944489477268995 22936786178916734215903493)
                ·
                  refine ⟨4300647408546887665481905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22936786178916734215903493 4300647408546887665481905)
                  ·
                    refine ⟨3225485556410165749111429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300647408546887665481905 3225485556410165749111429)
                    ·
                      refine ⟨604778541826906077958393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3225485556410165749111429 604778541826906077958393)
                      ·
                        rfl

theorem cell23_1177802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1177802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177802 prefixEnd_1177802 := by exact prefixLift 1177802
  have htrace : WordTrace (prefixWord ++ tailWord_1177802) baseStart_1177802 baseEnd_1177802 := by
    simpa [prefixWord, tailWord_1177802, baseEnd_1177802] using wordTrace_append hprefix tailTrace_1177802
  have hstable : (prefixWord ++ tailWord_1177802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177802).length < 2 ^ (prefixWord ++ tailWord_1177802).sum := by decide
  have hdescent : baseEnd_1177802 < baseStart_1177802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177846 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1177846 : Nat := 118140960795 + 1177846 * 2 ^ 59
def prefixEnd_1177846 : Nat := 4983230072969 + 3 ^ 40 * 1177846 * 2
def baseEnd_1177846 : Nat := 67200126108411545089799

theorem tailTrace_1177846 : CollatzResearch.WordTrace tailWord_1177846 prefixEnd_1177846 67200126108411545089799 := by
  unfold tailWord_1177846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684973305679536057921087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28639715260581717951158261 2684973305679536057921087)
  ·
    refine ⟨4027459958519304086881631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2684973305679536057921087 4027459958519304086881631)
    ·
      refine ⟨6041189937778956130322447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027459958519304086881631 6041189937778956130322447)
      ·
        refine ⟨9061784906668434195483671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041189937778956130322447 9061784906668434195483671)
        ·
          refine ⟨13592677360002651293225507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9061784906668434195483671 13592677360002651293225507)
          ·
            refine ⟨20389016040003976939838261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13592677360002651293225507 20389016040003976939838261)
            ·
              refine ⟨1911470253750372838109837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20389016040003976939838261 1911470253750372838109837)
              ·
                refine ⟨716801345156389814291189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911470253750372838109837 716801345156389814291189)
                ·
                  refine ⟨67200126108411545089799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 716801345156389814291189 67200126108411545089799)
                  ·
                    rfl

theorem cell23_1177846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1177846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177846 prefixEnd_1177846 := by exact prefixLift 1177846
  have htrace : WordTrace (prefixWord ++ tailWord_1177846) baseStart_1177846 baseEnd_1177846 := by
    simpa [prefixWord, tailWord_1177846, baseEnd_1177846] using wordTrace_append hprefix tailTrace_1177846
  have hstable : (prefixWord ++ tailWord_1177846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177846).length < 2 ^ (prefixWord ++ tailWord_1177846).sum := by decide
  have hdescent : baseEnd_1177846 < baseStart_1177846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177863 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 7]
def baseStart_1177863 : Nat := 118140960795 + 1177863 * 2 ^ 59
def prefixEnd_1177863 : Nat := 4983230072969 + 3 ^ 40 * 1177863 * 2
def baseEnd_1177863 : Nat := 67201096016314482143957

theorem tailTrace_1177863 : CollatzResearch.WordTrace tailWord_1177863 prefixEnd_1177863 67201096016314482143957 := by
  unfold tailWord_1177863
  simp only [CollatzResearch.WordTrace]
  refine ⟨42960192931810988830106243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28640128621207325886737495 42960192931810988830106243)
  ·
    refine ⟨64440289397716483245159365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42960192931810988830106243 64440289397716483245159365)
    ·
      refine ⟨12082554262071840608467381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64440289397716483245159365 12082554262071840608467381)
      ·
        refine ⟨1132739462069235057043817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12082554262071840608467381 1132739462069235057043817)
        ·
          refine ⟨849554596551926292782863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132739462069235057043817 849554596551926292782863)
          ·
            refine ⟨1274331894827889439174295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849554596551926292782863 1274331894827889439174295)
            ·
              refine ⟨1911497842241834158761443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274331894827889439174295 1911497842241834158761443)
              ·
                refine ⟨2867246763362751238142165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911497842241834158761443 2867246763362751238142165)
                ·
                  refine ⟨67201096016314482143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2867246763362751238142165 67201096016314482143957)
                  ·
                    rfl

theorem cell23_1177863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 7].length) (baseStart_1177863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177863 prefixEnd_1177863 := by exact prefixLift 1177863
  have htrace : WordTrace (prefixWord ++ tailWord_1177863) baseStart_1177863 baseEnd_1177863 := by
    simpa [prefixWord, tailWord_1177863, baseEnd_1177863] using wordTrace_append hprefix tailTrace_1177863
  have hstable : (prefixWord ++ tailWord_1177863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177863).length < 2 ^ (prefixWord ++ tailWord_1177863).sum := by decide
  have hdescent : baseEnd_1177863 < baseStart_1177863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177889 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1177889 : Nat := 118140960795 + 1177889 * 2 ^ 59
def prefixEnd_1177889 : Nat := 4983230072969 + 3 ^ 40 * 1177889 * 2
def baseEnd_1177889 : Nat := 201607738214615745856831

theorem tailTrace_1177889 : CollatzResearch.WordTrace tailWord_1177889 prefixEnd_1177889 201607738214615745856831 := by
  unfold tailWord_1177889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42961141229716795270552721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28640760819811196847035147 42961141229716795270552721)
  ·
    refine ⟨32220855922287596452914541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42961141229716795270552721 32220855922287596452914541)
    ·
      refine ⟨12082820970857848669842953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32220855922287596452914541 12082820970857848669842953)
      ·
        refine ⟨9062115728143386502382215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12082820970857848669842953 9062115728143386502382215)
        ·
          refine ⟨13593173592215079753573323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062115728143386502382215 13593173592215079753573323)
          ·
            refine ⟨20389760388322619630359985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13593173592215079753573323 20389760388322619630359985)
            ·
              refine ⟨15292320291241964722769989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20389760388322619630359985 15292320291241964722769989)
              ·
                refine ⟨2867310054607868385519373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15292320291241964722769989 2867310054607868385519373)
                ·
                  refine ⟨1075241270477950644569765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2867310054607868385519373 1075241270477950644569765)
                  ·
                    refine ⟨201607738214615745856831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1075241270477950644569765 201607738214615745856831)
                    ·
                      rfl

theorem cell23_1177889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1177889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177889 prefixEnd_1177889 := by exact prefixLift 1177889
  have htrace : WordTrace (prefixWord ++ tailWord_1177889) baseStart_1177889 baseEnd_1177889 := by
    simpa [prefixWord, tailWord_1177889, baseEnd_1177889] using wordTrace_append hprefix tailTrace_1177889
  have hstable : (prefixWord ++ tailWord_1177889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177889).length < 2 ^ (prefixWord ++ tailWord_1177889).sum := by decide
  have hdescent : baseEnd_1177889 < baseStart_1177889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177919 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 6]
def baseStart_1177919 : Nat := 118140960795 + 1177919 * 2 ^ 59
def prefixEnd_1177919 : Nat := 4983230072969 + 3 ^ 40 * 1177919 * 2
def baseEnd_1177919 : Nat := 67204291007053568910595

theorem tailTrace_1177919 : CollatzResearch.WordTrace tailWord_1177919 prefixEnd_1177919 67204291007053568910595 := by
  unfold tailWord_1177919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42962235419608110394144811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28641490279738740262763207 42962235419608110394144811)
  ·
    refine ⟨64443353129412165591217217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42962235419608110394144811 64443353129412165591217217)
    ·
      refine ⟨48332514847059124193412913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64443353129412165591217217 48332514847059124193412913)
      ·
        refine ⟨36249386135294343145059685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48332514847059124193412913 36249386135294343145059685)
        ·
          refine ⟨6796759900367689339698691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36249386135294343145059685 6796759900367689339698691)
          ·
            refine ⟨10195139850551534009548037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796759900367689339698691 10195139850551534009548037)
            ·
              refine ⟨1911588721978412626790257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10195139850551534009548037 1911588721978412626790257)
              ·
                refine ⟨1433691541483809470092693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911588721978412626790257 1433691541483809470092693)
                ·
                  refine ⟨67204291007053568910595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1433691541483809470092693 67204291007053568910595)
                  ·
                    rfl

theorem cell23_1177919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 6].length) (baseStart_1177919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1177919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1177919 prefixEnd_1177919 := by exact prefixLift 1177919
  have htrace : WordTrace (prefixWord ++ tailWord_1177919) baseStart_1177919 baseEnd_1177919 := by
    simpa [prefixWord, tailWord_1177919, baseEnd_1177919] using wordTrace_append hprefix tailTrace_1177919
  have hstable : (prefixWord ++ tailWord_1177919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177919).length < 2 ^ (prefixWord ++ tailWord_1177919).sum := by decide
  have hdescent : baseEnd_1177919 < baseStart_1177919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
