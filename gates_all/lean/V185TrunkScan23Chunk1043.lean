import V185TrunkScan23Chunk1042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6174597 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_6174597 : Nat := 118140960795 + 6174597 * 2 ^ 59
def prefixEnd_6174597 : Nat := 4983230072969 + 3 ^ 40 * 6174597 * 2
def baseEnd_6174597 : Nat := 1056845369603227864847017

theorem tailTrace_6174597 : CollatzResearch.WordTrace tailWord_6174597 prefixEnd_6174597 1056845369603227864847017 := by
  unfold tailWord_6174597
  simp only [CollatzResearch.WordTrace]
  refine ⟨225206054011497081056714045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150137369340998054037809363 225206054011497081056714045)
  ·
    refine ⟨84452270254311405396267767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225206054011497081056714045 84452270254311405396267767)
    ·
      refine ⟨126678405381467108094401651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84452270254311405396267767 126678405381467108094401651)
      ·
        refine ⟨190017608072200662141602477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126678405381467108094401651 190017608072200662141602477)
        ·
          refine ⟨71256603027075248303100929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190017608072200662141602477 71256603027075248303100929)
          ·
            refine ⟨53442452270306436227325697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71256603027075248303100929 53442452270306436227325697)
            ·
              refine ⟨40081839202729827170494273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53442452270306436227325697 40081839202729827170494273)
              ·
                refine ⟨30061379402047370377870705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40081839202729827170494273 30061379402047370377870705)
                ·
                  refine ⟨22546034551535527783403029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30061379402047370377870705 22546034551535527783403029)
                  ·
                    refine ⟨1056845369603227864847017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22546034551535527783403029 1056845369603227864847017)
                    ·
                      rfl

theorem cell23_6174597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_6174597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174597 prefixEnd_6174597 := by exact prefixLift 6174597
  have htrace : WordTrace (prefixWord ++ tailWord_6174597) baseStart_6174597 baseEnd_6174597 := by
    simpa [prefixWord, tailWord_6174597, baseEnd_6174597] using wordTrace_append hprefix tailTrace_6174597
  have hstable : (prefixWord ++ tailWord_6174597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174597).length < 2 ^ (prefixWord ++ tailWord_6174597).sum := by decide
  have hdescent : baseEnd_6174597 < baseStart_6174597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174599 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_6174599 : Nat := 118140960795 + 6174599 * 2 ^ 59
def prefixEnd_6174599 : Nat := 4983230072969 + 3 ^ 40 * 6174599 * 2
def baseEnd_6174599 : Nat := 3170537135770992586716043

theorem tailTrace_6174599 : CollatzResearch.WordTrace tailWord_6174599 prefixEnd_6174599 3170537135770992586716043 := by
  unfold tailWord_6174599
  simp only [CollatzResearch.WordTrace]
  refine ⟨225206126957489835398286851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150137417971659890265524567 225206126957489835398286851)
  ·
    refine ⟨337809190436234753097430277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225206126957489835398286851 337809190436234753097430277)
    ·
      refine ⟨63339223206794016205768177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337809190436234753097430277 63339223206794016205768177)
      ·
        refine ⟨47504417405095512154326133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63339223206794016205768177 47504417405095512154326133)
        ·
          refine ⟨4453539131727704264468075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47504417405095512154326133 4453539131727704264468075)
          ·
            refine ⟨6680308697591556396702113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453539131727704264468075 6680308697591556396702113)
            ·
              refine ⟨5010231523193667297526585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680308697591556396702113 5010231523193667297526585)
              ·
                refine ⟨3757673642395250473144939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010231523193667297526585 3757673642395250473144939)
                ·
                  refine ⟨5636510463592875709717409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757673642395250473144939 5636510463592875709717409)
                  ·
                    refine ⟨4227382847694656782288057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636510463592875709717409 4227382847694656782288057)
                    ·
                      refine ⟨3170537135770992586716043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227382847694656782288057 3170537135770992586716043)
                      ·
                        rfl

theorem cell23_6174599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_6174599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174599 prefixEnd_6174599 := by exact prefixLift 6174599
  have htrace : WordTrace (prefixWord ++ tailWord_6174599) baseStart_6174599 baseEnd_6174599 := by
    simpa [prefixWord, tailWord_6174599, baseEnd_6174599] using wordTrace_append hprefix tailTrace_6174599
  have hstable : (prefixWord ++ tailWord_6174599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174599).length < 2 ^ (prefixWord ++ tailWord_6174599).sum := by decide
  have hdescent : baseEnd_6174599 < baseStart_6174599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_6174604 : Nat := 118140960795 + 6174604 * 2 ^ 59
def prefixEnd_6174604 : Nat := 4983230072969 + 3 ^ 40 * 6174604 * 2
def baseEnd_6174604 : Nat := 3170539703174265067153519

theorem tailTrace_6174604 : CollatzResearch.WordTrace tailWord_6174604 prefixEnd_6174604 3170539703174265067153519 := by
  unfold tailWord_6174604
  simp only [CollatzResearch.WordTrace]
  refine ⟨112603154661235860626109433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150137539548314480834812577 112603154661235860626109433)
  ·
    refine ⟨84452365995926895469582075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112603154661235860626109433 84452365995926895469582075)
    ·
      refine ⟨126678548993890343204373113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84452365995926895469582075 126678548993890343204373113)
      ·
        refine ⟨95008911745417757403279835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126678548993890343204373113 95008911745417757403279835)
        ·
          refine ⟨142513367618126636104919753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95008911745417757403279835 142513367618126636104919753)
          ·
            refine ⟨106885025713594977078689815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142513367618126636104919753 106885025713594977078689815)
            ·
              refine ⟨160327538570392465618034723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106885025713594977078689815 160327538570392465618034723)
              ·
                refine ⟨240491307855588698427052085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160327538570392465618034723 240491307855588698427052085)
                ·
                  refine ⟨22546060111461440477536133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240491307855588698427052085 22546060111461440477536133)
                  ·
                    refine ⟨4227386270899020089538025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22546060111461440477536133 4227386270899020089538025)
                    ·
                      refine ⟨3170539703174265067153519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227386270899020089538025 3170539703174265067153519)
                      ·
                        rfl

theorem cell23_6174604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_6174604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174604 prefixEnd_6174604 := by exact prefixLift 6174604
  have htrace : WordTrace (prefixWord ++ tailWord_6174604) baseStart_6174604 baseEnd_6174604 := by
    simpa [prefixWord, tailWord_6174604, baseEnd_6174604] using wordTrace_append hprefix tailTrace_6174604
  have hstable : (prefixWord ++ tailWord_6174604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174604).length < 2 ^ (prefixWord ++ tailWord_6174604).sum := by decide
  have hdescent : baseEnd_6174604 < baseStart_6174604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174617 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_6174617 : Nat := 118140960795 + 6174617 * 2 ^ 59
def prefixEnd_6174617 : Nat := 4983230072969 + 3 ^ 40 * 6174617 * 2
def baseEnd_6174617 : Nat := 3170546378422773516290959

theorem tailTrace_6174617 : CollatzResearch.WordTrace tailWord_6174617 prefixEnd_6174617 3170546378422773516290959 := by
  unfold tailWord_6174617
  simp only [CollatzResearch.WordTrace]
  refine ⟨225206783471424624472442105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150137855647616416314961403 225206783471424624472442105)
  ·
    refine ⟨168905087603568468354331579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225206783471424624472442105 168905087603568468354331579)
    ·
      refine ⟨253357631405352702531497369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168905087603568468354331579 253357631405352702531497369)
      ·
        refine ⟨190018223554014526898623027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253357631405352702531497369 190018223554014526898623027)
        ·
          refine ⟨285027335331021790347934541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190018223554014526898623027 285027335331021790347934541)
          ·
            refine ⟨106885250749133171380475453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285027335331021790347934541 106885250749133171380475453)
            ·
              refine ⟨40081969030924939267678295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106885250749133171380475453 40081969030924939267678295)
              ·
                refine ⟨60122953546387408901517443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40081969030924939267678295 60122953546387408901517443)
                ·
                  refine ⟨90184430319581113352276165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60122953546387408901517443 90184430319581113352276165)
                  ·
                    refine ⟨16909580684921458753551781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90184430319581113352276165 16909580684921458753551781)
                    ·
                      refine ⟨3170546378422773516290959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16909580684921458753551781 3170546378422773516290959)
                      ·
                        rfl

theorem cell23_6174617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_6174617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174617 prefixEnd_6174617 := by exact prefixLift 6174617
  have htrace : WordTrace (prefixWord ++ tailWord_6174617) baseStart_6174617 baseEnd_6174617 := by
    simpa [prefixWord, tailWord_6174617, baseEnd_6174617] using wordTrace_append hprefix tailTrace_6174617
  have hstable : (prefixWord ++ tailWord_6174617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174617).length < 2 ^ (prefixWord ++ tailWord_6174617).sum := by decide
  have hdescent : baseEnd_6174617 < baseStart_6174617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174621 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_6174621 : Nat := 118140960795 + 6174621 * 2 ^ 59
def prefixEnd_6174621 : Nat := 4983230072969 + 3 ^ 40 * 6174621 * 2
def baseEnd_6174621 : Nat := 3170548432345391500640941

theorem tailTrace_6174621 : CollatzResearch.WordTrace tailWord_6174621 prefixEnd_6174621 3170548432345391500640941 := by
  unfold tailWord_6174621
  simp only [CollatzResearch.WordTrace]
  refine ⟨225206929363410133155587717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150137952908940088770391811 225206929363410133155587717)
  ·
    refine ⟨42226299255639399966672697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225206929363410133155587717 42226299255639399966672697)
    ·
      refine ⟨31669724441729549975004523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42226299255639399966672697 31669724441729549975004523)
      ·
        refine ⟨47504586662594324962506785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31669724441729549975004523 47504586662594324962506785)
        ·
          refine ⟨35628439996945743721880089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47504586662594324962506785 35628439996945743721880089)
          ·
            refine ⟨26721329997709307791410067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35628439996945743721880089 26721329997709307791410067)
            ·
              refine ⟨40081994996563961687115101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26721329997709307791410067 40081994996563961687115101)
              ·
                refine ⟨15030748123711485632668163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40081994996563961687115101 15030748123711485632668163)
                ·
                  refine ⟨22546122185567228449002245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15030748123711485632668163 22546122185567228449002245)
                  ·
                    refine ⟨4227397909793855334187921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22546122185567228449002245 4227397909793855334187921)
                    ·
                      refine ⟨3170548432345391500640941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227397909793855334187921 3170548432345391500640941)
                      ·
                        rfl

theorem cell23_6174621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_6174621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174621 prefixEnd_6174621 := by exact prefixLift 6174621
  have htrace : WordTrace (prefixWord ++ tailWord_6174621) baseStart_6174621 baseEnd_6174621 := by
    simpa [prefixWord, tailWord_6174621, baseEnd_6174621] using wordTrace_append hprefix tailTrace_6174621
  have hstable : (prefixWord ++ tailWord_6174621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174621).length < 2 ^ (prefixWord ++ tailWord_6174621).sum := by decide
  have hdescent : baseEnd_6174621 < baseStart_6174621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174667 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_6174667 : Nat := 118140960795 + 6174667 * 2 ^ 59
def prefixEnd_6174667 : Nat := 4983230072969 + 3 ^ 40 * 6174667 * 2
def baseEnd_6174667 : Nat := 3170572052455498320665729

theorem tailTrace_6174667 : CollatzResearch.WordTrace tailWord_6174667 prefixEnd_6174667 3170572052455498320665729 := by
  unfold tailWord_6174667
  simp only [CollatzResearch.WordTrace]
  refine ⟨225208607121243483011762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150139071414162322007841503 225208607121243483011762255)
  ·
    refine ⟨337812910681865224517643383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225208607121243483011762255 337812910681865224517643383)
    ·
      refine ⟨506719366022797836776465075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337812910681865224517643383 506719366022797836776465075)
      ·
        refine ⟨760079049034196755164697613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506719366022797836776465075 760079049034196755164697613)
        ·
          refine ⟨285029643387823783186761605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760079049034196755164697613 285029643387823783186761605)
          ·
            refine ⟨53443058135216959347517801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285029643387823783186761605 53443058135216959347517801)
            ·
              refine ⟨40082293601412719510638351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53443058135216959347517801 40082293601412719510638351)
              ·
                refine ⟨60123440402119079265957527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40082293601412719510638351 60123440402119079265957527)
                ·
                  refine ⟨90185160603178618898936291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60123440402119079265957527 90185160603178618898936291)
                  ·
                    refine ⟨135277740904767928348404437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90185160603178618898936291 135277740904767928348404437)
                    ·
                      refine ⟨3170572052455498320665729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135277740904767928348404437 3170572052455498320665729)
                      ·
                        rfl

theorem cell23_6174667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_6174667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174667 prefixEnd_6174667 := by exact prefixLift 6174667
  have htrace : WordTrace (prefixWord ++ tailWord_6174667) baseStart_6174667 baseEnd_6174667 := by
    simpa [prefixWord, tailWord_6174667, baseEnd_6174667] using wordTrace_append hprefix tailTrace_6174667
  have hstable : (prefixWord ++ tailWord_6174667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174667).length < 2 ^ (prefixWord ++ tailWord_6174667).sum := by decide
  have hdescent : baseEnd_6174667 < baseStart_6174667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174695 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 5]
def baseStart_6174695 : Nat := 118140960795 + 6174695 * 2 ^ 59
def prefixEnd_6174695 : Nat := 4983230072969 + 3 ^ 40 * 6174695 * 2
def baseEnd_6174695 : Nat := 352287381101536023457289

theorem tailTrace_6174695 : CollatzResearch.WordTrace tailWord_6174695 prefixEnd_6174695 352287381101536023457289 := by
  unfold tailWord_6174695
  simp only [CollatzResearch.WordTrace]
  refine ⟨225209628365142043793781539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150139752243428029195854359 225209628365142043793781539)
  ·
    refine ⟨337814442547713065690672309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225209628365142043793781539 337814442547713065690672309)
    ·
      refine ⟨31670103988848099908500529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337814442547713065690672309 31670103988848099908500529)
      ·
        refine ⟨23752577991636074931375397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31670103988848099908500529 23752577991636074931375397)
        ·
          refine ⟨4453608373431764049632887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23752577991636074931375397 4453608373431764049632887)
          ·
            refine ⟨6680412560147646074449331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453608373431764049632887 6680412560147646074449331)
            ·
              refine ⟨10020618840221469111673997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680412560147646074449331 10020618840221469111673997)
              ·
                refine ⟨3757732065083050916877749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10020618840221469111673997 3757732065083050916877749)
                ·
                  refine ⟨352287381101536023457289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757732065083050916877749 352287381101536023457289)
                  ·
                    rfl

theorem cell23_6174695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 5].length) (baseStart_6174695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174695 prefixEnd_6174695 := by exact prefixLift 6174695
  have htrace : WordTrace (prefixWord ++ tailWord_6174695) baseStart_6174695 baseEnd_6174695 := by
    simpa [prefixWord, tailWord_6174695, baseEnd_6174695] using wordTrace_append hprefix tailTrace_6174695
  have hstable : (prefixWord ++ tailWord_6174695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174695).length < 2 ^ (prefixWord ++ tailWord_6174695).sum := by decide
  have hdescent : baseEnd_6174695 < baseStart_6174695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174704 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_6174704 : Nat := 118140960795 + 6174704 * 2 ^ 59
def prefixEnd_6174704 : Nat := 4983230072969 + 3 ^ 40 * 6174704 * 2
def baseEnd_6174704 : Nat := 1056863683746571558634353

theorem tailTrace_6174704 : CollatzResearch.WordTrace tailWord_6174704 prefixEnd_6174704 1056863683746571558634353 := by
  unfold tailWord_6174704
  simp only [CollatzResearch.WordTrace]
  refine ⟨112604978311054719165429583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150139971081406292220572777 112604978311054719165429583)
  ·
    refine ⟨168907467466582078748144375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112604978311054719165429583 168907467466582078748144375)
    ·
      refine ⟨253361201199873118122216563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168907467466582078748144375 253361201199873118122216563)
      ·
        refine ⟨380041801799809677183324845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253361201199873118122216563 380041801799809677183324845)
        ·
          refine ⟨142515675674928628943746817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380041801799809677183324845 142515675674928628943746817)
          ·
            refine ⟨106886756756196471707810113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142515675674928628943746817 106886756756196471707810113)
            ·
              refine ⟨80165067567147353780857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106886756756196471707810113 80165067567147353780857585)
              ·
                refine ⟨60123800675360515335643189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80165067567147353780857585 60123800675360515335643189)
                ·
                  refine ⟨5636606313315048312716549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60123800675360515335643189 5636606313315048312716549)
                  ·
                    refine ⟨1056863683746571558634353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636606313315048312716549 1056863683746571558634353)
                    ·
                      rfl

theorem cell23_6174704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_6174704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174704 prefixEnd_6174704 := by exact prefixLift 6174704
  have htrace : WordTrace (prefixWord ++ tailWord_6174704) baseStart_6174704 baseEnd_6174704 := by
    simpa [prefixWord, tailWord_6174704, baseEnd_6174704] using wordTrace_append hprefix tailTrace_6174704
  have hstable : (prefixWord ++ tailWord_6174704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174704).length < 2 ^ (prefixWord ++ tailWord_6174704).sum := by decide
  have hdescent : baseEnd_6174704 < baseStart_6174704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174707 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_6174707 : Nat := 118140960795 + 6174707 * 2 ^ 59
def prefixEnd_6174707 : Nat := 4983230072969 + 3 ^ 40 * 6174707 * 2
def baseEnd_6174707 : Nat := 3170592591681678164165545

theorem tailTrace_6174707 : CollatzResearch.WordTrace tailWord_6174707 prefixEnd_6174707 3170592591681678164165545 := by
  unfold tailWord_6174707
  simp only [CollatzResearch.WordTrace]
  refine ⟨225210066041098569843218375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150140044027399046562145583 225210066041098569843218375)
  ·
    refine ⟨337815099061647854764827563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225210066041098569843218375 337815099061647854764827563)
    ·
      refine ⟨506722648592471782147241345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337815099061647854764827563 506722648592471782147241345)
      ·
        refine ⟨380041986444353836610431009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506722648592471782147241345 380041986444353836610431009)
        ·
          refine ⟨285031489833265377457823257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380041986444353836610431009 285031489833265377457823257)
          ·
            refine ⟨213773617374949033093367443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285031489833265377457823257 213773617374949033093367443)
            ·
              refine ⟨320660426062423549640051165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213773617374949033093367443 320660426062423549640051165)
              ·
                refine ⟨120247659773408831115019187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320660426062423549640051165 120247659773408831115019187)
                ·
                  refine ⟨180371489660113246672528781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120247659773408831115019187 180371489660113246672528781)
                  ·
                    refine ⟨67639308622542467502198293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180371489660113246672528781 67639308622542467502198293)
                    ·
                      refine ⟨3170592591681678164165545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67639308622542467502198293 3170592591681678164165545)
                      ·
                        rfl

theorem cell23_6174707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_6174707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174707 prefixEnd_6174707 := by exact prefixLift 6174707
  have htrace : WordTrace (prefixWord ++ tailWord_6174707) baseStart_6174707 baseEnd_6174707 := by
    simpa [prefixWord, tailWord_6174707, baseEnd_6174707] using wordTrace_append hprefix tailTrace_6174707
  have hstable : (prefixWord ++ tailWord_6174707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174707).length < 2 ^ (prefixWord ++ tailWord_6174707).sum := by decide
  have hdescent : baseEnd_6174707 < baseStart_6174707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174748 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6174748 : Nat := 118140960795 + 6174748 * 2 ^ 59
def prefixEnd_6174748 : Nat := 4983230072969 + 3 ^ 40 * 6174748 * 2
def baseEnd_6174748 : Nat := 3170613644388512503752857

theorem tailTrace_6174748 : CollatzResearch.WordTrace tailWord_6174748 prefixEnd_6174748 3170613644388512503752857 := by
  unfold tailWord_6174748
  simp only [CollatzResearch.WordTrace]
  refine ⟨112605780716975016922730449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150141040955966689230307265 112605780716975016922730449)
  ·
    refine ⟨84454335537731262692047837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112605780716975016922730449 84454335537731262692047837)
    ·
      refine ⟨31670375826649223509517939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84454335537731262692047837 31670375826649223509517939)
      ·
        refine ⟨47505563739973835264276909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31670375826649223509517939 47505563739973835264276909)
        ·
          refine ⟨17814586402490188224103841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47505563739973835264276909 17814586402490188224103841)
          ·
            refine ⟨13360939801867641168077881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17814586402490188224103841 13360939801867641168077881)
            ·
              refine ⟨10020704851400730876058411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13360939801867641168077881 10020704851400730876058411)
              ·
                refine ⟨15031057277101096314087617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10020704851400730876058411 15031057277101096314087617)
                ·
                  refine ⟨11273292957825822235565713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15031057277101096314087617 11273292957825822235565713)
                  ·
                    refine ⟨8454969718369366676674285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11273292957825822235565713 8454969718369366676674285)
                    ·
                      refine ⟨3170613644388512503752857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8454969718369366676674285 3170613644388512503752857)
                      ·
                        rfl

theorem cell23_6174748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6174748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174748 prefixEnd_6174748 := by exact prefixLift 6174748
  have htrace : WordTrace (prefixWord ++ tailWord_6174748) baseStart_6174748 baseEnd_6174748 := by
    simpa [prefixWord, tailWord_6174748, baseEnd_6174748] using wordTrace_append hprefix tailTrace_6174748
  have hstable : (prefixWord ++ tailWord_6174748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174748).length < 2 ^ (prefixWord ++ tailWord_6174748).sum := by decide
  have hdescent : baseEnd_6174748 < baseStart_6174748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174772 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_6174772 : Nat := 118140960795 + 6174772 * 2 ^ 59
def prefixEnd_6174772 : Nat := 4983230072969 + 3 ^ 40 * 6174772 * 2
def baseEnd_6174772 : Nat := 1056875322641406803284249

theorem tailTrace_6174772 : CollatzResearch.WordTrace tailWord_6174772 prefixEnd_6174772 1056875322641406803284249 := by
  unfold tailWord_6174772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112606218392931542972167285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150141624523908723962889713 112606218392931542972167285)
  ·
    refine ⟨10556832974337332153640683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112606218392931542972167285 10556832974337332153640683)
    ·
      refine ⟨15835249461505998230461025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10556832974337332153640683 15835249461505998230461025)
      ·
        refine ⟨11876437096129498672845769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15835249461505998230461025 11876437096129498672845769)
        ·
          refine ⟨8907327822097124004634327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876437096129498672845769 8907327822097124004634327)
          ·
            refine ⟨13360991733145686006951491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907327822097124004634327 13360991733145686006951491)
            ·
              refine ⟨20041487599718529010427237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13360991733145686006951491 20041487599718529010427237)
              ·
                refine ⟨3757778924947224189455107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20041487599718529010427237 3757778924947224189455107)
                ·
                  refine ⟨5636668387420836284182661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757778924947224189455107 5636668387420836284182661)
                  ·
                    refine ⟨1056875322641406803284249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636668387420836284182661 1056875322641406803284249)
                    ·
                      rfl

theorem cell23_6174772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_6174772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174772 prefixEnd_6174772 := by exact prefixLift 6174772
  have htrace : WordTrace (prefixWord ++ tailWord_6174772) baseStart_6174772 baseEnd_6174772 := by
    simpa [prefixWord, tailWord_6174772, baseEnd_6174772] using wordTrace_append hprefix tailTrace_6174772
  have hstable : (prefixWord ++ tailWord_6174772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174772).length < 2 ^ (prefixWord ++ tailWord_6174772).sum := by decide
  have hdescent : baseEnd_6174772 < baseStart_6174772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_6174801 : Nat := 118140960795 + 6174801 * 2 ^ 59
def prefixEnd_6174801 : Nat := 4983230072969 + 3 ^ 40 * 6174801 * 2
def baseEnd_6174801 : Nat := 3170640858863200796390113

theorem tailTrace_6174801 : CollatzResearch.WordTrace tailWord_6174801 prefixEnd_6174801 3170640858863200796390113 := by
  unfold tailWord_6174801
  simp only [CollatzResearch.WordTrace]
  refine ⟨225213494502758023897140257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150142329668505349264760171 225213494502758023897140257)
  ·
    refine ⟨168910120877068517922855193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225213494502758023897140257 168910120877068517922855193)
    ·
      refine ⟨126682590657801388442141395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168910120877068517922855193 126682590657801388442141395)
      ·
        refine ⟨190023885986702082663212093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126682590657801388442141395 190023885986702082663212093)
        ·
          refine ⟨71258957245013280998704535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190023885986702082663212093 71258957245013280998704535)
          ·
            refine ⟨106888435867519921498056803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71258957245013280998704535 106888435867519921498056803)
            ·
              refine ⟨160332653801279882247085205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106888435867519921498056803 160332653801279882247085205)
              ·
                refine ⟨7515593146934994480332119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160332653801279882247085205 7515593146934994480332119)
                ·
                  refine ⟨11273389720402491720498179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515593146934994480332119 11273389720402491720498179)
                  ·
                    refine ⟨16910084580603737580747269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11273389720402491720498179 16910084580603737580747269)
                    ·
                      refine ⟨3170640858863200796390113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16910084580603737580747269 3170640858863200796390113)
                      ·
                        rfl

theorem cell23_6174801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_6174801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174801 prefixEnd_6174801 := by exact prefixLift 6174801
  have htrace : WordTrace (prefixWord ++ tailWord_6174801) baseStart_6174801 baseEnd_6174801 := by
    simpa [prefixWord, tailWord_6174801, baseEnd_6174801] using wordTrace_append hprefix tailTrace_6174801
  have hstable : (prefixWord ++ tailWord_6174801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174801).length < 2 ^ (prefixWord ++ tailWord_6174801).sum := by decide
  have hdescent : baseEnd_6174801 < baseStart_6174801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174805 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6174805 : Nat := 118140960795 + 6174805 * 2 ^ 59
def prefixEnd_6174805 : Nat := 4983230072969 + 3 ^ 40 * 6174805 * 2
def baseEnd_6174805 : Nat := 3170642912785818780740095

theorem tailTrace_6174805 : CollatzResearch.WordTrace tailWord_6174805 prefixEnd_6174805 3170642912785818780740095 := by
  unfold tailWord_6174805
  simp only [CollatzResearch.WordTrace]
  refine ⟨225213640394743532580285869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150142426929829021720190579 225213640394743532580285869)
  ·
    refine ⟨84455115148028824717607201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225213640394743532580285869 84455115148028824717607201)
    ·
      refine ⟨63341336361021618538205401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84455115148028824717607201 63341336361021618538205401)
      ·
        refine ⟨47506002270766213903654051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63341336361021618538205401 47506002270766213903654051)
        ·
          refine ⟨71259003406149320855481077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47506002270766213903654051 71259003406149320855481077)
          ·
            refine ⟨6680531569326498830201351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71259003406149320855481077 6680531569326498830201351)
            ·
              refine ⟨10020797353989748245302027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680531569326498830201351 10020797353989748245302027)
              ·
                refine ⟨15031196030984622367953041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10020797353989748245302027 15031196030984622367953041)
                ·
                  refine ⟨11273397023238466775964781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15031196030984622367953041 11273397023238466775964781)
                  ·
                    refine ⟨4227523883714425040986793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11273397023238466775964781 4227523883714425040986793)
                    ·
                      refine ⟨3170642912785818780740095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227523883714425040986793 3170642912785818780740095)
                      ·
                        rfl

theorem cell23_6174805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6174805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174805 prefixEnd_6174805 := by exact prefixLift 6174805
  have htrace : WordTrace (prefixWord ++ tailWord_6174805) baseStart_6174805 baseEnd_6174805 := by
    simpa [prefixWord, tailWord_6174805, baseEnd_6174805] using wordTrace_append hprefix tailTrace_6174805
  have hstable : (prefixWord ++ tailWord_6174805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174805).length < 2 ^ (prefixWord ++ tailWord_6174805).sum := by decide
  have hdescent : baseEnd_6174805 < baseStart_6174805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174812 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6174812 : Nat := 118140960795 + 6174812 * 2 ^ 59
def prefixEnd_6174812 : Nat := 4983230072969 + 3 ^ 40 * 6174812 * 2
def baseEnd_6174812 : Nat := 3170646507150400253352563

theorem tailTrace_6174812 : CollatzResearch.WordTrace tailWord_6174812 prefixEnd_6174812 3170646507150400253352563 := by
  unfold tailWord_6174812
  simp only [CollatzResearch.WordTrace]
  refine ⟨112606947852859086387895345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150142597137145448517193793 112606947852859086387895345)
  ·
    refine ⟨84455210889644314790921509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112606947852859086387895345 84455210889644314790921509)
    ·
      refine ⟨15835352041808309023297783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84455210889644314790921509 15835352041808309023297783)
      ·
        refine ⟨23753028062712463534946675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15835352041808309023297783 23753028062712463534946675)
        ·
          refine ⟨35629542094068695302420013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23753028062712463534946675 35629542094068695302420013)
          ·
            refine ⟨13361078285275760738407505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35629542094068695302420013 13361078285275760738407505)
            ·
              refine ⟨10020808713956820553805629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13361078285275760738407505 10020808713956820553805629)
              ·
                refine ⟨3757803267733807707677111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10020808713956820553805629 3757803267733807707677111)
                ·
                  refine ⟨5636704901600711561515667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757803267733807707677111 5636704901600711561515667)
                  ·
                    refine ⟨8455057352401067342273501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636704901600711561515667 8455057352401067342273501)
                    ·
                      refine ⟨3170646507150400253352563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8455057352401067342273501 3170646507150400253352563)
                      ·
                        rfl

theorem cell23_6174812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6174812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174812 prefixEnd_6174812 := by exact prefixLift 6174812
  have htrace : WordTrace (prefixWord ++ tailWord_6174812) baseStart_6174812 baseEnd_6174812 := by
    simpa [prefixWord, tailWord_6174812, baseEnd_6174812] using wordTrace_append hprefix tailTrace_6174812
  have hstable : (prefixWord ++ tailWord_6174812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174812).length < 2 ^ (prefixWord ++ tailWord_6174812).sum := by decide
  have hdescent : baseEnd_6174812 < baseStart_6174812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174828 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_6174828 : Nat := 118140960795 + 6174828 * 2 ^ 59
def prefixEnd_6174828 : Nat := 4983230072969 + 3 ^ 40 * 6174828 * 2
def baseEnd_6174828 : Nat := 1056884907613624063584163

theorem tailTrace_6174828 : CollatzResearch.WordTrace tailWord_6174828 prefixEnd_6174828 1056884907613624063584163 := by
  unfold tailWord_6174828
  simp only [CollatzResearch.WordTrace]
  refine ⟨112607239636830103754186569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150142986182440138338915425 112607239636830103754186569)
  ·
    refine ⟨84455429727622577815639927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112607239636830103754186569 84455429727622577815639927)
    ·
      refine ⟨126683144591433866723459891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84455429727622577815639927 126683144591433866723459891)
      ·
        refine ⟨190024716887150800085189837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126683144591433866723459891 190024716887150800085189837)
        ·
          refine ⟨71259268832681550031946189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190024716887150800085189837 71259268832681550031946189)
          ·
            refine ⟨26722225812255581261979821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71259268832681550031946189 26722225812255581261979821)
            ·
              refine ⟨10020834679595842973242433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26722225812255581261979821 10020834679595842973242433)
              ·
                refine ⟨7515626009696882229931825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020834679595842973242433 7515626009696882229931825)
                ·
                  refine ⟨5636719507272661672448869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515626009696882229931825 5636719507272661672448869)
                  ·
                    refine ⟨1056884907613624063584163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636719507272661672448869 1056884907613624063584163)
                    ·
                      rfl

theorem cell23_6174828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_6174828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174828 prefixEnd_6174828 := by exact prefixLift 6174828
  have htrace : WordTrace (prefixWord ++ tailWord_6174828) baseStart_6174828 baseEnd_6174828 := by
    simpa [prefixWord, tailWord_6174828, baseEnd_6174828] using wordTrace_append hprefix tailTrace_6174828
  have hstable : (prefixWord ++ tailWord_6174828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174828).length < 2 ^ (prefixWord ++ tailWord_6174828).sum := by decide
  have hdescent : baseEnd_6174828 < baseStart_6174828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174838 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6174838 : Nat := 118140960795 + 6174838 * 2 ^ 59
def prefixEnd_6174838 : Nat := 4983230072969 + 3 ^ 40 * 6174838 * 2
def baseEnd_6174838 : Nat := 3170659857647417151627443

theorem tailTrace_6174838 : CollatzResearch.WordTrace tailWord_6174838 prefixEnd_6174838 3170659857647417151627443 := by
  unfold tailWord_6174838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075927750226498701014823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150143229335749319477491445 14075927750226498701014823)
  ·
    refine ⟨21113891625339748051522235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075927750226498701014823 21113891625339748051522235)
    ·
      refine ⟨31670837438009622077283353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21113891625339748051522235 31670837438009622077283353)
      ·
        refine ⟨23753128078507216557962515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31670837438009622077283353 23753128078507216557962515)
        ·
          refine ⟨35629692117760824836943773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23753128078507216557962515 35629692117760824836943773)
          ·
            refine ⟨13361134544160309313853915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35629692117760824836943773 13361134544160309313853915)
            ·
              refine ⟨20041701816240463970780873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13361134544160309313853915 20041701816240463970780873)
              ·
                refine ⟨15031276362180347978085655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20041701816240463970780873 15031276362180347978085655)
                ·
                  refine ⟨22546914543270521967128483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15031276362180347978085655 22546914543270521967128483)
                  ·
                    refine ⟨33820371814905782950692725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22546914543270521967128483 33820371814905782950692725)
                    ·
                      refine ⟨3170659857647417151627443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33820371814905782950692725 3170659857647417151627443)
                      ·
                        rfl

theorem cell23_6174838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6174838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174838 prefixEnd_6174838 := by exact prefixLift 6174838
  have htrace : WordTrace (prefixWord ++ tailWord_6174838) baseStart_6174838 baseEnd_6174838 := by
    simpa [prefixWord, tailWord_6174838, baseEnd_6174838] using wordTrace_append hprefix tailTrace_6174838
  have hstable : (prefixWord ++ tailWord_6174838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174838).length < 2 ^ (prefixWord ++ tailWord_6174838).sum := by decide
  have hdescent : baseEnd_6174838 < baseStart_6174838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174845 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_6174845 : Nat := 118140960795 + 6174845 * 2 ^ 59
def prefixEnd_6174845 : Nat := 4983230072969 + 3 ^ 40 * 6174845 * 2
def baseEnd_6174845 : Nat := 1056887817337332874746637

theorem tailTrace_6174845 : CollatzResearch.WordTrace tailWord_6174845 prefixEnd_6174845 1056887817337332874746637 := by
  unfold tailWord_6174845
  simp only [CollatzResearch.WordTrace]
  refine ⟨225215099314598619411741989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150143399543065746274494659 225215099314598619411741989)
  ·
    refine ⟨42227831121487241139701623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225215099314598619411741989 42227831121487241139701623)
    ·
      refine ⟨63341746682230861709552435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42227831121487241139701623 63341746682230861709552435)
      ·
        refine ⟨95012620023346292564328653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63341746682230861709552435 95012620023346292564328653)
        ·
          refine ⟨35629732508754859711623245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95012620023346292564328653 35629732508754859711623245)
          ·
            refine ⟨13361149690783072391858717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35629732508754859711623245 13361149690783072391858717)
            ·
              refine ⟨5010431134043652146947019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13361149690783072391858717 5010431134043652146947019)
              ·
                refine ⟨7515646701065478220420529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010431134043652146947019 7515646701065478220420529)
                ·
                  refine ⟨5636735025799108665315397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515646701065478220420529 5636735025799108665315397)
                  ·
                    refine ⟨1056887817337332874746637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636735025799108665315397 1056887817337332874746637)
                    ·
                      rfl

theorem cell23_6174845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_6174845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174845 prefixEnd_6174845 := by exact prefixLift 6174845
  have htrace : WordTrace (prefixWord ++ tailWord_6174845) baseStart_6174845 baseEnd_6174845 := by
    simpa [prefixWord, tailWord_6174845, baseEnd_6174845] using wordTrace_append hprefix tailTrace_6174845
  have hstable : (prefixWord ++ tailWord_6174845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174845).length < 2 ^ (prefixWord ++ tailWord_6174845).sum := by decide
  have hdescent : baseEnd_6174845 < baseStart_6174845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174858 : List Nat := [3, 1, 2, 3, 1, 4, 2, 7]
def baseStart_6174858 : Nat := 118140960795 + 6174858 * 2 ^ 59
def prefixEnd_6174858 : Nat := 4983230072969 + 3 ^ 40 * 6174858 * 2
def baseEnd_6174858 : Nat := 117432226935574336051013

theorem tailTrace_6174858 : CollatzResearch.WordTrace tailWord_6174858 prefixEnd_6174858 117432226935574336051013 := by
  unfold tailWord_6174858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56303893365887880657991307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150143715642367681754643485 56303893365887880657991307)
  ·
    refine ⟨84455840048831820986986961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56303893365887880657991307 84455840048831820986986961)
    ·
      refine ⟨63341880036623865740240221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84455840048831820986986961 63341880036623865740240221)
      ·
        refine ⟨23753205013733949652590083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63341880036623865740240221 23753205013733949652590083)
        ·
          refine ⟨35629807520600924478885125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23753205013733949652590083 35629807520600924478885125)
          ·
            refine ⟨6680588910112673339790961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35629807520600924478885125 6680588910112673339790961)
            ·
              refine ⟨5010441682584505004843221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680588910112673339790961 5010441682584505004843221)
              ·
                refine ⟨117432226935574336051013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5010441682584505004843221 117432226935574336051013)
                ·
                  rfl

theorem cell23_6174858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_6174858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174858 prefixEnd_6174858 := by exact prefixLift 6174858
  have htrace : WordTrace (prefixWord ++ tailWord_6174858) baseStart_6174858 baseEnd_6174858 := by
    simpa [prefixWord, tailWord_6174858, baseEnd_6174858] using wordTrace_append hprefix tailTrace_6174858
  have hstable : (prefixWord ++ tailWord_6174858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174858).length < 2 ^ (prefixWord ++ tailWord_6174858).sum := by decide
  have hdescent : baseEnd_6174858 < baseStart_6174858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174864 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_6174864 : Nat := 118140960795 + 6174864 * 2 ^ 59
def prefixEnd_6174864 : Nat := 4983230072969 + 3 ^ 40 * 6174864 * 2
def baseEnd_6174864 : Nat := 3170673208144434049902323

theorem tailTrace_6174864 : CollatzResearch.WordTrace tailWord_6174864 prefixEnd_6174864 3170673208144434049902323 := by
  unfold tailWord_6174864
  simp only [CollatzResearch.WordTrace]
  refine ⟨112607896150764892828341823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150143861534353190437789097 112607896150764892828341823)
  ·
    refine ⟨168911844226147339242512735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112607896150764892828341823 168911844226147339242512735)
    ·
      refine ⟨253367766339221008863769103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168911844226147339242512735 253367766339221008863769103)
      ·
        refine ⟨380051649508831513295653655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253367766339221008863769103 380051649508831513295653655)
        ·
          refine ⟨570077474263247269943480483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380051649508831513295653655 570077474263247269943480483)
          ·
            refine ⟨855116211394870904915220725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570077474263247269943480483 855116211394870904915220725)
            ·
              refine ⟨80167144818269147335801943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 855116211394870904915220725 80167144818269147335801943)
              ·
                refine ⟨120250717227403721003702915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80167144818269147335801943 120250717227403721003702915)
                ·
                  refine ⟨180376075841105581505554373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120250717227403721003702915 180376075841105581505554373)
                  ·
                    refine ⟨33820514220207296532291445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180376075841105581505554373 33820514220207296532291445)
                    ·
                      refine ⟨3170673208144434049902323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33820514220207296532291445 3170673208144434049902323)
                      ·
                        rfl

theorem cell23_6174864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_6174864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174864 prefixEnd_6174864 := by exact prefixLift 6174864
  have htrace : WordTrace (prefixWord ++ tailWord_6174864) baseStart_6174864 baseEnd_6174864 := by
    simpa [prefixWord, tailWord_6174864, baseEnd_6174864] using wordTrace_append hprefix tailTrace_6174864
  have hstable : (prefixWord ++ tailWord_6174864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174864).length < 2 ^ (prefixWord ++ tailWord_6174864).sum := by decide
  have hdescent : baseEnd_6174864 < baseStart_6174864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174912 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2]
def baseStart_6174912 : Nat := 118140960795 + 6174912 * 2 ^ 59
def prefixEnd_6174912 : Nat := 4983230072969 + 3 ^ 40 * 6174912 * 2
def baseEnd_6174912 : Nat := 3170697855215849862102103

theorem tailTrace_6174912 : CollatzResearch.WordTrace tailWord_6174912 prefixEnd_6174912 3170697855215849862102103 := by
  unfold tailWord_6174912
  simp only [CollatzResearch.WordTrace]
  refine ⟨112608771502677944927215495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150145028670237259902953993 112608771502677944927215495)
  ·
    refine ⟨168913157254016917390823243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112608771502677944927215495 168913157254016917390823243)
    ·
      refine ⟨253369735881025376086234865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168913157254016917390823243 253369735881025376086234865)
      ·
        refine ⟨190027301910769032064676149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253369735881025376086234865 190027301910769032064676149)
        ·
          refine ⟨17815059554134596756063389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190027301910769032064676149 17815059554134596756063389)
          ·
            refine ⟨6680647332800473783523771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17815059554134596756063389 6680647332800473783523771)
            ·
              refine ⟨10020970999200710675285657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680647332800473783523771 10020970999200710675285657)
              ·
                refine ⟨7515728249400533006464243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020970999200710675285657 7515728249400533006464243)
                ·
                  refine ⟨11273592374100799509696365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515728249400533006464243 11273592374100799509696365)
                  ·
                    refine ⟨4227597140287799816136137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11273592374100799509696365 4227597140287799816136137)
                    ·
                      refine ⟨3170697855215849862102103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227597140287799816136137 3170697855215849862102103)
                      ·
                        rfl

theorem cell23_6174912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_6174912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174912 prefixEnd_6174912 := by exact prefixLift 6174912
  have htrace : WordTrace (prefixWord ++ tailWord_6174912) baseStart_6174912 baseEnd_6174912 := by
    simpa [prefixWord, tailWord_6174912, baseEnd_6174912] using wordTrace_append hprefix tailTrace_6174912
  have hstable : (prefixWord ++ tailWord_6174912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174912).length < 2 ^ (prefixWord ++ tailWord_6174912).sum := by decide
  have hdescent : baseEnd_6174912 < baseStart_6174912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174961 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_6174961 : Nat := 118140960795 + 6174961 * 2 ^ 59
def prefixEnd_6174961 : Nat := 4983230072969 + 3 ^ 40 * 6174961 * 2
def baseEnd_6174961 : Nat := 1056907671922640056796459

theorem tailTrace_6174961 : CollatzResearch.WordTrace tailWord_6174961 prefixEnd_6174961 1056907671922640056796459 := by
  unfold tailWord_6174961
  simp only [CollatzResearch.WordTrace]
  refine ⟨225219330182178371222964737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150146220121452247481976491 225219330182178371222964737)
  ·
    refine ⟨168914497636633778417223553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225219330182178371222964737 168914497636633778417223553)
    ·
      refine ⟨126685873227475333812917665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168914497636633778417223553 126685873227475333812917665)
      ·
        refine ⟨95014404920606500359688249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126685873227475333812917665 95014404920606500359688249)
        ·
          refine ⟨71260803690454875269766187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95014404920606500359688249 71260803690454875269766187)
          ·
            refine ⟨106891205535682312904649281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71260803690454875269766187 106891205535682312904649281)
            ·
              refine ⟨80168404151761734678486961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106891205535682312904649281 80168404151761734678486961)
              ·
                refine ⟨60126303113821301008865221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80168404151761734678486961 60126303113821301008865221)
                ·
                  refine ⟨11273681833841493939162229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60126303113821301008865221 11273681833841493939162229)
                  ·
                    refine ⟨1056907671922640056796459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11273681833841493939162229 1056907671922640056796459)
                    ·
                      rfl

theorem cell23_6174961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_6174961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174961 prefixEnd_6174961 := by exact prefixLift 6174961
  have htrace : WordTrace (prefixWord ++ tailWord_6174961) baseStart_6174961 baseEnd_6174961 := by
    simpa [prefixWord, tailWord_6174961, baseEnd_6174961] using wordTrace_append hprefix tailTrace_6174961
  have hstable : (prefixWord ++ tailWord_6174961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174961).length < 2 ^ (prefixWord ++ tailWord_6174961).sum := by decide
  have hdescent : baseEnd_6174961 < baseStart_6174961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175011 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_6175011 : Nat := 118140960795 + 6175011 * 2 ^ 59
def prefixEnd_6175011 : Nat := 4983230072969 + 3 ^ 40 * 6175011 * 2
def baseEnd_6175011 : Nat := 3170748689800644974764147

theorem tailTrace_6175011 : CollatzResearch.WordTrace tailWord_6175011 prefixEnd_6175011 3170748689800644974764147 := by
  unfold tailWord_6175011
  simp only [CollatzResearch.WordTrace]
  refine ⟨225221153831997229762284887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150147435887998153174856591 225221153831997229762284887)
  ·
    refine ⟨337831730747995844643427331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225221153831997229762284887 337831730747995844643427331)
    ·
      refine ⟨506747596121993766965140997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337831730747995844643427331 506747596121993766965140997)
      ·
        refine ⟨95015174272873831305963937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506747596121993766965140997 95015174272873831305963937)
        ·
          refine ⟨71261380704655373479472953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95015174272873831305963937 71261380704655373479472953)
          ·
            refine ⟨53446035528491530109604715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71261380704655373479472953 53446035528491530109604715)
            ·
              refine ⟨80169053292737295164407073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53446035528491530109604715 80169053292737295164407073)
              ·
                refine ⟨60126789969552971373305305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80169053292737295164407073 60126789969552971373305305)
                ·
                  refine ⟨45095092477164728529978979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60126789969552971373305305 45095092477164728529978979)
                  ·
                    refine ⟨67642638715747092794968469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45095092477164728529978979 67642638715747092794968469)
                    ·
                      refine ⟨3170748689800644974764147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67642638715747092794968469 3170748689800644974764147)
                      ·
                        rfl

theorem cell23_6175011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_6175011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175011 prefixEnd_6175011 := by exact prefixLift 6175011
  have htrace : WordTrace (prefixWord ++ tailWord_6175011) baseStart_6175011 baseEnd_6175011 := by
    simpa [prefixWord, tailWord_6175011, baseEnd_6175011] using wordTrace_append hprefix tailTrace_6175011
  have hstable : (prefixWord ++ tailWord_6175011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175011).length < 2 ^ (prefixWord ++ tailWord_6175011).sum := by decide
  have hdescent : baseEnd_6175011 < baseStart_6175011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175038 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_6175038 : Nat := 118140960795 + 6175038 * 2 ^ 59
def prefixEnd_6175038 : Nat := 4983230072969 + 3 ^ 40 * 6175038 * 2
def baseEnd_6175038 : Nat := 352306950419812929902947

theorem tailTrace_6175038 : CollatzResearch.WordTrace tailWord_6175038 prefixEnd_6175038 352306950419812929902947 := by
  unfold tailWord_6175038
  simp only [CollatzResearch.WordTrace]
  refine ⟨28152767325362426671689721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150148092401932942249011845 28152767325362426671689721)
  ·
    refine ⟨21114575494021820003767291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28152767325362426671689721 21114575494021820003767291)
    ·
      refine ⟨31671863241032730005650937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21114575494021820003767291 31671863241032730005650937)
      ·
        refine ⟨23753897430774547504238203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31671863241032730005650937 23753897430774547504238203)
        ·
          refine ⟨35630846146161821256357305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23753897430774547504238203 35630846146161821256357305)
          ·
            refine ⟨26723134609621365942267979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35630846146161821256357305 26723134609621365942267979)
            ·
              refine ⟨40084701914432048913401969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26723134609621365942267979 40084701914432048913401969)
              ·
                refine ⟨30063526435824036685051477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40084701914432048913401969 30063526435824036685051477)
                ·
                  refine ⟨352306950419812929902947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30063526435824036685051477 352306950419812929902947)
                  ·
                    rfl

theorem cell23_6175038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_6175038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175038 prefixEnd_6175038 := by exact prefixLift 6175038
  have htrace : WordTrace (prefixWord ++ tailWord_6175038) baseStart_6175038 baseEnd_6175038 := by
    simpa [prefixWord, tailWord_6175038, baseEnd_6175038] using wordTrace_append hprefix tailTrace_6175038
  have hstable : (prefixWord ++ tailWord_6175038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175038).length < 2 ^ (prefixWord ++ tailWord_6175038).sum := by decide
  have hdescent : baseEnd_6175038 < baseStart_6175038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175072 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 6]
def baseStart_6175072 : Nat := 118140960795 + 6175072 * 2 ^ 59
def prefixEnd_6175072 : Nat := 4983230072969 + 3 ^ 40 * 6175072 * 2
def baseEnd_6175072 : Nat := 352308890235618804011263

theorem tailTrace_6175072 : CollatzResearch.WordTrace tailWord_6175072 prefixEnd_6175072 352308890235618804011263 := by
  unfold tailWord_6175072
  simp only [CollatzResearch.WordTrace]
  refine ⟨112611689342388118590127735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150148919123184158120170313 112611689342388118590127735)
  ·
    refine ⟨168917534013582177885191603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112611689342388118590127735 168917534013582177885191603)
    ·
      refine ⟨253376301020373266827787405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168917534013582177885191603 253376301020373266827787405)
      ·
        refine ⟨95016112882639975060420277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253376301020373266827787405 95016112882639975060420277)
        ·
          refine ⟨8907760582747497661914401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95016112882639975060420277 8907760582747497661914401)
          ·
            refine ⟨6680820437060623246435801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8907760582747497661914401 6680820437060623246435801)
            ·
              refine ⟨5010615327795467434826851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680820437060623246435801 5010615327795467434826851)
              ·
                refine ⟨7515922991693201152240277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010615327795467434826851 7515922991693201152240277)
                ·
                  refine ⟨352308890235618804011263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7515922991693201152240277 352308890235618804011263)
                  ·
                    rfl

theorem cell23_6175072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_6175072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175072 prefixEnd_6175072 := by exact prefixLift 6175072
  have htrace : WordTrace (prefixWord ++ tailWord_6175072) baseStart_6175072 baseEnd_6175072 := by
    simpa [prefixWord, tailWord_6175072, baseEnd_6175072] using wordTrace_append hprefix tailTrace_6175072
  have hstable : (prefixWord ++ tailWord_6175072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175072).length < 2 ^ (prefixWord ++ tailWord_6175072).sum := by decide
  have hdescent : baseEnd_6175072 < baseStart_6175072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175075 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 4, 3, 2]
def baseStart_6175075 : Nat := 118140960795 + 6175075 * 2 ^ 59
def prefixEnd_6175075 : Nat := 4983230072969 + 3 ^ 40 * 6175075 * 2
def baseEnd_6175075 : Nat := 3170781552562532724363853

theorem tailTrace_6175075 : CollatzResearch.WordTrace tailWord_6175075 prefixEnd_6175075 3170781552562532724363853 := by
  unfold tailWord_6175075
  simp only [CollatzResearch.WordTrace]
  refine ⟨225223488103765368692614679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150148992069176912461743119 225223488103765368692614679)
  ·
    refine ⟨337835232155648053038922019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225223488103765368692614679 337835232155648053038922019)
    ·
      refine ⟨506752848233472079558383029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337835232155648053038922019 506752848233472079558383029)
      ·
        refine ⟨47508079521888007458598409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 506752848233472079558383029 47508079521888007458598409)
        ·
          refine ⟨35631059641416005593948807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47508079521888007458598409 35631059641416005593948807)
          ·
            refine ⟨53446589462124008390923211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35631059641416005593948807 53446589462124008390923211)
            ·
              refine ⟨80169884193186012586384817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53446589462124008390923211 80169884193186012586384817)
              ·
                refine ⟨60127413144889509439788613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80169884193186012586384817 60127413144889509439788613)
                ·
                  refine ⟨11273889964666783019960365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60127413144889509439788613 11273889964666783019960365)
                  ·
                    refine ⟨4227708736750043632485137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11273889964666783019960365 4227708736750043632485137)
                    ·
                      refine ⟨3170781552562532724363853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227708736750043632485137 3170781552562532724363853)
                      ·
                        rfl

theorem cell23_6175075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_6175075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175075 prefixEnd_6175075 := by exact prefixLift 6175075
  have htrace : WordTrace (prefixWord ++ tailWord_6175075) baseStart_6175075 baseEnd_6175075 := by
    simpa [prefixWord, tailWord_6175075, baseEnd_6175075] using wordTrace_append hprefix tailTrace_6175075
  have hstable : (prefixWord ++ tailWord_6175075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175075).length < 2 ^ (prefixWord ++ tailWord_6175075).sum := by decide
  have hdescent : baseEnd_6175075 < baseStart_6175075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175115 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 2, 4]
def baseStart_6175115 : Nat := 118140960795 + 6175115 * 2 ^ 59
def prefixEnd_6175115 : Nat := 4983230072969 + 3 ^ 40 * 6175115 * 2
def baseEnd_6175115 : Nat := 1056934030596237522621223

theorem tailTrace_6175115 : CollatzResearch.WordTrace tailWord_6175115 prefixEnd_6175115 1056934030596237522621223 := by
  unfold tailWord_6175115
  simp only [CollatzResearch.WordTrace]
  refine ⟨225224947023620455524070799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150149964682413637016047199 225224947023620455524070799)
  ·
    refine ⟨337837420535430683286106199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225224947023620455524070799 337837420535430683286106199)
    ·
      refine ⟨506756130803146024929159299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337837420535430683286106199 506756130803146024929159299)
      ·
        refine ⟨760134196204719037393738949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506756130803146024929159299 760134196204719037393738949)
        ·
          refine ⟨142525161788384819511326053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 760134196204719037393738949 142525161788384819511326053)
          ·
            refine ⟨26723467835322153658373635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142525161788384819511326053 26723467835322153658373635)
            ·
              refine ⟨40085201752983230487560453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26723467835322153658373635 40085201752983230487560453)
              ·
                refine ⟨7515975328684355716417585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40085201752983230487560453 7515975328684355716417585)
                ·
                  refine ⟨5636981496513266787313189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515975328684355716417585 5636981496513266787313189)
                  ·
                    refine ⟨1056934030596237522621223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636981496513266787313189 1056934030596237522621223)
                    ·
                      rfl

theorem cell23_6175115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 4].length) (baseStart_6175115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175115 prefixEnd_6175115 := by exact prefixLift 6175115
  have htrace : WordTrace (prefixWord ++ tailWord_6175115) baseStart_6175115 baseEnd_6175115 := by
    simpa [prefixWord, tailWord_6175115, baseEnd_6175115] using wordTrace_append hprefix tailTrace_6175115
  have hstable : (prefixWord ++ tailWord_6175115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175115).length < 2 ^ (prefixWord ++ tailWord_6175115).sum := by decide
  have hdescent : baseEnd_6175115 < baseStart_6175115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175116 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_6175116 : Nat := 118140960795 + 6175116 * 2 ^ 59
def prefixEnd_6175116 : Nat := 4983230072969 + 3 ^ 40 * 6175116 * 2
def baseEnd_6175116 : Nat := 3170802605269367063951165

theorem tailTrace_6175116 : CollatzResearch.WordTrace tailWord_6175116 prefixEnd_6175116 3170802605269367063951165 := by
  unfold tailWord_6175116
  simp only [CollatzResearch.WordTrace]
  refine ⟨112612491748308416347428601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150149988997744555129904801 112612491748308416347428601)
  ·
    refine ⟨84459368811231312260571451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112612491748308416347428601 84459368811231312260571451)
    ·
      refine ⟨126689053216846968390857177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84459368811231312260571451 126689053216846968390857177)
      ·
        refine ⟨95016789912635226293142883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126689053216846968390857177 95016789912635226293142883)
        ·
          refine ⟨142525184868952839439714325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95016789912635226293142883 142525184868952839439714325)
          ·
            refine ⟨6680868040732164348736609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142525184868952839439714325 6680868040732164348736609)
            ·
              refine ⟨5010651030549123261552457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680868040732164348736609 5010651030549123261552457)
              ·
                refine ⟨3757988272911842446164343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010651030549123261552457 3757988272911842446164343)
                ·
                  refine ⟨5636982409367763669246515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757988272911842446164343 5636982409367763669246515)
                  ·
                    refine ⟨8455473614051645503869773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636982409367763669246515 8455473614051645503869773)
                    ·
                      refine ⟨3170802605269367063951165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8455473614051645503869773 3170802605269367063951165)
                      ·
                        rfl

theorem cell23_6175116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_6175116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175116 prefixEnd_6175116 := by exact prefixLift 6175116
  have htrace : WordTrace (prefixWord ++ tailWord_6175116) baseStart_6175116 baseEnd_6175116 := by
    simpa [prefixWord, tailWord_6175116, baseEnd_6175116] using wordTrace_append hprefix tailTrace_6175116
  have hstable : (prefixWord ++ tailWord_6175116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175116).length < 2 ^ (prefixWord ++ tailWord_6175116).sum := by decide
  have hdescent : baseEnd_6175116 < baseStart_6175116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175135 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6175135 : Nat := 118140960795 + 6175135 * 2 ^ 59
def prefixEnd_6175135 : Nat := 4983230072969 + 3 ^ 40 * 6175135 * 2
def baseEnd_6175135 : Nat := 3170812361401802489613577

theorem tailTrace_6175135 : CollatzResearch.WordTrace tailWord_6175135 prefixEnd_6175135 3170812361401802489613577 := by
  unfold tailWord_6175135
  simp only [CollatzResearch.WordTrace]
  refine ⟨225225676483547998939798859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150150450989031999293199239 225225676483547998939798859)
  ·
    refine ⟨337838514725321998409698289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225225676483547998939798859 337838514725321998409698289)
    ·
      refine ⟨253378886043991498807273717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337838514725321998409698289 253378886043991498807273717)
      ·
        refine ⟨23754270566624203013181911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253378886043991498807273717 23754270566624203013181911)
        ·
          refine ⟨35631405849936304519772867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23754270566624203013181911 35631405849936304519772867)
          ·
            refine ⟨53447108774904456779659301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35631405849936304519772867 53447108774904456779659301)
            ·
              refine ⟨10021332895294585646186119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53447108774904456779659301 10021332895294585646186119)
              ·
                refine ⟨15031999342941878469279179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021332895294585646186119 15031999342941878469279179)
                ·
                  refine ⟨22547999014412817703918769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15031999342941878469279179 22547999014412817703918769)
                  ·
                    refine ⟨16910999260809613277939077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22547999014412817703918769 16910999260809613277939077)
                    ·
                      refine ⟨3170812361401802489613577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16910999260809613277939077 3170812361401802489613577)
                      ·
                        rfl

theorem cell23_6175135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6175135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175135 prefixEnd_6175135 := by exact prefixLift 6175135
  have htrace : WordTrace (prefixWord ++ tailWord_6175135) baseStart_6175135 baseEnd_6175135 := by
    simpa [prefixWord, tailWord_6175135, baseEnd_6175135] using wordTrace_append hprefix tailTrace_6175135
  have hstable : (prefixWord ++ tailWord_6175135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175135).length < 2 ^ (prefixWord ++ tailWord_6175135).sum := by decide
  have hdescent : baseEnd_6175135 < baseStart_6175135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175156 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6175156 : Nat := 118140960795 + 6175156 * 2 ^ 59
def prefixEnd_6175156 : Nat := 4983230072969 + 3 ^ 40 * 6175156 * 2
def baseEnd_6175156 : Nat := 3170823144495546907450981

theorem tailTrace_6175156 : CollatzResearch.WordTrace tailWord_6175156 prefixEnd_6175156 3170823144495546907450981 := by
  unfold tailWord_6175156
  simp only [CollatzResearch.WordTrace]
  refine ⟨112613221208235959763156661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150150961610981279684208881 112613221208235959763156661)
  ·
    refine ⟨10557489488272121227795937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112613221208235959763156661 10557489488272121227795937)
    ·
      refine ⟨7918117116204090920846953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10557489488272121227795937 7918117116204090920846953)
      ·
        refine ⟨5938587837153068190635215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7918117116204090920846953 5938587837153068190635215)
        ·
          refine ⟨8907881755729602285952823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938587837153068190635215 8907881755729602285952823)
          ·
            refine ⟨13361822633594403428929235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907881755729602285952823 13361822633594403428929235)
            ·
              refine ⟨20042733950391605143393853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13361822633594403428929235 20042733950391605143393853)
              ·
                refine ⟨7516025231396851928772695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20042733950391605143393853 7516025231396851928772695)
                ·
                  refine ⟨11274037847095277893159043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516025231396851928772695 11274037847095277893159043)
                  ·
                    refine ⟨16911056770642916839738565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11274037847095277893159043 16911056770642916839738565)
                    ·
                      refine ⟨3170823144495546907450981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16911056770642916839738565 3170823144495546907450981)
                      ·
                        rfl

theorem cell23_6175156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6175156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175156 prefixEnd_6175156 := by exact prefixLift 6175156
  have htrace : WordTrace (prefixWord ++ tailWord_6175156) baseStart_6175156 baseEnd_6175156 := by
    simpa [prefixWord, tailWord_6175156, baseEnd_6175156] using wordTrace_append hprefix tailTrace_6175156
  have hstable : (prefixWord ++ tailWord_6175156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175156).length < 2 ^ (prefixWord ++ tailWord_6175156).sum := by decide
  have hdescent : baseEnd_6175156 < baseStart_6175156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175159 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_6175159 : Nat := 118140960795 + 6175159 * 2 ^ 59
def prefixEnd_6175159 : Nat := 4983230072969 + 3 ^ 40 * 6175159 * 2
def baseEnd_6175159 : Nat := 3170824684937510395713467

theorem tailTrace_6175159 : CollatzResearch.WordTrace tailWord_6175159 prefixEnd_6175159 3170824684937510395713467 := by
  unfold tailWord_6175159
  simp only [CollatzResearch.WordTrace]
  refine ⟨225226551835461051038672531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150151034556974034025781687 225226551835461051038672531)
  ·
    refine ⟨337839827753191576558008797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225226551835461051038672531 337839827753191576558008797)
    ·
      refine ⟨126689935407446841209253299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337839827753191576558008797 126689935407446841209253299)
      ·
        refine ⟨190034903111170261813879949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126689935407446841209253299 190034903111170261813879949)
        ·
          refine ⟨71263088666688848180204981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190034903111170261813879949 71263088666688848180204981)
          ·
            refine ⟨6680914562502079516894217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71263088666688848180204981 6680914562502079516894217)
            ·
              refine ⟨5010685921876559637670663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680914562502079516894217 5010685921876559637670663)
              ·
                refine ⟨7516028882814839456505995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010685921876559637670663 7516028882814839456505995)
                ·
                  refine ⟨11274043324222259184758993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516028882814839456505995 11274043324222259184758993)
                  ·
                    refine ⟨8455532493166694388569245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11274043324222259184758993 8455532493166694388569245)
                    ·
                      refine ⟨3170824684937510395713467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8455532493166694388569245 3170824684937510395713467)
                      ·
                        rfl

theorem cell23_6175159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_6175159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175159 prefixEnd_6175159 := by exact prefixLift 6175159
  have htrace : WordTrace (prefixWord ++ tailWord_6175159) baseStart_6175159 baseEnd_6175159 := by
    simpa [prefixWord, tailWord_6175159, baseEnd_6175159] using wordTrace_append hprefix tailTrace_6175159
  have hstable : (prefixWord ++ tailWord_6175159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175159).length < 2 ^ (prefixWord ++ tailWord_6175159).sum := by decide
  have hdescent : baseEnd_6175159 < baseStart_6175159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175186 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6175186 : Nat := 118140960795 + 6175186 * 2 ^ 59
def prefixEnd_6175186 : Nat := 4983230072969 + 3 ^ 40 * 6175186 * 2
def baseEnd_6175186 : Nat := 3170838548915181790075843

theorem tailTrace_6175186 : CollatzResearch.WordTrace tailWord_6175186 prefixEnd_6175186 3170838548915181790075843 := by
  unfold tailWord_6175186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56306884151590808662476353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150151691070908823099936941 56306884151590808662476353)
  ·
    refine ⟨42230163113693106496857265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56306884151590808662476353 42230163113693106496857265)
    ·
      refine ⟨31672622335269829872642949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42230163113693106496857265 31672622335269829872642949)
      ·
        refine ⟨5938616687863093101120553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31672622335269829872642949 5938616687863093101120553)
        ·
          refine ⟨4453962515897319825840415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5938616687863093101120553 4453962515897319825840415)
          ·
            refine ⟨6680943773845979738760623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453962515897319825840415 6680943773845979738760623)
            ·
              refine ⟨10021415660768969608140935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680943773845979738760623 10021415660768969608140935)
              ·
                refine ⟨15032123491153454412211403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021415660768969608140935 15032123491153454412211403)
                ·
                  refine ⟨22548185236730181618317105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15032123491153454412211403 22548185236730181618317105)
                  ·
                    refine ⟨16911138927547636213737829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22548185236730181618317105 16911138927547636213737829)
                    ·
                      refine ⟨3170838548915181790075843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16911138927547636213737829 3170838548915181790075843)
                      ·
                        rfl

theorem cell23_6175186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6175186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175186 prefixEnd_6175186 := by exact prefixLift 6175186
  have htrace : WordTrace (prefixWord ++ tailWord_6175186) baseStart_6175186 baseEnd_6175186 := by
    simpa [prefixWord, tailWord_6175186, baseEnd_6175186] using wordTrace_append hprefix tailTrace_6175186
  have hstable : (prefixWord ++ tailWord_6175186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175186).length < 2 ^ (prefixWord ++ tailWord_6175186).sum := by decide
  have hdescent : baseEnd_6175186 < baseStart_6175186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175199 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 1, 3, 2]
def baseStart_6175199 : Nat := 118140960795 + 6175199 * 2 ^ 59
def prefixEnd_6175199 : Nat := 4983230072969 + 3 ^ 40 * 6175199 * 2
def baseEnd_6175199 : Nat := 3170845224163690239213283

theorem tailTrace_6175199 : CollatzResearch.WordTrace tailWord_6175199 prefixEnd_6175199 3170845224163690239213283 := by
  unfold tailWord_6175199
  simp only [CollatzResearch.WordTrace]
  refine ⟨225228010755316137870128651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150152007170210758580085767 225228010755316137870128651)
  ·
    refine ⟨337842016132974206805192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225228010755316137870128651 337842016132974206805192977)
    ·
      refine ⟨253381512099730655103894733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337842016132974206805192977 253381512099730655103894733)
      ·
        refine ⟨95018067037398995663960525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253381512099730655103894733 95018067037398995663960525)
        ·
          refine ⟨35631775139024623373985197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95018067037398995663960525 35631775139024623373985197)
          ·
            refine ⟨13361915677134233765244449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35631775139024623373985197 13361915677134233765244449)
            ·
              refine ⟨10021436757850675323933337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13361915677134233765244449 10021436757850675323933337)
              ·
                refine ⟨7516077568388006492950003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10021436757850675323933337 7516077568388006492950003)
                ·
                  refine ⟨11274116352582009739425005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516077568388006492950003 11274116352582009739425005)
                  ·
                    refine ⟨4227793632218253652284377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11274116352582009739425005 4227793632218253652284377)
                    ·
                      refine ⟨3170845224163690239213283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227793632218253652284377 3170845224163690239213283)
                      ·
                        rfl

theorem cell23_6175199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_6175199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175199 prefixEnd_6175199 := by exact prefixLift 6175199
  have htrace : WordTrace (prefixWord ++ tailWord_6175199) baseStart_6175199 baseEnd_6175199 := by
    simpa [prefixWord, tailWord_6175199, baseEnd_6175199] using wordTrace_append hprefix tailTrace_6175199
  have hstable : (prefixWord ++ tailWord_6175199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175199).length < 2 ^ (prefixWord ++ tailWord_6175199).sum := by decide
  have hdescent : baseEnd_6175199 < baseStart_6175199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175212 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_6175212 : Nat := 118140960795 + 6175212 * 2 ^ 59
def prefixEnd_6175212 : Nat := 4983230072969 + 3 ^ 40 * 6175212 * 2
def baseEnd_6175212 : Nat := 3170851899412198688350723

theorem tailTrace_6175212 : CollatzResearch.WordTrace tailWord_6175212 prefixEnd_6175212 3170851899412198688350723 := by
  unfold tailWord_6175212
  simp only [CollatzResearch.WordTrace]
  refine ⟨112614242452134520545175945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150152323269512694060234593 112614242452134520545175945)
  ·
    refine ⟨84460681839100890408881959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112614242452134520545175945 84460681839100890408881959)
    ·
      refine ⟨126691022758651335613322939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84460681839100890408881959 126691022758651335613322939)
      ·
        refine ⟨190036534137977003419984409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126691022758651335613322939 190036534137977003419984409)
        ·
          refine ⟨142527400603482752564988307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190036534137977003419984409 142527400603482752564988307)
          ·
            refine ⟨213791100905224128847482461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142527400603482752564988307 213791100905224128847482461)
            ·
              refine ⟨80171662839459048317805923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213791100905224128847482461 80171662839459048317805923)
              ·
                refine ⟨120257494259188572476708885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80171662839459048317805923 120257494259188572476708885)
                ·
                  refine ⟨5637070043399464334845729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120257494259188572476708885 5637070043399464334845729)
                  ·
                    refine ⟨4227802532549598251134297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637070043399464334845729 4227802532549598251134297)
                    ·
                      refine ⟨3170851899412198688350723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227802532549598251134297 3170851899412198688350723)
                      ·
                        rfl

theorem cell23_6175212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_6175212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175212 prefixEnd_6175212 := by exact prefixLift 6175212
  have htrace : WordTrace (prefixWord ++ tailWord_6175212) baseStart_6175212 baseEnd_6175212 := by
    simpa [prefixWord, tailWord_6175212, baseEnd_6175212] using wordTrace_append hprefix tailTrace_6175212
  have hstable : (prefixWord ++ tailWord_6175212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175212).length < 2 ^ (prefixWord ++ tailWord_6175212).sum := by decide
  have hdescent : baseEnd_6175212 < baseStart_6175212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_6175228 : Nat := 118140960795 + 6175228 * 2 ^ 59
def prefixEnd_6175228 : Nat := 4983230072969 + 3 ^ 40 * 6175228 * 2
def baseEnd_6175228 : Nat := 3170860115102670625750649

theorem tailTrace_6175228 : CollatzResearch.WordTrace tailWord_6175228 prefixEnd_6175228 3170860115102670625750649 := by
  unfold tailWord_6175228
  simp only [CollatzResearch.WordTrace]
  refine ⟨112614534236105537911467169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150152712314807383881956225 112614534236105537911467169)
  ·
    refine ⟨84460900677079153433600377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112614534236105537911467169 84460900677079153433600377)
    ·
      refine ⟨63345675507809365075200283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84460900677079153433600377 63345675507809365075200283)
      ·
        refine ⟨95018513261714047612800425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63345675507809365075200283 95018513261714047612800425)
        ·
          refine ⟨71263884946285535709600319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95018513261714047612800425 71263884946285535709600319)
          ·
            refine ⟨106895827419428303564400479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71263884946285535709600319 106895827419428303564400479)
            ·
              refine ⟨160343741129142455346600719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106895827419428303564400479 160343741129142455346600719)
              ·
                refine ⟨240515611693713683019901079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160343741129142455346600719 240515611693713683019901079)
                ·
                  refine ⟨360773417540570524529851619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240515611693713683019901079 360773417540570524529851619)
                  ·
                    refine ⟨541160126310855786794777429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360773417540570524529851619 541160126310855786794777429)
                    ·
                      refine ⟨3170860115102670625750649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 541160126310855786794777429 3170860115102670625750649)
                      ·
                        rfl

theorem cell23_6175228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_6175228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175228 prefixEnd_6175228 := by exact prefixLift 6175228
  have htrace : WordTrace (prefixWord ++ tailWord_6175228) baseStart_6175228 baseEnd_6175228 := by
    simpa [prefixWord, tailWord_6175228, baseEnd_6175228] using wordTrace_append hprefix tailTrace_6175228
  have hstable : (prefixWord ++ tailWord_6175228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175228).length < 2 ^ (prefixWord ++ tailWord_6175228).sum := by decide
  have hdescent : baseEnd_6175228 < baseStart_6175228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175229 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_6175229 : Nat := 118140960795 + 6175229 * 2 ^ 59
def prefixEnd_6175229 : Nat := 4983230072969 + 3 ^ 40 * 6175229 * 2
def baseEnd_6175229 : Nat := 3170860628583325121838145

theorem tailTrace_6175229 : CollatzResearch.WordTrace tailWord_6175229 prefixEnd_6175229 3170860628583325121838145 := by
  unfold tailWord_6175229
  simp only [CollatzResearch.WordTrace]
  refine ⟨225229104945207452993720741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150152736630138301995813827 225229104945207452993720741)
  ·
    refine ⟨42230457177226397436322639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225229104945207452993720741 42230457177226397436322639)
    ·
      refine ⟨63345685765839596154483959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42230457177226397436322639 63345685765839596154483959)
      ·
        refine ⟨95018528648759394231725939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63345685765839596154483959 95018528648759394231725939)
        ·
          refine ⟨142527792973139091347588909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95018528648759394231725939 142527792973139091347588909)
          ·
            refine ⟨53447922364927159255345841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142527792973139091347588909 53447922364927159255345841)
            ·
              refine ⟨40085941773695369441509381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53447922364927159255345841 40085941773695369441509381)
              ·
                refine ⟨7516114082567881770283009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40085941773695369441509381 7516114082567881770283009)
                ·
                  refine ⟨5637085561925911327712257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7516114082567881770283009 5637085561925911327712257)
                  ·
                    refine ⟨4227814171444433495784193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637085561925911327712257 4227814171444433495784193)
                    ·
                      refine ⟨3170860628583325121838145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227814171444433495784193 3170860628583325121838145)
                      ·
                        rfl

theorem cell23_6175229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_6175229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175229 prefixEnd_6175229 := by exact prefixLift 6175229
  have htrace : WordTrace (prefixWord ++ tailWord_6175229) baseStart_6175229 baseEnd_6175229 := by
    simpa [prefixWord, tailWord_6175229, baseEnd_6175229] using wordTrace_append hprefix tailTrace_6175229
  have hstable : (prefixWord ++ tailWord_6175229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175229).length < 2 ^ (prefixWord ++ tailWord_6175229).sum := by decide
  have hdescent : baseEnd_6175229 < baseStart_6175229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175246 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6175246 : Nat := 118140960795 + 6175246 * 2 ^ 59
def prefixEnd_6175246 : Nat := 4983230072969 + 3 ^ 40 * 6175246 * 2
def baseEnd_6175246 : Nat := 3170869357754451555325567

theorem tailTrace_6175246 : CollatzResearch.WordTrace tailWord_6175246 prefixEnd_6175246 3170869357754451555325567 := by
  unfold tailWord_6175246
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153715623268233112136199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150153149990763909931393061 28153715623268233112136199)
  ·
    refine ⟨42230573434902349668204299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28153715623268233112136199 42230573434902349668204299)
    ·
      refine ⟨63345860152353524502306449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42230573434902349668204299 63345860152353524502306449)
      ·
        refine ⟨47509395114265143376729837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63345860152353524502306449 47509395114265143376729837)
        ·
          refine ⟨17816023167849428766273689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47509395114265143376729837 17816023167849428766273689)
          ·
            refine ⟨13362017375887071574705267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17816023167849428766273689 13362017375887071574705267)
            ·
              refine ⟨20043026063830607362057901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362017375887071574705267 20043026063830607362057901)
              ·
                refine ⟨7516134773936477760771713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20043026063830607362057901 7516134773936477760771713)
                ·
                  refine ⟨5637101080452358320578785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7516134773936477760771713 5637101080452358320578785)
                  ·
                    refine ⟨4227825810339268740434089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637101080452358320578785 4227825810339268740434089)
                    ·
                      refine ⟨3170869357754451555325567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227825810339268740434089 3170869357754451555325567)
                      ·
                        rfl

theorem cell23_6175246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6175246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175246 prefixEnd_6175246 := by exact prefixLift 6175246
  have htrace : WordTrace (prefixWord ++ tailWord_6175246) baseStart_6175246 baseEnd_6175246 := by
    simpa [prefixWord, tailWord_6175246, baseEnd_6175246] using wordTrace_append hprefix tailTrace_6175246
  have hstable : (prefixWord ++ tailWord_6175246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175246).length < 2 ^ (prefixWord ++ tailWord_6175246).sum := by decide
  have hdescent : baseEnd_6175246 < baseStart_6175246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175286 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_6175286 : Nat := 118140960795 + 6175286 * 2 ^ 59
def prefixEnd_6175286 : Nat := 4983230072969 + 3 ^ 40 * 6175286 * 2
def baseEnd_6175286 : Nat := 352321099664514599869487

theorem tailTrace_6175286 : CollatzResearch.WordTrace tailWord_6175286 prefixEnd_6175286 352321099664514599869487 := by
  unfold tailWord_6175286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14076948994125059483034107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150154122604000634485697141 14076948994125059483034107)
  ·
    refine ⟨21115423491187589224551161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14076948994125059483034107 21115423491187589224551161)
    ·
      refine ⟨15836567618390691918413371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21115423491187589224551161 15836567618390691918413371)
      ·
        refine ⟨23754851427586037877620057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15836567618390691918413371 23754851427586037877620057)
        ·
          refine ⟨17816138570689528408215043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23754851427586037877620057 17816138570689528408215043)
          ·
            refine ⟨26724207856034292612322565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17816138570689528408215043 26724207856034292612322565)
            ·
              refine ⟨5010788973006429864810481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26724207856034292612322565 5010788973006429864810481)
              ·
                refine ⟨3758091729754822398607861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010788973006429864810481 3758091729754822398607861)
                ·
                  refine ⟨352321099664514599869487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3758091729754822398607861 352321099664514599869487)
                  ·
                    rfl

theorem cell23_6175286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_6175286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175286 prefixEnd_6175286 := by exact prefixLift 6175286
  have htrace : WordTrace (prefixWord ++ tailWord_6175286) baseStart_6175286 baseEnd_6175286 := by
    simpa [prefixWord, tailWord_6175286, baseEnd_6175286] using wordTrace_append hprefix tailTrace_6175286
  have hstable : (prefixWord ++ tailWord_6175286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175286).length < 2 ^ (prefixWord ++ tailWord_6175286).sum := by decide
  have hdescent : baseEnd_6175286 < baseStart_6175286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175329 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6175329 : Nat := 118140960795 + 6175329 * 2 ^ 59
def prefixEnd_6175329 : Nat := 4983230072969 + 3 ^ 40 * 6175329 * 2
def baseEnd_6175329 : Nat := 1056970658882924910195895

theorem tailTrace_6175329 : CollatzResearch.WordTrace tailWord_6175329 prefixEnd_6175329 1056970658882924910195895 := by
  unfold tailWord_6175329
  simp only [CollatzResearch.WordTrace]
  refine ⟨225232752244845170072361041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150155168163230113381574027 225232752244845170072361041)
  ·
    refine ⟨168924564183633877554270781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225232752244845170072361041 168924564183633877554270781)
    ·
      refine ⟨63346711568862704082851543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168924564183633877554270781 63346711568862704082851543)
      ·
        refine ⟨95020067353294056124277315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63346711568862704082851543 95020067353294056124277315)
        ·
          refine ⟨142530101029941084186415973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95020067353294056124277315 142530101029941084186415973)
          ·
            refine ⟨26724393943113953284952995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142530101029941084186415973 26724393943113953284952995)
            ·
              refine ⟨40086590914670929927429493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26724393943113953284952995 40086590914670929927429493)
              ·
                refine ⟨3758117898250399680696515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40086590914670929927429493 3758117898250399680696515)
                ·
                  refine ⟨5637176847375599521044773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758117898250399680696515 5637176847375599521044773)
                  ·
                    refine ⟨1056970658882924910195895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5637176847375599521044773 1056970658882924910195895)
                    ·
                      rfl

theorem cell23_6175329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6175329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175329 prefixEnd_6175329 := by exact prefixLift 6175329
  have htrace : WordTrace (prefixWord ++ tailWord_6175329) baseStart_6175329 baseEnd_6175329 := by
    simpa [prefixWord, tailWord_6175329, baseEnd_6175329] using wordTrace_append hprefix tailTrace_6175329
  have hstable : (prefixWord ++ tailWord_6175329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175329).length < 2 ^ (prefixWord ++ tailWord_6175329).sum := by decide
  have hdescent : baseEnd_6175329 < baseStart_6175329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175342 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_6175342 : Nat := 118140960795 + 6175342 * 2 ^ 59
def prefixEnd_6175342 : Nat := 4983230072969 + 3 ^ 40 * 6175342 * 2
def baseEnd_6175342 : Nat := 352324294655253686636125

theorem tailTrace_6175342 : CollatzResearch.WordTrace tailWord_6175342 prefixEnd_6175342 352324294655253686636125 := by
  unfold tailWord_6175342
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154153299224759161573035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150155484262532048861722853 28154153299224759161573035)
  ·
    refine ⟨42231229948837138742359553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28154153299224759161573035 42231229948837138742359553)
    ·
      refine ⟨31673422461627854056769665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42231229948837138742359553 31673422461627854056769665)
      ·
        refine ⟨23755066846220890542577249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31673422461627854056769665 23755066846220890542577249)
        ·
          refine ⟨17816300134665667906932937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23755066846220890542577249 17816300134665667906932937)
          ·
            refine ⟨13362225100999250930199703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17816300134665667906932937 13362225100999250930199703)
            ·
              refine ⟨20043337651498876395299555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362225100999250930199703 20043337651498876395299555)
              ·
                refine ⟨30065006477248314592949333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20043337651498876395299555 30065006477248314592949333)
                ·
                  refine ⟨352324294655253686636125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30065006477248314592949333 352324294655253686636125)
                  ·
                    rfl

theorem cell23_6175342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_6175342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175342 prefixEnd_6175342 := by exact prefixLift 6175342
  have htrace : WordTrace (prefixWord ++ tailWord_6175342) baseStart_6175342 baseEnd_6175342 := by
    simpa [prefixWord, tailWord_6175342, baseEnd_6175342] using wordTrace_append hprefix tailTrace_6175342
  have hstable : (prefixWord ++ tailWord_6175342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175342).length < 2 ^ (prefixWord ++ tailWord_6175342).sum := by decide
  have hdescent : baseEnd_6175342 < baseStart_6175342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175352 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_6175352 : Nat := 118140960795 + 6175352 * 2 ^ 59
def prefixEnd_6175352 : Nat := 4983230072969 + 3 ^ 40 * 6175352 * 2
def baseEnd_6175352 : Nat := 3170923786703828140600079

theorem tailTrace_6175352 : CollatzResearch.WordTrace tailWord_6175352 prefixEnd_6175352 3170923786703828140600079 := by
  unfold tailWord_6175352
  simp only [CollatzResearch.WordTrace]
  refine ⟨112616795561880922500224155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150155727415841230000298873 112616795561880922500224155)
  ·
    refine ⟨168925193342821383750336233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112616795561880922500224155 168925193342821383750336233)
    ·
      refine ⟨126693895007116037812752175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168925193342821383750336233 126693895007116037812752175)
      ·
        refine ⟨190040842510674056719128263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126693895007116037812752175 190040842510674056719128263)
        ·
          refine ⟨285061263766011085078692395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190040842510674056719128263 285061263766011085078692395)
          ·
            refine ⟨427591895649016627618038593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285061263766011085078692395 427591895649016627618038593)
            ·
              refine ⟨320693921736762470713528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427591895649016627618038593 320693921736762470713528945)
              ·
                refine ⟨240520441302571853035146709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320693921736762470713528945 240520441302571853035146709)
                ·
                  refine ⟨5637197843029027805511251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 240520441302571853035146709 5637197843029027805511251)
                  ·
                    refine ⟨8455796764543541708266877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5637197843029027805511251 8455796764543541708266877)
                    ·
                      refine ⟨3170923786703828140600079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8455796764543541708266877 3170923786703828140600079)
                      ·
                        rfl

theorem cell23_6175352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_6175352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175352 prefixEnd_6175352 := by exact prefixLift 6175352
  have htrace : WordTrace (prefixWord ++ tailWord_6175352) baseStart_6175352 baseEnd_6175352 := by
    simpa [prefixWord, tailWord_6175352, baseEnd_6175352] using wordTrace_append hprefix tailTrace_6175352
  have hstable : (prefixWord ++ tailWord_6175352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175352).length < 2 ^ (prefixWord ++ tailWord_6175352).sum := by decide
  have hdescent : baseEnd_6175352 < baseStart_6175352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175355 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 3, 5]
def baseStart_6175355 : Nat := 118140960795 + 6175355 * 2 ^ 59
def prefixEnd_6175355 : Nat := 4983230072969 + 3 ^ 40 * 6175355 * 2
def baseEnd_6175355 : Nat := 1056975109048597209620855

theorem tailTrace_6175355 : CollatzResearch.WordTrace tailWord_6175355 prefixEnd_6175355 1056975109048597209620855 := by
  unfold tailWord_6175355
  simp only [CollatzResearch.WordTrace]
  refine ⟨225233700542750976512807519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150155800361833984341871679 225233700542750976512807519)
  ·
    refine ⟨337850550814126464769211279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225233700542750976512807519 337850550814126464769211279)
    ·
      refine ⟨506775826221189697153816919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337850550814126464769211279 506775826221189697153816919)
      ·
        refine ⟨760163739331784545730725379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506775826221189697153816919 760163739331784545730725379)
        ·
          refine ⟨1140245608997676818596088069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760163739331784545730725379 1140245608997676818596088069)
          ·
            refine ⟨213796051687064403486766513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1140245608997676818596088069 213796051687064403486766513)
            ·
              refine ⟨160347038765298302615074885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213796051687064403486766513 160347038765298302615074885)
              ·
                refine ⟨30065069768493431740326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160347038765298302615074885 30065069768493431740326541)
                ·
                  refine ⟨11274401163185036902622453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30065069768493431740326541 11274401163185036902622453)
                  ·
                    refine ⟨1056975109048597209620855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11274401163185036902622453 1056975109048597209620855)
                    ·
                      rfl

theorem cell23_6175355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].length) (baseStart_6175355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175355 prefixEnd_6175355 := by exact prefixLift 6175355
  have htrace : WordTrace (prefixWord ++ tailWord_6175355) baseStart_6175355 baseEnd_6175355 := by
    simpa [prefixWord, tailWord_6175355, baseEnd_6175355] using wordTrace_append hprefix tailTrace_6175355
  have hstable : (prefixWord ++ tailWord_6175355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175355).length < 2 ^ (prefixWord ++ tailWord_6175355).sum := by decide
  have hdescent : baseEnd_6175355 < baseStart_6175355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175385 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_6175385 : Nat := 118140960795 + 6175385 * 2 ^ 59
def prefixEnd_6175385 : Nat := 4983230072969 + 3 ^ 40 * 6175385 * 2
def baseEnd_6175385 : Nat := 1056980243855142170495809

theorem tailTrace_6175385 : CollatzResearch.WordTrace tailWord_6175385 prefixEnd_6175385 1056980243855142170495809 := by
  unfold tailWord_6175385
  simp only [CollatzResearch.WordTrace]
  refine ⟨225234794732642291636399609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150156529821761527757599739 225234794732642291636399609)
  ·
    refine ⟨168926096049481718727299707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225234794732642291636399609 168926096049481718727299707)
    ·
      refine ⟨253389144074222578090949561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168926096049481718727299707 253389144074222578090949561)
      ·
        refine ⟨190041858055666933568212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253389144074222578090949561 190041858055666933568212171)
        ·
          refine ⟨285062787083500400352318257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190041858055666933568212171 285062787083500400352318257)
          ·
            refine ⟨213797090312625300264238693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285062787083500400352318257 213797090312625300264238693)
            ·
              refine ⟨40086954433617243799544755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213797090312625300264238693 40086954433617243799544755)
              ·
                refine ⟨60130431650425865699317133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40086954433617243799544755 60130431650425865699317133)
                ·
                  refine ⟨22548911868909699637243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60130431650425865699317133 22548911868909699637243925)
                  ·
                    refine ⟨1056980243855142170495809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22548911868909699637243925 1056980243855142170495809)
                    ·
                      rfl

theorem cell23_6175385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_6175385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175385 prefixEnd_6175385 := by exact prefixLift 6175385
  have htrace : WordTrace (prefixWord ++ tailWord_6175385) baseStart_6175385 baseEnd_6175385 := by
    simpa [prefixWord, tailWord_6175385, baseEnd_6175385] using wordTrace_append hprefix tailTrace_6175385
  have hstable : (prefixWord ++ tailWord_6175385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175385).length < 2 ^ (prefixWord ++ tailWord_6175385).sum := by decide
  have hdescent : baseEnd_6175385 < baseStart_6175385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175422 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6175422 : Nat := 118140960795 + 6175422 * 2 ^ 59
def prefixEnd_6175422 : Nat := 4983230072969 + 3 ^ 40 * 6175422 * 2
def baseEnd_6175422 : Nat := 3170959730349642866724757

theorem tailTrace_6175422 : CollatzResearch.WordTrace tailWord_6175422 prefixEnd_6175422 3170959730349642866724757 := by
  unfold tailWord_6175422
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154518029188530869437065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150157429489005497970331013 28154518029188530869437065)
  ·
    refine ⟨21115888521891398152077799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28154518029188530869437065 21115888521891398152077799)
    ·
      refine ⟨31673832782837097228116699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21115888521891398152077799 31673832782837097228116699)
      ·
        refine ⟨47510749174255645842175049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31673832782837097228116699 47510749174255645842175049)
        ·
          refine ⟨35633061880691734381631287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47510749174255645842175049 35633061880691734381631287)
          ·
            refine ⟨53449592821037601572446931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35633061880691734381631287 53449592821037601572446931)
            ·
              refine ⟨80174389231556402358670397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53449592821037601572446931 80174389231556402358670397)
              ·
                refine ⟨30065395961833650884501399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80174389231556402358670397 30065395961833650884501399)
                ·
                  refine ⟨45098093942750476326752099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30065395961833650884501399 45098093942750476326752099)
                  ·
                    refine ⟨67647140914125714490128149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45098093942750476326752099 67647140914125714490128149)
                    ·
                      refine ⟨3170959730349642866724757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67647140914125714490128149 3170959730349642866724757)
                      ·
                        rfl

theorem cell23_6175422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6175422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175422 prefixEnd_6175422 := by exact prefixLift 6175422
  have htrace : WordTrace (prefixWord ++ tailWord_6175422) baseStart_6175422 baseEnd_6175422 := by
    simpa [prefixWord, tailWord_6175422, baseEnd_6175422] using wordTrace_append hprefix tailTrace_6175422
  have hstable : (prefixWord ++ tailWord_6175422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175422).length < 2 ^ (prefixWord ++ tailWord_6175422).sum := by decide
  have hdescent : baseEnd_6175422 < baseStart_6175422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175460 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_6175460 : Nat := 118140960795 + 6175460 * 2 ^ 59
def prefixEnd_6175460 : Nat := 4983230072969 + 3 ^ 40 * 6175460 * 2
def baseEnd_6175460 : Nat := 3170979242614513718049583

theorem tailTrace_6175460 : CollatzResearch.WordTrace tailWord_6175460 prefixEnd_6175460 3170979242614513718049583 := by
  unfold tailWord_6175460
  simp only [CollatzResearch.WordTrace]
  refine ⟨112618765103685289722689917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150158353471580386296919889 112618765103685289722689917)
  ·
    refine ⟨42232036913881983646008719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112618765103685289722689917 42232036913881983646008719)
    ·
      refine ⟨63348055370822975469013079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42232036913881983646008719 63348055370822975469013079)
      ·
        refine ⟨95022083056234463203519619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63348055370822975469013079 95022083056234463203519619)
        ·
          refine ⟨142533124584351694805279429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95022083056234463203519619 142533124584351694805279429)
          ·
            refine ⟨26724960859565942775989893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142533124584351694805279429 26724960859565942775989893)
            ·
              refine ⟨5010930161168614270498105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26724960859565942775989893 5010930161168614270498105)
              ·
                refine ⟨3758197620876460702873579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010930161168614270498105 3758197620876460702873579)
                ·
                  refine ⟨5637296431314691054310369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758197620876460702873579 5637296431314691054310369)
                  ·
                    refine ⟨4227972323486018290732777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637296431314691054310369 4227972323486018290732777)
                    ·
                      refine ⟨3170979242614513718049583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227972323486018290732777 3170979242614513718049583)
                      ·
                        rfl

theorem cell23_6175460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_6175460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175460 prefixEnd_6175460 := by exact prefixLift 6175460
  have htrace : WordTrace (prefixWord ++ tailWord_6175460) baseStart_6175460 baseEnd_6175460 := by
    simpa [prefixWord, tailWord_6175460, baseEnd_6175460] using wordTrace_append hprefix tailTrace_6175460
  have hstable : (prefixWord ++ tailWord_6175460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175460).length < 2 ^ (prefixWord ++ tailWord_6175460).sum := by decide
  have hdescent : baseEnd_6175460 < baseStart_6175460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175477 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6175477 : Nat := 118140960795 + 6175477 * 2 ^ 59
def prefixEnd_6175477 : Nat := 4983230072969 + 3 ^ 40 * 6175477 * 2
def baseEnd_6175477 : Nat := 3170987971785640151537005

theorem tailTrace_6175477 : CollatzResearch.WordTrace tailWord_6175477 prefixEnd_6175477 3170987971785640151537005 := by
  unfold tailWord_6175477
  simp only [CollatzResearch.WordTrace]
  refine ⟨225238150248308991348748685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150158766832205994232499123 225238150248308991348748685)
  ·
    refine ⟨84464306343115871755780757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225238150248308991348748685 84464306343115871755780757)
    ·
      refine ⟨3959264359833556488552223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84464306343115871755780757 3959264359833556488552223)
      ·
        refine ⟨5938896539750334732828335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3959264359833556488552223 5938896539750334732828335)
        ·
          refine ⟨8908344809625502099242503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938896539750334732828335 8908344809625502099242503)
          ·
            refine ⟨13362517214438253148863755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908344809625502099242503 13362517214438253148863755)
            ·
              refine ⟨20043775821657379723295633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362517214438253148863755 20043775821657379723295633)
              ·
                refine ⟨15032831866243034792471725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20043775821657379723295633 15032831866243034792471725)
                ·
                  refine ⟨5637311949841138047176897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15032831866243034792471725 5637311949841138047176897)
                  ·
                    refine ⟨4227983962380853535382673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637311949841138047176897 4227983962380853535382673)
                    ·
                      refine ⟨3170987971785640151537005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227983962380853535382673 3170987971785640151537005)
                      ·
                        rfl

theorem cell23_6175477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6175477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175477 prefixEnd_6175477 := by exact prefixLift 6175477
  have htrace : WordTrace (prefixWord ++ tailWord_6175477) baseStart_6175477 baseEnd_6175477 := by
    simpa [prefixWord, tailWord_6175477, baseEnd_6175477] using wordTrace_append hprefix tailTrace_6175477
  have hstable : (prefixWord ++ tailWord_6175477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175477).length < 2 ^ (prefixWord ++ tailWord_6175477).sum := by decide
  have hdescent : baseEnd_6175477 < baseStart_6175477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175492 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_6175492 : Nat := 118140960795 + 6175492 * 2 ^ 59
def prefixEnd_6175492 : Nat := 4983230072969 + 3 ^ 40 * 6175492 * 2
def baseEnd_6175492 : Nat := 1056998557998485864283145

theorem tailTrace_6175492 : CollatzResearch.WordTrace tailWord_6175492 prefixEnd_6175492 1056998557998485864283145 := by
  unfold tailWord_6175492
  simp only [CollatzResearch.WordTrace]
  refine ⟨112619348671627324455272365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150159131562169765940363153 112619348671627324455272365)
  ·
    refine ⟨42232255751860246670727137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112619348671627324455272365 42232255751860246670727137)
    ·
      refine ⟨31674191813895185003045353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42232255751860246670727137 31674191813895185003045353)
      ·
        refine ⟨23755643860421388752284015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31674191813895185003045353 23755643860421388752284015)
        ·
          refine ⟨35633465790632083128426023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23755643860421388752284015 35633465790632083128426023)
          ·
            refine ⟨53450198685948124692639035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35633465790632083128426023 53450198685948124692639035)
            ·
              refine ⟨80175298028922187038958553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53450198685948124692639035 80175298028922187038958553)
              ·
                refine ⟨60131473521691640279218915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80175298028922187038958553 60131473521691640279218915)
                ·
                  refine ⟨90197210282537460418828373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60131473521691640279218915 90197210282537460418828373)
                  ·
                    refine ⟨1056998557998485864283145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90197210282537460418828373 1056998557998485864283145)
                    ·
                      rfl

theorem cell23_6175492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_6175492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175492 prefixEnd_6175492 := by exact prefixLift 6175492
  have htrace : WordTrace (prefixWord ++ tailWord_6175492) baseStart_6175492 baseEnd_6175492 := by
    simpa [prefixWord, tailWord_6175492, baseEnd_6175492] using wordTrace_append hprefix tailTrace_6175492
  have hstable : (prefixWord ++ tailWord_6175492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175492).length < 2 ^ (prefixWord ++ tailWord_6175492).sum := by decide
  have hdescent : baseEnd_6175492 < baseStart_6175492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175502 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6175502 : Nat := 118140960795 + 6175502 * 2 ^ 59
def prefixEnd_6175502 : Nat := 4983230072969 + 3 ^ 40 * 6175502 * 2
def baseEnd_6175502 : Nat := 3171000808802002553724389

theorem tailTrace_6175502 : CollatzResearch.WordTrace tailWord_6175502 prefixEnd_6175502 3171000808802002553724389 := by
  unfold tailWord_6175502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154882759152302577301095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150159374715478947078939173 28154882759152302577301095)
  ·
    refine ⟨42232324138728453865951643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28154882759152302577301095 42232324138728453865951643)
    ·
      refine ⟨63348486208092680798927465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42232324138728453865951643 63348486208092680798927465)
      ·
        refine ⟨47511364656069510599195599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63348486208092680798927465 47511364656069510599195599)
        ·
          refine ⟨71267046984104265898793399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47511364656069510599195599 71267046984104265898793399)
          ·
            refine ⟨106900570476156398848190099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71267046984104265898793399 106900570476156398848190099)
            ·
              refine ⟨160350855714234598272285149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106900570476156398848190099 160350855714234598272285149)
              ·
                refine ⟨60131570892837974352106931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160350855714234598272285149 60131570892837974352106931)
                ·
                  refine ⟨90197356339256961528160397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60131570892837974352106931 90197356339256961528160397)
                  ·
                    refine ⟨33824008627221360573060149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90197356339256961528160397 33824008627221360573060149)
                    ·
                      refine ⟨3171000808802002553724389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33824008627221360573060149 3171000808802002553724389)
                      ·
                        rfl

theorem cell23_6175502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6175502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175502 prefixEnd_6175502 := by exact prefixLift 6175502
  have htrace : WordTrace (prefixWord ++ tailWord_6175502) baseStart_6175502 baseEnd_6175502 := by
    simpa [prefixWord, tailWord_6175502, baseEnd_6175502] using wordTrace_append hprefix tailTrace_6175502
  have hstable : (prefixWord ++ tailWord_6175502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175502).length < 2 ^ (prefixWord ++ tailWord_6175502).sum := by decide
  have hdescent : baseEnd_6175502 < baseStart_6175502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175552 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_6175552 : Nat := 118140960795 + 6175552 * 2 ^ 59
def prefixEnd_6175552 : Nat := 4983230072969 + 3 ^ 40 * 6175552 * 2
def baseEnd_6175552 : Nat := 1057008827611575786033053

theorem tailTrace_6175552 : CollatzResearch.WordTrace tailWord_6175552 prefixEnd_6175552 1057008827611575786033053 := by
  unfold tailWord_6175552
  simp only [CollatzResearch.WordTrace]
  refine ⟨112620442861518639578864455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150160590482024852771819273 112620442861518639578864455)
  ·
    refine ⟨168930664292277959368296683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112620442861518639578864455 168930664292277959368296683)
    ·
      refine ⟨253395996438416939052445025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168930664292277959368296683 253395996438416939052445025)
      ·
        refine ⟨190046997328812704289333769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253395996438416939052445025 190046997328812704289333769)
        ·
          refine ⟨142535247996609528217000327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190046997328812704289333769 142535247996609528217000327)
          ·
            refine ⟨213802871994914292325500491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142535247996609528217000327 213802871994914292325500491)
            ·
              refine ⟨320704307992371438488250737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213802871994914292325500491 320704307992371438488250737)
              ·
                refine ⟨240528230994278578866188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320704307992371438488250737 240528230994278578866188053)
                ·
                  refine ⟨11274760827856808384352565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240528230994278578866188053 11274760827856808384352565)
                  ·
                    refine ⟨1057008827611575786033053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11274760827856808384352565 1057008827611575786033053)
                    ·
                      rfl

theorem cell23_6175552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_6175552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175552 prefixEnd_6175552 := by exact prefixLift 6175552
  have htrace : WordTrace (prefixWord ++ tailWord_6175552) baseStart_6175552 baseEnd_6175552 := by
    simpa [prefixWord, tailWord_6175552, baseEnd_6175552] using wordTrace_append hprefix tailTrace_6175552
  have hstable : (prefixWord ++ tailWord_6175552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175552).length < 2 ^ (prefixWord ++ tailWord_6175552).sum := by decide
  have hdescent : baseEnd_6175552 < baseStart_6175552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175559 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_6175559 : Nat := 118140960795 + 6175559 * 2 ^ 59
def prefixEnd_6175559 : Nat := 4983230072969 + 3 ^ 40 * 6175559 * 2
def baseEnd_6175559 : Nat := 3171030077199308830711627

theorem tailTrace_6175559 : CollatzResearch.WordTrace tailWord_6175559 prefixEnd_6175559 3171030077199308830711627 := by
  unfold tailWord_6175559
  simp only [CollatzResearch.WordTrace]
  refine ⟨225241141034011919353233731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150160760689341279568822487 225241141034011919353233731)
  ·
    refine ⟨337861711551017879029850597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225241141034011919353233731 337861711551017879029850597)
    ·
      refine ⟨63349070915815852318096987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337861711551017879029850597 63349070915815852318096987)
      ·
        refine ⟨95023606373723778477145481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63349070915815852318096987 95023606373723778477145481)
        ·
          refine ⟨71267704780292833857859111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95023606373723778477145481 71267704780292833857859111)
          ·
            refine ⟨106901557170439250786788667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71267704780292833857859111 106901557170439250786788667)
            ·
              refine ⟨160352335755658876180183001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106901557170439250786788667 160352335755658876180183001)
              ·
                refine ⟨120264251816744157135137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160352335755658876180183001 120264251816744157135137251)
                ·
                  refine ⟨180396377725116235702705877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120264251816744157135137251 180396377725116235702705877)
                  ·
                    refine ⟨4228040102932411774282169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180396377725116235702705877 4228040102932411774282169)
                    ·
                      refine ⟨3171030077199308830711627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228040102932411774282169 3171030077199308830711627)
                      ·
                        rfl

theorem cell23_6175559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_6175559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175559 prefixEnd_6175559 := by exact prefixLift 6175559
  have htrace : WordTrace (prefixWord ++ tailWord_6175559) baseStart_6175559 baseEnd_6175559 := by
    simpa [prefixWord, tailWord_6175559, baseEnd_6175559] using wordTrace_append hprefix tailTrace_6175559
  have hstable : (prefixWord ++ tailWord_6175559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175559).length < 2 ^ (prefixWord ++ tailWord_6175559).sum := by decide
  have hdescent : baseEnd_6175559 < baseStart_6175559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175599 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 3, 4]
def baseStart_6175599 : Nat := 118140960795 + 6175599 * 2 ^ 59
def prefixEnd_6175599 : Nat := 4983230072969 + 3 ^ 40 * 6175599 * 2
def baseEnd_6175599 : Nat := 1057016872141829558070481

theorem tailTrace_6175599 : CollatzResearch.WordTrace tailWord_6175599 prefixEnd_6175599 1057016872141829558070481 := by
  unfold tailWord_6175599
  simp only [CollatzResearch.WordTrace]
  refine ⟨225242599953867006184689851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150161733302578004123126567 225242599953867006184689851)
  ·
    refine ⟨337863899930800509277034777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225242599953867006184689851 337863899930800509277034777)
    ·
      refine ⟨253397924948100381957776083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337863899930800509277034777 253397924948100381957776083)
      ·
        refine ⟨380096887422150572936664125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253397924948100381957776083 380096887422150572936664125)
        ·
          refine ⟨142536332783306464851249047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380096887422150572936664125 142536332783306464851249047)
          ·
            refine ⟨213804499174959697276873571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142536332783306464851249047 213804499174959697276873571)
            ·
              refine ⟨320706748762439545915310357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213804499174959697276873571 320706748762439545915310357)
              ·
                refine ⟨15033128848239353714780173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 320706748762439545915310357 15033128848239353714780173)
                ·
                  refine ⟨5637423318089757643042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15033128848239353714780173 5637423318089757643042565)
                  ·
                    refine ⟨1057016872141829558070481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5637423318089757643042565 1057016872141829558070481)
                    ·
                      rfl

theorem cell23_6175599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_6175599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175599 prefixEnd_6175599 := by exact prefixLift 6175599
  have htrace : WordTrace (prefixWord ++ tailWord_6175599) baseStart_6175599 baseEnd_6175599 := by
    simpa [prefixWord, tailWord_6175599, baseEnd_6175599] using wordTrace_append hprefix tailTrace_6175599
  have hstable : (prefixWord ++ tailWord_6175599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175599).length < 2 ^ (prefixWord ++ tailWord_6175599).sum := by decide
  have hdescent : baseEnd_6175599 < baseStart_6175599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175612 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 10]
def baseStart_6175612 : Nat := 118140960795 + 6175612 * 2 ^ 59
def prefixEnd_6175612 : Nat := 4983230072969 + 3 ^ 40 * 6175612 * 2
def baseEnd_6175612 : Nat := 352339699074888569260987

theorem tailTrace_6175612 : CollatzResearch.WordTrace tailWord_6175612 prefixEnd_6175612 352339699074888569260987 := by
  unfold tailWord_6175612
  simp only [CollatzResearch.WordTrace]
  refine ⟨112621537051409954702456545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150162049401879939603275393 112621537051409954702456545)
  ·
    refine ⟨84466152788557466026842409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112621537051409954702456545 84466152788557466026842409)
    ·
      refine ⟨63349614591418099520131807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84466152788557466026842409 63349614591418099520131807)
      ·
        refine ⟨95024421887127149280197711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63349614591418099520131807 95024421887127149280197711)
        ·
          refine ⟨142536632830690723920296567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95024421887127149280197711 142536632830690723920296567)
          ·
            refine ⟨213804949246036085880444851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142536632830690723920296567 213804949246036085880444851)
            ·
              refine ⟨320707423869054128820667277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213804949246036085880444851 320707423869054128820667277)
              ·
                refine ⟨120265283950895298307750229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320707423869054128820667277 120265283950895298307750229)
                ·
                  refine ⟨352339699074888569260987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120265283950895298307750229 352339699074888569260987)
                  ·
                    rfl

theorem cell23_6175612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_6175612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175612 prefixEnd_6175612 := by exact prefixLift 6175612
  have htrace : WordTrace (prefixWord ++ tailWord_6175612) baseStart_6175612 baseEnd_6175612 := by
    simpa [prefixWord, tailWord_6175612, baseEnd_6175612] using wordTrace_append hprefix tailTrace_6175612
  have hstable : (prefixWord ++ tailWord_6175612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175612).length < 2 ^ (prefixWord ++ tailWord_6175612).sum := by decide
  have hdescent : baseEnd_6175612 < baseStart_6175612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175679 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_6175679 : Nat := 118140960795 + 6175679 * 2 ^ 59
def prefixEnd_6175679 : Nat := 4983230072969 + 3 ^ 40 * 6175679 * 2
def baseEnd_6175679 : Nat := 3171091694877848361211075

theorem tailTrace_6175679 : CollatzResearch.WordTrace tailWord_6175679 prefixEnd_6175679 3171091694877848361211075 := by
  unfold tailWord_6175679
  simp only [CollatzResearch.WordTrace]
  refine ⟨225245517793577179847602091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150163678529051453231734727 225245517793577179847602091)
  ·
    refine ⟨337868276690365769771403137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225245517793577179847602091 337868276690365769771403137)
    ·
      refine ⟨253401207517774327328552353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337868276690365769771403137 253401207517774327328552353)
      ·
        refine ⟨190050905638330745496414265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253401207517774327328552353 190050905638330745496414265)
        ·
          refine ⟨142538179228748059122310699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190050905638330745496414265 142538179228748059122310699)
          ·
            refine ⟨213807268843122088683466049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142538179228748059122310699 213807268843122088683466049)
            ·
              refine ⟨160355451632341566512599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213807268843122088683466049 160355451632341566512599537)
              ·
                refine ⟨120266588724256174884449653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160355451632341566512599537 120266588724256174884449653)
                ·
                  refine ⟨11274992692899016395417155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120266588724256174884449653 11274992692899016395417155)
                  ·
                    refine ⟨16912489039348524593125733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11274992692899016395417155 16912489039348524593125733)
                    ·
                      refine ⟨3171091694877848361211075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16912489039348524593125733 3171091694877848361211075)
                      ·
                        rfl

theorem cell23_6175679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_6175679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175679 prefixEnd_6175679 := by exact prefixLift 6175679
  have htrace : WordTrace (prefixWord ++ tailWord_6175679) baseStart_6175679 baseEnd_6175679 := by
    simpa [prefixWord, tailWord_6175679, baseEnd_6175679] using wordTrace_append hprefix tailTrace_6175679
  have hstable : (prefixWord ++ tailWord_6175679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175679).length < 2 ^ (prefixWord ++ tailWord_6175679).sum := by decide
  have hdescent : baseEnd_6175679 < baseStart_6175679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175706 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_6175706 : Nat := 118140960795 + 6175706 * 2 ^ 59
def prefixEnd_6175706 : Nat := 4983230072969 + 3 ^ 40 * 6175706 * 2
def baseEnd_6175706 : Nat := 1057035186285173251857817

theorem tailTrace_6175706 : CollatzResearch.WordTrace tailWord_6175706 prefixEnd_6175706 1057035186285173251857817 := by
  unfold tailWord_6175706
  simp only [CollatzResearch.WordTrace]
  refine ⟨56311625641119840864708743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150164335042986242305889981 56311625641119840864708743)
  ·
    refine ⟨84467438461679761297063115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56311625641119840864708743 84467438461679761297063115)
    ·
      refine ⟨126701157692519641945594673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84467438461679761297063115 126701157692519641945594673)
      ·
        refine ⟨95025868269389731459196005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126701157692519641945594673 95025868269389731459196005)
        ·
          refine ⟨17817350300510574648599251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95025868269389731459196005 17817350300510574648599251)
          ·
            refine ⟨26726025450765861972898877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17817350300510574648599251 26726025450765861972898877)
            ·
              refine ⟨10022259544037198239837079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26726025450765861972898877 10022259544037198239837079)
              ·
                refine ⟨15033389316055797359755619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022259544037198239837079 15033389316055797359755619)
                ·
                  refine ⟨22550083974083696039633429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15033389316055797359755619 22550083974083696039633429)
                  ·
                    refine ⟨1057035186285173251857817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22550083974083696039633429 1057035186285173251857817)
                    ·
                      rfl

theorem cell23_6175706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_6175706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175706 prefixEnd_6175706 := by exact prefixLift 6175706
  have htrace : WordTrace (prefixWord ++ tailWord_6175706) baseStart_6175706 baseEnd_6175706 := by
    simpa [prefixWord, tailWord_6175706, baseEnd_6175706] using wordTrace_append hprefix tailTrace_6175706
  have hstable : (prefixWord ++ tailWord_6175706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175706).length < 2 ^ (prefixWord ++ tailWord_6175706).sum := by decide
  have hdescent : baseEnd_6175706 < baseStart_6175706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175749 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_6175749 : Nat := 118140960795 + 6175749 * 2 ^ 59
def prefixEnd_6175749 : Nat := 4983230072969 + 3 ^ 40 * 6175749 * 2
def baseEnd_6175749 : Nat := 1057042546174554362445251

theorem tailTrace_6175749 : CollatzResearch.WordTrace tailWord_6175749 prefixEnd_6175749 1057042546174554362445251 := by
  unfold tailWord_6175749
  simp only [CollatzResearch.WordTrace]
  refine ⟨225248070903323581802650301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150165380602215721201766867 225248070903323581802650301)
  ·
    refine ⟨84468026588746343175993863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225248070903323581802650301 84468026588746343175993863)
    ·
      refine ⟨126702039883119514763990795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84468026588746343175993863 126702039883119514763990795)
      ·
        refine ⟨190053059824679272145986193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126702039883119514763990795 190053059824679272145986193)
        ·
          refine ⟨142539794868509454109489645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190053059824679272145986193 142539794868509454109489645)
          ·
            refine ⟨53452423075691045291058617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142539794868509454109489645 53452423075691045291058617)
            ·
              refine ⟨40089317306768283968293963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53452423075691045291058617 40089317306768283968293963)
              ·
                refine ⟨60133975960152425952440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40089317306768283968293963 60133975960152425952440945)
                ·
                  refine ⟨45100481970114319464330709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60133975960152425952440945 45100481970114319464330709)
                  ·
                    refine ⟨1057042546174554362445251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45100481970114319464330709 1057042546174554362445251)
                    ·
                      rfl

theorem cell23_6175749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_6175749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175749 prefixEnd_6175749 := by exact prefixLift 6175749
  have htrace : WordTrace (prefixWord ++ tailWord_6175749) baseStart_6175749 baseEnd_6175749 := by
    simpa [prefixWord, tailWord_6175749, baseEnd_6175749] using wordTrace_append hprefix tailTrace_6175749
  have hstable : (prefixWord ++ tailWord_6175749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175749).length < 2 ^ (prefixWord ++ tailWord_6175749).sum := by decide
  have hdescent : baseEnd_6175749 < baseStart_6175749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175799 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_6175799 : Nat := 118140960795 + 6175799 * 2 ^ 59
def prefixEnd_6175799 : Nat := 4983230072969 + 3 ^ 40 * 6175799 * 2
def baseEnd_6175799 : Nat := 3171153312556387891710523

theorem tailTrace_6175799 : CollatzResearch.WordTrace tailWord_6175799 prefixEnd_6175799 3171153312556387891710523 := by
  unfold tailWord_6175799
  simp only [CollatzResearch.WordTrace]
  refine ⟨225249894553142440341970451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150166596368761626894646967 225249894553142440341970451)
  ·
    refine ⟨337874841829713660512955677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225249894553142440341970451 337874841829713660512955677)
    ·
      refine ⟨126703065686142622692358379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337874841829713660512955677 126703065686142622692358379)
      ·
        refine ⟨190054598529213934038537569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126703065686142622692358379 190054598529213934038537569)
        ·
          refine ⟨142540948896910450528903177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190054598529213934038537569 142540948896910450528903177)
          ·
            refine ⟨106905711672682837896677383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142540948896910450528903177 106905711672682837896677383)
            ·
              refine ⟨160358567509024256845016075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106905711672682837896677383 160358567509024256845016075)
              ·
                refine ⟨240537851263536385267524113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160358567509024256845016075 240537851263536385267524113)
                ·
                  refine ⟨180403388447652288950643085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240537851263536385267524113 180403388447652288950643085)
                  ·
                    refine ⟨67651270667869608356491157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180403388447652288950643085 67651270667869608356491157)
                    ·
                      refine ⟨3171153312556387891710523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67651270667869608356491157 3171153312556387891710523)
                      ·
                        rfl

theorem cell23_6175799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_6175799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175799 prefixEnd_6175799 := by exact prefixLift 6175799
  have htrace : WordTrace (prefixWord ++ tailWord_6175799) baseStart_6175799 baseEnd_6175799 := by
    simpa [prefixWord, tailWord_6175799, baseEnd_6175799] using wordTrace_append hprefix tailTrace_6175799
  have hstable : (prefixWord ++ tailWord_6175799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175799).length < 2 ^ (prefixWord ++ tailWord_6175799).sum := by decide
  have hdescent : baseEnd_6175799 < baseStart_6175799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175816 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6175816 : Nat := 118140960795 + 6175816 * 2 ^ 59
def prefixEnd_6175816 : Nat := 4983230072969 + 3 ^ 40 * 6175816 * 2
def baseEnd_6175816 : Nat := 3171162041727514325197945

theorem tailTrace_6175816 : CollatzResearch.WordTrace tailWord_6175816 prefixEnd_6175816 3171162041727514325197945 := by
  unfold tailWord_6175816
  simp only [CollatzResearch.WordTrace]
  refine ⟨112625257297040426122669651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150167009729387234830226201 112625257297040426122669651)
  ·
    refine ⟨168937885945560639184004477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112625257297040426122669651 168937885945560639184004477)
    ·
      refine ⟨63351707229585239694001679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168937885945560639184004477 63351707229585239694001679)
      ·
        refine ⟨95027560844377859541002519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63351707229585239694001679 95027560844377859541002519)
        ·
          refine ⟨142541341266566789311503779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95027560844377859541002519 142541341266566789311503779)
          ·
            refine ⟨213812011899850183967255669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142541341266566789311503779 213812011899850183967255669)
            ·
              refine ⟨20044876115610954746930219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213812011899850183967255669 20044876115610954746930219)
              ·
                refine ⟨30067314173416432120395329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20044876115610954746930219 30067314173416432120395329)
                ·
                  refine ⟨22550485630062324090296497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30067314173416432120395329 22550485630062324090296497)
                  ·
                    refine ⟨16912864222546743067722373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22550485630062324090296497 16912864222546743067722373)
                    ·
                      refine ⟨3171162041727514325197945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16912864222546743067722373 3171162041727514325197945)
                      ·
                        rfl

theorem cell23_6175816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6175816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175816 prefixEnd_6175816 := by exact prefixLift 6175816
  have htrace : WordTrace (prefixWord ++ tailWord_6175816) baseStart_6175816 baseEnd_6175816 := by
    simpa [prefixWord, tailWord_6175816, baseEnd_6175816] using wordTrace_append hprefix tailTrace_6175816
  have hstable : (prefixWord ++ tailWord_6175816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175816).length < 2 ^ (prefixWord ++ tailWord_6175816).sum := by decide
  have hdescent : baseEnd_6175816 < baseStart_6175816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175826 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_6175826 : Nat := 118140960795 + 6175826 * 2 ^ 59
def prefixEnd_6175826 : Nat := 4983230072969 + 3 ^ 40 * 6175826 * 2
def baseEnd_6175826 : Nat := 352351908503784365119211

theorem tailTrace_6175826 : CollatzResearch.WordTrace tailWord_6175826 prefixEnd_6175826 352351908503784365119211 := by
  unfold tailWord_6175826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56312719831011155988300833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150167252882696415968802221 56312719831011155988300833)
  ·
    refine ⟨42234539873258366991225625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56312719831011155988300833 42234539873258366991225625)
    ·
      refine ⟨31675904904943775243419219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42234539873258366991225625 31675904904943775243419219)
      ·
        refine ⟨47513857357415662865128829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31675904904943775243419219 47513857357415662865128829)
        ·
          refine ⟨17817696509030873574423311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47513857357415662865128829 17817696509030873574423311)
          ·
            refine ⟨26726544763546310361634967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17817696509030873574423311 26726544763546310361634967)
            ·
              refine ⟨40089817145319465542452451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26726544763546310361634967 40089817145319465542452451)
              ·
                refine ⟨60134725717979198313678677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40089817145319465542452451 60134725717979198313678677)
                ·
                  refine ⟨352351908503784365119211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60134725717979198313678677 352351908503784365119211)
                  ·
                    rfl

theorem cell23_6175826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_6175826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175826 prefixEnd_6175826 := by exact prefixLift 6175826
  have htrace : WordTrace (prefixWord ++ tailWord_6175826) baseStart_6175826 baseEnd_6175826 := by
    simpa [prefixWord, tailWord_6175826, baseEnd_6175826] using wordTrace_append hprefix tailTrace_6175826
  have hstable : (prefixWord ++ tailWord_6175826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175826).length < 2 ^ (prefixWord ++ tailWord_6175826).sum := by decide
  have hdescent : baseEnd_6175826 < baseStart_6175826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175853 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6175853 : Nat := 118140960795 + 6175853 * 2 ^ 59
def prefixEnd_6175853 : Nat := 4983230072969 + 3 ^ 40 * 6175853 * 2
def baseEnd_6175853 : Nat := 3171181040511730680435275

theorem tailTrace_6175853 : CollatzResearch.WordTrace tailWord_6175853 prefixEnd_6175853 3171181040511730680435275 := by
  unfold tailWord_6175853
  simp only [CollatzResearch.WordTrace]
  refine ⟨225251864094946807564436213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150167909396631205042957475 225251864094946807564436213)
  ·
    refine ⟨21117362258901263209165895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225251864094946807564436213 21117362258901263209165895)
    ·
      refine ⟨31676043388351894813748843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21117362258901263209165895 31676043388351894813748843)
      ·
        refine ⟨47514065082527842220623265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31676043388351894813748843 47514065082527842220623265)
        ·
          refine ⟨35635548811895881665467449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47514065082527842220623265 35635548811895881665467449)
          ·
            refine ⟨26726661608921911249100587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35635548811895881665467449 26726661608921911249100587)
            ·
              refine ⟨40089992413382866873650881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26726661608921911249100587 40089992413382866873650881)
              ·
                refine ⟨30067494310037150155238161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40089992413382866873650881 30067494310037150155238161)
                ·
                  refine ⟨22550620732527862616428621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30067494310037150155238161 22550620732527862616428621)
                  ·
                    refine ⟨8456482774697948481160733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22550620732527862616428621 8456482774697948481160733)
                    ·
                      refine ⟨3171181040511730680435275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8456482774697948481160733 3171181040511730680435275)
                      ·
                        rfl

theorem cell23_6175853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6175853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175853 prefixEnd_6175853 := by exact prefixLift 6175853
  have htrace : WordTrace (prefixWord ++ tailWord_6175853) baseStart_6175853 baseEnd_6175853 := by
    simpa [prefixWord, tailWord_6175853, baseEnd_6175853] using wordTrace_append hprefix tailTrace_6175853
  have hstable : (prefixWord ++ tailWord_6175853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175853).length < 2 ^ (prefixWord ++ tailWord_6175853).sum := by decide
  have hdescent : baseEnd_6175853 < baseStart_6175853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175854 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_6175854 : Nat := 118140960795 + 6175854 * 2 ^ 59
def prefixEnd_6175854 : Nat := 4983230072969 + 3 ^ 40 * 6175854 * 2
def baseEnd_6175854 : Nat := 3171181553992385176522771

theorem tailTrace_6175854 : CollatzResearch.WordTrace tailWord_6175854 prefixEnd_6175854 3171181553992385176522771 := by
  unfold tailWord_6175854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28156487570992898091902827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150167933711962123156815077 28156487570992898091902827)
  ·
    refine ⟨42234731356489347137854241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28156487570992898091902827 42234731356489347137854241)
    ·
      refine ⟨31676048517367010353390681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42234731356489347137854241 31676048517367010353390681)
      ·
        refine ⟨23757036388025257765043011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31676048517367010353390681 23757036388025257765043011)
        ·
          refine ⟨35635554582037886647564517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23757036388025257765043011 35635554582037886647564517)
          ·
            refine ⟨6681666484132103746418347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35635554582037886647564517 6681666484132103746418347)
            ·
              refine ⟨10022499726198155619627521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681666484132103746418347 10022499726198155619627521)
              ·
                refine ⟨7516874794648616714720641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10022499726198155619627521 7516874794648616714720641)
                ·
                  refine ⟨5637656095986462536040481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7516874794648616714720641 5637656095986462536040481)
                  ·
                    refine ⟨4228242071989846902030361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637656095986462536040481 4228242071989846902030361)
                    ·
                      refine ⟨3171181553992385176522771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228242071989846902030361 3171181553992385176522771)
                      ·
                        rfl

theorem cell23_6175854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_6175854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175854 prefixEnd_6175854 := by exact prefixLift 6175854
  have htrace : WordTrace (prefixWord ++ tailWord_6175854) baseStart_6175854 baseEnd_6175854 := by
    simpa [prefixWord, tailWord_6175854, baseEnd_6175854] using wordTrace_append hprefix tailTrace_6175854
  have hstable : (prefixWord ++ tailWord_6175854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175854).length < 2 ^ (prefixWord ++ tailWord_6175854).sum := by decide
  have hdescent : baseEnd_6175854 < baseStart_6175854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175856 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_6175856 : Nat := 118140960795 + 6175856 * 2 ^ 59
def prefixEnd_6175856 : Nat := 4983230072969 + 3 ^ 40 * 6175856 * 2
def baseEnd_6175856 : Nat := 1057060860317898056232587

theorem tailTrace_6175856 : CollatzResearch.WordTrace tailWord_6175856 prefixEnd_6175856 1057060860317898056232587 := by
  unfold tailWord_6175856
  simp only [CollatzResearch.WordTrace]
  refine ⟨112625986756967969538397711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150167982342623959384530281 112625986756967969538397711)
  ·
    refine ⟨168938980135451954307596567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112625986756967969538397711 168938980135451954307596567)
    ·
      refine ⟨253408470203177931461394851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168938980135451954307596567 253408470203177931461394851)
      ·
        refine ⟨380112705304766897192092277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253408470203177931461394851 380112705304766897192092277)
        ·
          refine ⟨35635566122321896611758651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 380112705304766897192092277 35635566122321896611758651)
          ·
            refine ⟨53453349183482844917637977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35635566122321896611758651 53453349183482844917637977)
            ·
              refine ⟨40090011887612133688228483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53453349183482844917637977 40090011887612133688228483)
              ·
                refine ⟨60135017831418200532342725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40090011887612133688228483 60135017831418200532342725)
                ·
                  refine ⟨11275315843390912599814261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60135017831418200532342725 11275315843390912599814261)
                  ·
                    refine ⟨1057060860317898056232587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11275315843390912599814261 1057060860317898056232587)
                    ·
                      rfl

theorem cell23_6175856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_6175856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175856 prefixEnd_6175856 := by exact prefixLift 6175856
  have htrace : WordTrace (prefixWord ++ tailWord_6175856) baseStart_6175856 baseEnd_6175856 := by
    simpa [prefixWord, tailWord_6175856, baseEnd_6175856] using wordTrace_append hprefix tailTrace_6175856
  have hstable : (prefixWord ++ tailWord_6175856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175856).length < 2 ^ (prefixWord ++ tailWord_6175856).sum := by decide
  have hdescent : baseEnd_6175856 < baseStart_6175856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_6175893 : Nat := 118140960795 + 6175893 * 2 ^ 59
def prefixEnd_6175893 : Nat := 4983230072969 + 3 ^ 40 * 6175893 * 2
def baseEnd_6175893 : Nat := 3171201579737910523935091

theorem tailTrace_6175893 : CollatzResearch.WordTrace tailWord_6175893 prefixEnd_6175893 3171201579737910523935091 := by
  unfold tailWord_6175893
  simp only [CollatzResearch.WordTrace]
  refine ⟨225253323014801894395892333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150168882009867929597261555 225253323014801894395892333)
  ·
    refine ⟨84469996130550710398459625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225253323014801894395892333 84469996130550710398459625)
    ·
      refine ⟨63352497097913032798844719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84469996130550710398459625 63352497097913032798844719)
      ·
        refine ⟨95028745646869549198267079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63352497097913032798844719 95028745646869549198267079)
        ·
          refine ⟨142543118470304323797400619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95028745646869549198267079 142543118470304323797400619)
          ·
            refine ⟨213814677705456485696100929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142543118470304323797400619 213814677705456485696100929)
            ·
              refine ⟨160361008279092364272075697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213814677705456485696100929 160361008279092364272075697)
              ·
                refine ⟨120270756209319273204056773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160361008279092364272075697 120270756209319273204056773)
                ·
                  refine ⟨22550766789247363725760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120270756209319273204056773 22550766789247363725760645)
                  ·
                    refine ⟨4228268772983880698580121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22550766789247363725760645 4228268772983880698580121)
                    ·
                      refine ⟨3171201579737910523935091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228268772983880698580121 3171201579737910523935091)
                      ·
                        rfl

theorem cell23_6175893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_6175893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175893 prefixEnd_6175893 := by exact prefixLift 6175893
  have htrace : WordTrace (prefixWord ++ tailWord_6175893) baseStart_6175893 baseEnd_6175893 := by
    simpa [prefixWord, tailWord_6175893, baseEnd_6175893] using wordTrace_append hprefix tailTrace_6175893
  have hstable : (prefixWord ++ tailWord_6175893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175893).length < 2 ^ (prefixWord ++ tailWord_6175893).sum := by decide
  have hdescent : baseEnd_6175893 < baseStart_6175893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6175993 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_6175993 : Nat := 118140960795 + 6175993 * 2 ^ 59
def prefixEnd_6175993 : Nat := 4983230072969 + 3 ^ 40 * 6175993 * 2
def baseEnd_6175993 : Nat := 1057084309267786710894877

theorem tailTrace_6175993 : CollatzResearch.WordTrace tailWord_6175993 prefixEnd_6175993 1057084309267786710894877 := by
  unfold tailWord_6175993
  simp only [CollatzResearch.WordTrace]
  refine ⟨225256970314439611474532633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150171313542959740983021755 225256970314439611474532633)
  ·
    refine ⟨168942727735829708605899475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225256970314439611474532633 168942727735829708605899475)
    ·
      refine ⟨253414091603744562908849213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168942727735829708605899475 253414091603744562908849213)
      ·
        refine ⟨95030284351404211090818455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253414091603744562908849213 95030284351404211090818455)
        ·
          refine ⟨142545426527106316636227683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95030284351404211090818455 142545426527106316636227683)
          ·
            refine ⟨213818139790659474954341525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142545426527106316636227683 213818139790659474954341525)
            ·
              refine ⟨10022725302687162888484759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213818139790659474954341525 10022725302687162888484759)
              ·
                refine ⟨15034087954030744332727139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022725302687162888484759 15034087954030744332727139)
                ·
                  refine ⟨22551131931046116499090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15034087954030744332727139 22551131931046116499090709)
                  ·
                    refine ⟨1057084309267786710894877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22551131931046116499090709 1057084309267786710894877)
                    ·
                      rfl

theorem cell23_6175993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_6175993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6175993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6175993 prefixEnd_6175993 := by exact prefixLift 6175993
  have htrace : WordTrace (prefixWord ++ tailWord_6175993) baseStart_6175993 baseEnd_6175993 := by
    simpa [prefixWord, tailWord_6175993, baseEnd_6175993] using wordTrace_append hprefix tailTrace_6175993
  have hstable : (prefixWord ++ tailWord_6175993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6175993).length < 2 ^ (prefixWord ++ tailWord_6175993).sum := by decide
  have hdescent : baseEnd_6175993 < baseStart_6175993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6175993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176004 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_6176004 : Nat := 118140960795 + 6176004 * 2 ^ 59
def prefixEnd_6176004 : Nat := 4983230072969 + 3 ^ 40 * 6176004 * 2
def baseEnd_6176004 : Nat := 3171258576090559589647081

theorem tailTrace_6176004 : CollatzResearch.WordTrace tailWord_6176004 prefixEnd_6176004 3171258576090559589647081 := by
  unfold tailWord_6176004
  simp only [CollatzResearch.WordTrace]
  refine ⟨112628685758699880176591533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150171581011599840235455377 112628685758699880176591533)
  ·
    refine ⟨42235757159512455066221825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112628685758699880176591533 42235757159512455066221825)
    ·
      refine ⟨31676817869634341299666369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42235757159512455066221825 31676817869634341299666369)
      ·
        refine ⟨23757613402225755974749777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31676817869634341299666369 23757613402225755974749777)
        ·
          refine ⟨17818210051669316981062333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23757613402225755974749777 17818210051669316981062333)
          ·
            refine ⟨6681828769375993867898375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17818210051669316981062333 6681828769375993867898375)
            ·
              refine ⟨10022743154063990801847563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681828769375993867898375 10022743154063990801847563)
              ·
                refine ⟨15034114731095986202771345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022743154063990801847563 15034114731095986202771345)
                ·
                  refine ⟨11275586048321989652078509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15034114731095986202771345 11275586048321989652078509)
                  ·
                    refine ⟨4228344768120746119529441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11275586048321989652078509 4228344768120746119529441)
                    ·
                      refine ⟨3171258576090559589647081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228344768120746119529441 3171258576090559589647081)
                      ·
                        rfl

theorem cell23_6176004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_6176004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176004 prefixEnd_6176004 := by exact prefixLift 6176004
  have htrace : WordTrace (prefixWord ++ tailWord_6176004) baseStart_6176004 baseEnd_6176004 := by
    simpa [prefixWord, tailWord_6176004, baseEnd_6176004] using wordTrace_append hprefix tailTrace_6176004
  have hstable : (prefixWord ++ tailWord_6176004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176004).length < 2 ^ (prefixWord ++ tailWord_6176004).sum := by decide
  have hdescent : baseEnd_6176004 < baseStart_6176004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_6176016 : Nat := 118140960795 + 6176016 * 2 ^ 59
def prefixEnd_6176016 : Nat := 4983230072969 + 3 ^ 40 * 6176016 * 2
def baseEnd_6176016 : Nat := 3171264737858413542697025

theorem tailTrace_6176016 : CollatzResearch.WordTrace tailWord_6176016 prefixEnd_6176016 3171264737858413542697025 := by
  unfold tailWord_6176016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112628904596678143201309951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150171872795570857601746601 112628904596678143201309951)
  ·
    refine ⟨168943356895017214801964927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112628904596678143201309951 168943356895017214801964927)
    ·
      refine ⟨253415035342525822202947391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168943356895017214801964927 253415035342525822202947391)
      ·
        refine ⟨380122553013788733304421087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253415035342525822202947391 380122553013788733304421087)
        ·
          refine ⟨570183829520683099956631631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380122553013788733304421087 570183829520683099956631631)
          ·
            refine ⟨855275744281024649934947447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570183829520683099956631631 855275744281024649934947447)
            ·
              refine ⟨1282913616421536974902421171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855275744281024649934947447 1282913616421536974902421171)
              ·
                refine ⟨1924370424632305462353631757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282913616421536974902421171 1924370424632305462353631757)
                ·
                  refine ⟨721638909237114548382611909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1924370424632305462353631757 721638909237114548382611909)
                  ·
                    refine ⟨135307295481958977821739733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721638909237114548382611909 135307295481958977821739733)
                    ·
                      refine ⟨3171264737858413542697025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135307295481958977821739733 3171264737858413542697025)
                      ·
                        rfl

theorem cell23_6176016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_6176016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176016 prefixEnd_6176016 := by exact prefixLift 6176016
  have htrace : WordTrace (prefixWord ++ tailWord_6176016) baseStart_6176016 baseEnd_6176016 := by
    simpa [prefixWord, tailWord_6176016, baseEnd_6176016] using wordTrace_append hprefix tailTrace_6176016
  have hstable : (prefixWord ++ tailWord_6176016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176016).length < 2 ^ (prefixWord ++ tailWord_6176016).sum := by decide
  have hdescent : baseEnd_6176016 < baseStart_6176016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176057 : List Nat := [1, 2, 1, 6, 2, 2, 2, 7]
def baseStart_6176057 : Nat := 118140960795 + 6176057 * 2 ^ 59
def prefixEnd_6176057 : Nat := 4983230072969 + 3 ^ 40 * 6176057 * 2
def baseEnd_6176057 : Nat := 117455029280194366010531

theorem tailTrace_6176057 : CollatzResearch.WordTrace tailWord_6176057 prefixEnd_6176057 117455029280194366010531 := by
  unfold tailWord_6176057
  simp only [CollatzResearch.WordTrace]
  refine ⟨225259304586207750404862425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150172869724138500269908283 225259304586207750404862425)
  ·
    refine ⟨168944478439655812803646819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225259304586207750404862425 168944478439655812803646819)
    ·
      refine ⟨253416717659483719205470229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168944478439655812803646819 253416717659483719205470229)
      ·
        refine ⟨11878908640288299337756417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253416717659483719205470229 11878908640288299337756417)
        ·
          refine ⟨8909181480216224503317313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11878908640288299337756417 8909181480216224503317313)
          ·
            refine ⟨6681886110162168377487985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909181480216224503317313 6681886110162168377487985)
            ·
              refine ⟨5011414582621626283115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6681886110162168377487985 5011414582621626283115989)
              ·
                refine ⟨117455029280194366010531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5011414582621626283115989 117455029280194366010531)
                ·
                  rfl

theorem cell23_6176057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 7].length) (baseStart_6176057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176057 prefixEnd_6176057 := by exact prefixLift 6176057
  have htrace : WordTrace (prefixWord ++ tailWord_6176057) baseStart_6176057 baseEnd_6176057 := by
    simpa [prefixWord, tailWord_6176057, baseEnd_6176057] using wordTrace_append hprefix tailTrace_6176057
  have hstable : (prefixWord ++ tailWord_6176057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176057).length < 2 ^ (prefixWord ++ tailWord_6176057).sum := by decide
  have hdescent : baseEnd_6176057 < baseStart_6176057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176063 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_6176063 : Nat := 118140960795 + 6176063 * 2 ^ 59
def prefixEnd_6176063 : Nat := 4983230072969 + 3 ^ 40 * 6176063 * 2
def baseEnd_6176063 : Nat := 3171288871449174858809309

theorem tailTrace_6176063 : CollatzResearch.WordTrace tailWord_6176063 prefixEnd_6176063 3171288871449174858809309 := by
  unfold tailWord_6176063
  simp only [CollatzResearch.WordTrace]
  refine ⟨225259523424186013429580843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150173015616124008953053895 225259523424186013429580843)
  ·
    refine ⟨337889285136279020144371265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225259523424186013429580843 337889285136279020144371265)
    ·
      refine ⟨253416963852209265108278449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337889285136279020144371265 253416963852209265108278449)
      ·
        refine ⟨190062722889156948831208837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253416963852209265108278449 190062722889156948831208837)
        ·
          refine ⟨35636760541716927905851657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190062722889156948831208837 35636760541716927905851657)
          ·
            refine ⟨26727570406287695929388743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35636760541716927905851657 26727570406287695929388743)
            ·
              refine ⟨40091355609431543894083115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26727570406287695929388743 40091355609431543894083115)
              ·
                refine ⟨60137033414147315841124673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40091355609431543894083115 60137033414147315841124673)
                ·
                  refine ⟨45102775060610486880843505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60137033414147315841124673 45102775060610486880843505)
                  ·
                    refine ⟨33827081295457865160632629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45102775060610486880843505 33827081295457865160632629)
                    ·
                      refine ⟨3171288871449174858809309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33827081295457865160632629 3171288871449174858809309)
                      ·
                        rfl

theorem cell23_6176063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_6176063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176063 prefixEnd_6176063 := by exact prefixLift 6176063
  have htrace : WordTrace (prefixWord ++ tailWord_6176063) baseStart_6176063 baseEnd_6176063 := by
    simpa [prefixWord, tailWord_6176063, baseEnd_6176063] using wordTrace_append hprefix tailTrace_6176063
  have hstable : (prefixWord ++ tailWord_6176063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176063).length < 2 ^ (prefixWord ++ tailWord_6176063).sum := by decide
  have hdescent : baseEnd_6176063 < baseStart_6176063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176068 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6176068 : Nat := 118140960795 + 6176068 * 2 ^ 59
def prefixEnd_6176068 : Nat := 4983230072969 + 3 ^ 40 * 6176068 * 2
def baseEnd_6176068 : Nat := 3171291438852447339246787

theorem tailTrace_6176068 : CollatzResearch.WordTrace tailWord_6176068 prefixEnd_6176068 3171291438852447339246787 := by
  unfold tailWord_6176068
  simp only [CollatzResearch.WordTrace]
  refine ⟨112629852894583949641756429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150173137192778599522341905 112629852894583949641756429)
  ·
    refine ⟨42236194835468981115658661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112629852894583949641756429 42236194835468981115658661)
    ·
      refine ⟨7919286531650433959185999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42236194835468981115658661 7919286531650433959185999)
      ·
        refine ⟨11878929797475650938778999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919286531650433959185999 11878929797475650938778999)
        ·
          refine ⟨17818394696213476408168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11878929797475650938778999 17818394696213476408168499)
          ·
            refine ⟨26727592044320214612252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17818394696213476408168499 26727592044320214612252749)
            ·
              refine ⟨10022847016620080479594781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26727592044320214612252749 10022847016620080479594781)
              ·
                refine ⟨3758567631232530179848043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10022847016620080479594781 3758567631232530179848043)
                ·
                  refine ⟨5637851446848795269772065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758567631232530179848043 5637851446848795269772065)
                  ·
                    refine ⟨4228388585136596452329049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5637851446848795269772065 4228388585136596452329049)
                    ·
                      refine ⟨3171291438852447339246787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228388585136596452329049 3171291438852447339246787)
                      ·
                        rfl

theorem cell23_6176068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6176068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176068 prefixEnd_6176068 := by exact prefixLift 6176068
  have htrace : WordTrace (prefixWord ++ tailWord_6176068) baseStart_6176068 baseEnd_6176068 := by
    simpa [prefixWord, tailWord_6176068, baseEnd_6176068] using wordTrace_append hprefix tailTrace_6176068
  have hstable : (prefixWord ++ tailWord_6176068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176068).length < 2 ^ (prefixWord ++ tailWord_6176068).sum := by decide
  have hdescent : baseEnd_6176068 < baseStart_6176068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176113 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 7]
def baseStart_6176113 : Nat := 118140960795 + 6176113 * 2 ^ 59
def prefixEnd_6176113 : Nat := 4983230072969 + 3 ^ 40 * 6176113 * 2
def baseEnd_6176113 : Nat := 352368282831322184798231

theorem tailTrace_6176113 : CollatzResearch.WordTrace tailWord_6176113 prefixEnd_6176113 352368282831322184798231 := by
  unfold tailWord_6176113
  simp only [CollatzResearch.WordTrace]
  refine ⟨225261347074004871968900993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150174231382669914645933995 225261347074004871968900993)
  ·
    refine ⟨168946010305503653976675745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225261347074004871968900993 168946010305503653976675745)
    ·
      refine ⟨126709507729127740482506809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168946010305503653976675745 126709507729127740482506809)
      ·
        refine ⟨95032130796845805361880107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126709507729127740482506809 95032130796845805361880107)
        ·
          refine ⟨142548196195268708042820161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95032130796845805361880107 142548196195268708042820161)
          ·
            refine ⟨106911147146451531032115121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142548196195268708042820161 106911147146451531032115121)
            ·
              refine ⟨80183360359838648274086341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106911147146451531032115121 80183360359838648274086341)
              ·
                refine ⟨15034380067469746551391189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80183360359838648274086341 15034380067469746551391189)
                ·
                  refine ⟨352368282831322184798231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15034380067469746551391189 352368282831322184798231)
                  ·
                    rfl

theorem cell23_6176113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_6176113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176113 prefixEnd_6176113 := by exact prefixLift 6176113
  have htrace : WordTrace (prefixWord ++ tailWord_6176113) baseStart_6176113 baseEnd_6176113 := by
    simpa [prefixWord, tailWord_6176113, baseEnd_6176113] using wordTrace_append hprefix tailTrace_6176113
  have hstable : (prefixWord ++ tailWord_6176113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176113).length < 2 ^ (prefixWord ++ tailWord_6176113).sum := by decide
  have hdescent : baseEnd_6176113 < baseStart_6176113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176140 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_6176140 : Nat := 118140960795 + 6176140 * 2 ^ 59
def prefixEnd_6176140 : Nat := 4983230072969 + 3 ^ 40 * 6176140 * 2
def baseEnd_6176140 : Nat := 3171328409459571057546455

theorem tailTrace_6176140 : CollatzResearch.WordTrace tailWord_6176140 prefixEnd_6176140 3171328409459571057546455 := by
  unfold tailWord_6176140
  simp only [CollatzResearch.WordTrace]
  refine ⟨112631165922453527790066937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150174887896604703720089249 112631165922453527790066937)
  ·
    refine ⟨84473374441840145842550203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112631165922453527790066937 84473374441840145842550203)
    ·
      refine ⟨126710061662760218763825305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84473374441840145842550203 126710061662760218763825305)
      ·
        refine ⟨95032546247070164072868979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126710061662760218763825305 95032546247070164072868979)
        ·
          refine ⟨142548819370605246109303469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95032546247070164072868979 142548819370605246109303469)
          ·
            refine ⟨53455807263976967290988801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142548819370605246109303469 53455807263976967290988801)
            ·
              refine ⟨40091855447982725468241601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53455807263976967290988801 40091855447982725468241601)
              ·
                refine ⟨30068891585987044101181201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40091855447982725468241601 30068891585987044101181201)
                ·
                  refine ⟨22551668689490283075885901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30068891585987044101181201 22551668689490283075885901)
                  ·
                    refine ⟨8456875758558856153457213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22551668689490283075885901 8456875758558856153457213)
                    ·
                      refine ⟨3171328409459571057546455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8456875758558856153457213 3171328409459571057546455)
                      ·
                        rfl

theorem cell23_6176140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_6176140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176140 prefixEnd_6176140 := by exact prefixLift 6176140
  have htrace : WordTrace (prefixWord ++ tailWord_6176140) baseStart_6176140 baseEnd_6176140 := by
    simpa [prefixWord, tailWord_6176140, baseEnd_6176140] using wordTrace_append hprefix tailTrace_6176140
  have hstable : (prefixWord ++ tailWord_6176140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176140).length < 2 ^ (prefixWord ++ tailWord_6176140).sum := by decide
  have hdescent : baseEnd_6176140 < baseStart_6176140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176157 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_6176157 : Nat := 118140960795 + 6176157 * 2 ^ 59
def prefixEnd_6176157 : Nat := 4983230072969 + 3 ^ 40 * 6176157 * 2
def baseEnd_6176157 : Nat := 3171337138630697491033877

theorem tailTrace_6176157 : CollatzResearch.WordTrace tailWord_6176157 prefixEnd_6176157 3171337138630697491033877 := by
  unfold tailWord_6176157
  simp only [CollatzResearch.WordTrace]
  refine ⟨225262951885845467483502725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150175301257230311655668483 225262951885845467483502725)
  ·
    refine ⟨42236803478596025153156761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225262951885845467483502725 42236803478596025153156761)
    ·
      refine ⟨31677602608947018864867571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42236803478596025153156761 31677602608947018864867571)
      ·
        refine ⟨47516403913420528297301357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31677602608947018864867571 47516403913420528297301357)
        ·
          refine ⟨17818651467532698111488009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47516403913420528297301357 17818651467532698111488009)
          ·
            refine ⟨13363988600649523583616007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17818651467532698111488009 13363988600649523583616007)
            ·
              refine ⟨20045982900974285375424011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13363988600649523583616007 20045982900974285375424011)
              ·
                refine ⟨30068974351461428063136017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20045982900974285375424011 30068974351461428063136017)
                ·
                  refine ⟨22551730763596071047352013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30068974351461428063136017 22551730763596071047352013)
                  ·
                    refine ⟨8456899036348526642757005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22551730763596071047352013 8456899036348526642757005)
                    ·
                      refine ⟨3171337138630697491033877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8456899036348526642757005 3171337138630697491033877)
                      ·
                        rfl

theorem cell23_6176157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_6176157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176157 prefixEnd_6176157 := by exact prefixLift 6176157
  have htrace : WordTrace (prefixWord ++ tailWord_6176157) baseStart_6176157 baseEnd_6176157 := by
    simpa [prefixWord, tailWord_6176157, baseEnd_6176157] using wordTrace_append hprefix tailTrace_6176157
  have hstable : (prefixWord ++ tailWord_6176157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176157).length < 2 ^ (prefixWord ++ tailWord_6176157).sum := by decide
  have hdescent : baseEnd_6176157 < baseStart_6176157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176167 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_6176167 : Nat := 118140960795 + 6176167 * 2 ^ 59
def prefixEnd_6176167 : Nat := 4983230072969 + 3 ^ 40 * 6176167 * 2
def baseEnd_6176167 : Nat := 3171342273437242451908831

theorem tailTrace_6176167 : CollatzResearch.WordTrace tailWord_6176167 prefixEnd_6176167 3171342273437242451908831 := by
  unfold tailWord_6176167
  simp only [CollatzResearch.WordTrace]
  refine ⟨225263316615809239191366755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150175544410539492794244503 225263316615809239191366755)
  ·
    refine ⟨337894974923713858787050133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225263316615809239191366755 337894974923713858787050133)
    ·
      refine ⟨15838826949549087130642975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 337894974923713858787050133 15838826949549087130642975)
      ·
        refine ⟨23758240424323630695964463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15838826949549087130642975 23758240424323630695964463)
        ·
          refine ⟨35637360636485446043946695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23758240424323630695964463 35637360636485446043946695)
          ·
            refine ⟨53456040954728169065920043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35637360636485446043946695 53456040954728169065920043)
            ·
              refine ⟨80184061432092253598880065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53456040954728169065920043 80184061432092253598880065)
              ·
                refine ⟨60138046074069190199160049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80184061432092253598880065 60138046074069190199160049)
                ·
                  refine ⟨45103534555551892649370037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60138046074069190199160049 45103534555551892649370037)
                  ·
                    refine ⟨4228456364582989935878441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45103534555551892649370037 4228456364582989935878441)
                    ·
                      refine ⟨3171342273437242451908831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228456364582989935878441 3171342273437242451908831)
                      ·
                        rfl

theorem cell23_6176167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_6176167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176167 prefixEnd_6176167 := by exact prefixLift 6176167
  have htrace : WordTrace (prefixWord ++ tailWord_6176167) baseStart_6176167 baseEnd_6176167 := by
    simpa [prefixWord, tailWord_6176167, baseEnd_6176167] using wordTrace_append hprefix tailTrace_6176167
  have hstable : (prefixWord ++ tailWord_6176167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176167).length < 2 ^ (prefixWord ++ tailWord_6176167).sum := by decide
  have hdescent : baseEnd_6176167 < baseStart_6176167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176241 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 1, 4]
def baseStart_6176241 : Nat := 118140960795 + 6176241 * 2 ^ 59
def prefixEnd_6176241 : Nat := 4983230072969 + 3 ^ 40 * 6176241 * 2
def baseEnd_6176241 : Nat := 1057126757001891720794497

theorem tailTrace_6176241 : CollatzResearch.WordTrace tailWord_6176241 prefixEnd_6176241 1057126757001891720794497 := by
  unfold tailWord_6176241
  simp only [CollatzResearch.WordTrace]
  refine ⟨225266015617541149829560577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150177343745027433219707051 225266015617541149829560577)
  ·
    refine ⟨168949511713155862372170433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225266015617541149829560577 168949511713155862372170433)
    ·
      refine ⟨126712133784866896779127825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168949511713155862372170433 126712133784866896779127825)
      ·
        refine ⟨95034100338650172584345869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126712133784866896779127825 95034100338650172584345869)
        ·
          refine ⟨35637787626993814719129701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95034100338650172584345869 35637787626993814719129701)
          ·
            refine ⟨6682085180061340259836819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35637787626993814719129701 6682085180061340259836819)
            ·
              refine ⟨10023127770092010389755229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682085180061340259836819 10023127770092010389755229)
              ·
                refine ⟨3758672913784503896158211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10023127770092010389755229 3758672913784503896158211)
                ·
                  refine ⟨5638009370676755844237317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758672913784503896158211 5638009370676755844237317)
                  ·
                    refine ⟨1057126757001891720794497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638009370676755844237317 1057126757001891720794497)
                    ·
                      rfl

theorem cell23_6176241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_6176241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176241 prefixEnd_6176241 := by exact prefixLift 6176241
  have htrace : WordTrace (prefixWord ++ tailWord_6176241) baseStart_6176241 baseEnd_6176241 := by
    simpa [prefixWord, tailWord_6176241, baseEnd_6176241] using wordTrace_append hprefix tailTrace_6176241
  have hstable : (prefixWord ++ tailWord_6176241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176241).length < 2 ^ (prefixWord ++ tailWord_6176241).sum := by decide
  have hdescent : baseEnd_6176241 < baseStart_6176241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176264 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_6176264 : Nat := 118140960795 + 6176264 * 2 ^ 59
def prefixEnd_6176264 : Nat := 4983230072969 + 3 ^ 40 * 6176264 * 2
def baseEnd_6176264 : Nat := 3171392081060728572395885

theorem tailTrace_6176264 : CollatzResearch.WordTrace tailWord_6176264 prefixEnd_6176264 3171392081060728572395885 := by
  unfold tailWord_6176264
  simp only [CollatzResearch.WordTrace]
  refine ⟨112633427248228912378823923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150177902997638549838431897 112633427248228912378823923)
  ·
    refine ⟨168950140872343368568235885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112633427248228912378823923 168950140872343368568235885)
    ·
      refine ⟨63356302827128763213088457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168950140872343368568235885 63356302827128763213088457)
      ·
        refine ⟨47517227120346572409816343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63356302827128763213088457 47517227120346572409816343)
        ·
          refine ⟨71275840680519858614724515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47517227120346572409816343 71275840680519858614724515)
          ·
            refine ⟨106913761020779787922086773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71275840680519858614724515 106913761020779787922086773)
            ·
              refine ⟨10023165095698105117695635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106913761020779787922086773 10023165095698105117695635)
              ·
                refine ⟨15034747643547157676543453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023165095698105117695635 15034747643547157676543453)
                ·
                  refine ⟨5638030366330184128703795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15034747643547157676543453 5638030366330184128703795)
                  ·
                    refine ⟨8457045549495276193055693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5638030366330184128703795 8457045549495276193055693)
                    ·
                      refine ⟨3171392081060728572395885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8457045549495276193055693 3171392081060728572395885)
                      ·
                        rfl

theorem cell23_6176264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_6176264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176264 prefixEnd_6176264 := by exact prefixLift 6176264
  have htrace : WordTrace (prefixWord ++ tailWord_6176264) baseStart_6176264 baseEnd_6176264 := by
    simpa [prefixWord, tailWord_6176264, baseEnd_6176264] using wordTrace_append hprefix tailTrace_6176264
  have hstable : (prefixWord ++ tailWord_6176264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176264).length < 2 ^ (prefixWord ++ tailWord_6176264).sum := by decide
  have hdescent : baseEnd_6176264 < baseStart_6176264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176287 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 6, 2]
def baseStart_6176287 : Nat := 118140960795 + 6176287 * 2 ^ 59
def prefixEnd_6176287 : Nat := 4983230072969 + 3 ^ 40 * 6176287 * 2
def baseEnd_6176287 : Nat := 3171403891115781982408279

theorem tailTrace_6176287 : CollatzResearch.WordTrace tailWord_6176287 prefixEnd_6176287 3171403891115781982408279 := by
  unfold tailWord_6176287
  simp only [CollatzResearch.WordTrace]
  refine ⟨225267693375374499685735115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150178462250249666457156743 225267693375374499685735115)
  ·
    refine ⟨337901540063061749528602673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225267693375374499685735115 337901540063061749528602673)
    ·
      refine ⟨253426155047296312146452005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337901540063061749528602673 253426155047296312146452005)
      ·
        refine ⟨47517404071368058527459751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253426155047296312146452005 47517404071368058527459751)
        ·
          refine ⟨71276106107052087791189627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47517404071368058527459751 71276106107052087791189627)
          ·
            refine ⟨106914159160578131686784441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71276106107052087791189627 106914159160578131686784441)
            ·
              refine ⟨80185619370433598765088331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106914159160578131686784441 80185619370433598765088331)
              ·
                refine ⟨120278429055650398147632497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80185619370433598765088331 120278429055650398147632497)
                ·
                  refine ⟨90208821791737798610724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120278429055650398147632497 90208821791737798610724373)
                  ·
                    refine ⟨4228538521487709309877705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90208821791737798610724373 4228538521487709309877705)
                    ·
                      refine ⟨3171403891115781982408279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228538521487709309877705 3171403891115781982408279)
                      ·
                        rfl

theorem cell23_6176287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_6176287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176287 prefixEnd_6176287 := by exact prefixLift 6176287
  have htrace : WordTrace (prefixWord ++ tailWord_6176287) baseStart_6176287 baseEnd_6176287 := by
    simpa [prefixWord, tailWord_6176287, baseEnd_6176287] using wordTrace_append hprefix tailTrace_6176287
  have hstable : (prefixWord ++ tailWord_6176287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176287).length < 2 ^ (prefixWord ++ tailWord_6176287).sum := by decide
  have hdescent : baseEnd_6176287 < baseStart_6176287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176291 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 2, 3, 2]
def baseStart_6176291 : Nat := 118140960795 + 6176291 * 2 ^ 59
def prefixEnd_6176291 : Nat := 4983230072969 + 3 ^ 40 * 6176291 * 2
def baseEnd_6176291 : Nat := 3171405945038399966758261

theorem tailTrace_6176291 : CollatzResearch.WordTrace tailWord_6176291 prefixEnd_6176291 3171405945038399966758261 := by
  unfold tailWord_6176291
  simp only [CollatzResearch.WordTrace]
  refine ⟨225267839267360008368880727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150178559511573338912587151 225267839267360008368880727)
  ·
    refine ⟨337901758901040012553321091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225267839267360008368880727 337901758901040012553321091)
    ·
      refine ⟨506852638351560018829981637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337901758901040012553321091 506852638351560018829981637)
      ·
        refine ⟨95034869690917503530621557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506852638351560018829981637 95034869690917503530621557)
        ·
          refine ⟨8909519033523515955995771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95034869690917503530621557 8909519033523515955995771)
          ·
            refine ⟨13364278550285273933993657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8909519033523515955995771 13364278550285273933993657)
            ·
              refine ⟨10023208912713955450495243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13364278550285273933993657 10023208912713955450495243)
              ·
                refine ⟨15034813369070933175742865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023208912713955450495243 15034813369070933175742865)
                ·
                  refine ⟨11276110026803199881807149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15034813369070933175742865 11276110026803199881807149)
                  ·
                    refine ⟨4228541260051199955677681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11276110026803199881807149 4228541260051199955677681)
                    ·
                      refine ⟨3171405945038399966758261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228541260051199955677681 3171405945038399966758261)
                      ·
                        rfl

theorem cell23_6176291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_6176291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176291 prefixEnd_6176291 := by exact prefixLift 6176291
  have htrace : WordTrace (prefixWord ++ tailWord_6176291) baseStart_6176291 baseEnd_6176291 := by
    simpa [prefixWord, tailWord_6176291, baseEnd_6176291] using wordTrace_append hprefix tailTrace_6176291
  have hstable : (prefixWord ++ tailWord_6176291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176291).length < 2 ^ (prefixWord ++ tailWord_6176291).sum := by decide
  have hdescent : baseEnd_6176291 < baseStart_6176291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176307 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5]
def baseStart_6176307 : Nat := 118140960795 + 6176307 * 2 ^ 59
def prefixEnd_6176307 : Nat := 4983230072969 + 3 ^ 40 * 6176307 * 2
def baseEnd_6176307 : Nat := 3171414160728871904158187

theorem tailTrace_6176307 : CollatzResearch.WordTrace tailWord_6176307 prefixEnd_6176307 3171414160728871904158187 := by
  unfold tailWord_6176307
  simp only [CollatzResearch.WordTrace]
  refine ⟨225268422835302043101463175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150178948556868028734308783 225268422835302043101463175)
  ·
    refine ⟨337902634252953064652194763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225268422835302043101463175 337902634252953064652194763)
    ·
      refine ⟨506853951379429596978292145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337902634252953064652194763 506853951379429596978292145)
      ·
        refine ⟨380140463534572197733719109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506853951379429596978292145 380140463534572197733719109)
        ·
          refine ⟨71276336912732287075072333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380140463534572197733719109 71276336912732287075072333)
          ·
            refine ⟨26728626342274607653152125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71276336912732287075072333 26728626342274607653152125)
            ·
              refine ⟨10023234878352977869932047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26728626342274607653152125 10023234878352977869932047)
              ·
                refine ⟨15034852317529466804898071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023234878352977869932047 15034852317529466804898071)
                ·
                  refine ⟨22552278476294200207347107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15034852317529466804898071 22552278476294200207347107)
                  ·
                    refine ⟨33828417714441300311020661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22552278476294200207347107 33828417714441300311020661)
                    ·
                      refine ⟨3171414160728871904158187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33828417714441300311020661 3171414160728871904158187)
                      ·
                        rfl

theorem cell23_6176307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_6176307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176307 prefixEnd_6176307 := by exact prefixLift 6176307
  have htrace : WordTrace (prefixWord ++ tailWord_6176307) baseStart_6176307 baseEnd_6176307 := by
    simpa [prefixWord, tailWord_6176307, baseEnd_6176307] using wordTrace_append hprefix tailTrace_6176307
  have hstable : (prefixWord ++ tailWord_6176307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176307).length < 2 ^ (prefixWord ++ tailWord_6176307).sum := by decide
  have hdescent : baseEnd_6176307 < baseStart_6176307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176314 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_6176314 : Nat := 118140960795 + 6176314 * 2 ^ 59
def prefixEnd_6176314 : Nat := 4983230072969 + 3 ^ 40 * 6176314 * 2
def baseEnd_6176314 : Nat := 1057139251697817792256885

theorem tailTrace_6176314 : CollatzResearch.WordTrace tailWord_6176314 prefixEnd_6176314 1057139251697817792256885 := by
  unfold tailWord_6176314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56317169536569170824241999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150179118764184455531311997 56317169536569170824241999)
  ·
    refine ⟨84475754304853756236362999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56317169536569170824241999 84475754304853756236362999)
    ·
      refine ⟨126713631457280634354544499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84475754304853756236362999 126713631457280634354544499)
      ·
        refine ⟨190070447185920951531816749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126713631457280634354544499 190070447185920951531816749)
        ·
          refine ⟨71276417694720356824431281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190070447185920951531816749 71276417694720356824431281)
          ·
            refine ⟨53457313271040267618323461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71276417694720356824431281 53457313271040267618323461)
            ·
              refine ⟨10023246238320050178435649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53457313271040267618323461 10023246238320050178435649)
              ·
                refine ⟨7517434678740037633826737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10023246238320050178435649 7517434678740037633826737)
                ·
                  refine ⟨5638076009055028225370053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7517434678740037633826737 5638076009055028225370053)
                  ·
                    refine ⟨1057139251697817792256885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638076009055028225370053 1057139251697817792256885)
                    ·
                      rfl

theorem cell23_6176314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_6176314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176314 prefixEnd_6176314 := by exact prefixLift 6176314
  have htrace : WordTrace (prefixWord ++ tailWord_6176314) baseStart_6176314 baseEnd_6176314 := by
    simpa [prefixWord, tailWord_6176314, baseEnd_6176314] using wordTrace_append hprefix tailTrace_6176314
  have hstable : (prefixWord ++ tailWord_6176314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176314).length < 2 ^ (prefixWord ++ tailWord_6176314).sum := by decide
  have hdescent : baseEnd_6176314 < baseStart_6176314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176321 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6176321 : Nat := 118140960795 + 6176321 * 2 ^ 59
def prefixEnd_6176321 : Nat := 4983230072969 + 3 ^ 40 * 6176321 * 2
def baseEnd_6176321 : Nat := 3171421349458034849383123

theorem tailTrace_6176321 : CollatzResearch.WordTrace tailWord_6176321 prefixEnd_6176321 3171421349458034849383123 := by
  unfold tailWord_6176321
  simp only [CollatzResearch.WordTrace]
  refine ⟨225268933457251323492472817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150179288971500882328315211 225268933457251323492472817)
  ·
    refine ⟨168951700092938492619354613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225268933457251323492472817 168951700092938492619354613)
    ·
      refine ⟨15839221883712983683064495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168951700092938492619354613 15839221883712983683064495)
      ·
        refine ⟨23758832825569475524596743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15839221883712983683064495 23758832825569475524596743)
        ·
          refine ⟨35638249238354213286895115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23758832825569475524596743 35638249238354213286895115)
          ·
            refine ⟨53457373857531319930342673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35638249238354213286895115 53457373857531319930342673)
            ·
              refine ⟨40093030393148489947757005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53457373857531319930342673 40093030393148489947757005)
              ·
                refine ⟨15034886397430683730408877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40093030393148489947757005 15034886397430683730408877)
                ·
                  refine ⟨5638082399036506398903329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15034886397430683730408877 5638082399036506398903329)
                  ·
                    refine ⟨4228561799277379799177497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638082399036506398903329 4228561799277379799177497)
                    ·
                      refine ⟨3171421349458034849383123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228561799277379799177497 3171421349458034849383123)
                      ·
                        rfl

theorem cell23_6176321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6176321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176321 prefixEnd_6176321 := by exact prefixLift 6176321
  have htrace : WordTrace (prefixWord ++ tailWord_6176321) baseStart_6176321 baseEnd_6176321 := by
    simpa [prefixWord, tailWord_6176321, baseEnd_6176321] using wordTrace_append hprefix tailTrace_6176321
  have hstable : (prefixWord ++ tailWord_6176321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176321).length < 2 ^ (prefixWord ++ tailWord_6176321).sum := by decide
  have hdescent : baseEnd_6176321 < baseStart_6176321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176342 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6176342 : Nat := 118140960795 + 6176342 * 2 ^ 59
def prefixEnd_6176342 : Nat := 4983230072969 + 3 ^ 40 * 6176342 * 2
def baseEnd_6176342 : Nat := 3171432132551779267220527

theorem tailTrace_6176342 : CollatzResearch.WordTrace tailWord_6176342 prefixEnd_6176342 3171432132551779267220527 := by
  unfold tailWord_6176342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079356211885952754936705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150179799593450162719324853 14079356211885952754936705)
  ·
    refine ⟨10559517158914464566202529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14079356211885952754936705 10559517158914464566202529)
    ·
      refine ⟨7919637869185848424651897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10559517158914464566202529 7919637869185848424651897)
      ·
        refine ⟨5939728401889386318488923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7919637869185848424651897 5939728401889386318488923)
        ·
          refine ⟨8909592602834079477733385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939728401889386318488923 8909592602834079477733385)
          ·
            refine ⟨6682194452125559608300039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909592602834079477733385 6682194452125559608300039)
            ·
              refine ⟨10023291678188339412450059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682194452125559608300039 10023291678188339412450059)
              ·
                refine ⟨15034937517282509118675089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023291678188339412450059 15034937517282509118675089)
                ·
                  refine ⟨11276203137961881839006317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15034937517282509118675089 11276203137961881839006317)
                  ·
                    refine ⟨4228576176735705689627369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11276203137961881839006317 4228576176735705689627369)
                    ·
                      refine ⟨3171432132551779267220527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228576176735705689627369 3171432132551779267220527)
                      ·
                        rfl

theorem cell23_6176342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6176342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176342 prefixEnd_6176342 := by exact prefixLift 6176342
  have htrace : WordTrace (prefixWord ++ tailWord_6176342) baseStart_6176342 baseEnd_6176342 := by
    simpa [prefixWord, tailWord_6176342, baseEnd_6176342] using wordTrace_append hprefix tailTrace_6176342
  have hstable : (prefixWord ++ tailWord_6176342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176342).length < 2 ^ (prefixWord ++ tailWord_6176342).sum := by decide
  have hdescent : baseEnd_6176342 < baseStart_6176342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176388 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_6176388 : Nat := 118140960795 + 6176388 * 2 ^ 59
def prefixEnd_6176388 : Nat := 4983230072969 + 3 ^ 40 * 6176388 * 2
def baseEnd_6176388 : Nat := 3171455752661886087245315

theorem tailTrace_6176388 : CollatzResearch.WordTrace tailWord_6176388 prefixEnd_6176388 3171455752661886087245315 := by
  unfold tailWord_6176388
  simp only [CollatzResearch.WordTrace]
  refine ⟨112635688574004296967580909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150180918098672395956774545 112635688574004296967580909)
  ·
    refine ⟨42238383215251611362842841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112635688574004296967580909 42238383215251611362842841)
    ·
      refine ⟨31678787411438708522132131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42238383215251611362842841 31678787411438708522132131)
      ·
        refine ⟨47518181117158062783198197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31678787411438708522132131 47518181117158062783198197)
        ·
          refine ⟨4454829479733568385924831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47518181117158062783198197 4454829479733568385924831)
          ·
            refine ⟨6682244219600352578887247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454829479733568385924831 6682244219600352578887247)
            ·
              refine ⟨10023366329400528868330871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682244219600352578887247 10023366329400528868330871)
              ·
                refine ⟨15035049494100793302496307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023366329400528868330871 15035049494100793302496307)
                ·
                  refine ⟨22552574241151189953744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15035049494100793302496307 22552574241151189953744461)
                  ·
                    refine ⟨8457215340431696232654173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22552574241151189953744461 8457215340431696232654173)
                    ·
                      refine ⟨3171455752661886087245315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8457215340431696232654173 3171455752661886087245315)
                      ·
                        rfl

theorem cell23_6176388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_6176388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176388 prefixEnd_6176388 := by exact prefixLift 6176388
  have htrace : WordTrace (prefixWord ++ tailWord_6176388) baseStart_6176388 baseEnd_6176388 := by
    simpa [prefixWord, tailWord_6176388, baseEnd_6176388] using wordTrace_append hprefix tailTrace_6176388
  have hstable : (prefixWord ++ tailWord_6176388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176388).length < 2 ^ (prefixWord ++ tailWord_6176388).sum := by decide
  have hdescent : baseEnd_6176388 < baseStart_6176388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176398 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6176398 : Nat := 118140960795 + 6176398 * 2 ^ 59
def prefixEnd_6176398 : Nat := 4983230072969 + 3 ^ 40 * 6176398 * 2
def baseEnd_6176398 : Nat := 3171460887468431048120269

theorem tailTrace_6176398 : CollatzResearch.WordTrace tailWord_6176398 prefixEnd_6176398 3171460887468431048120269 := by
  unfold tailWord_6176398
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158967734746545705378231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150181161251981577095350565 28158967734746545705378231)
  ·
    refine ⟨42238451602119818558067347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28158967734746545705378231 42238451602119818558067347)
    ·
      refine ⟨63357677403179727837101021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42238451602119818558067347 63357677403179727837101021)
      ·
        refine ⟨23759129026192397938912883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63357677403179727837101021 23759129026192397938912883)
        ·
          refine ⟨35638693539288596908369325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23759129026192397938912883 35638693539288596908369325)
          ·
            refine ⟨13364510077233223840638497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35638693539288596908369325 13364510077233223840638497)
            ·
              refine ⟨10023382557924917880478873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13364510077233223840638497 10023382557924917880478873)
              ·
                refine ⟨7517536918443688410359155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10023382557924917880478873 7517536918443688410359155)
                ·
                  refine ⟨11276305377665532615538733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517536918443688410359155 11276305377665532615538733)
                  ·
                    refine ⟨4228614516624574730827025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11276305377665532615538733 4228614516624574730827025)
                    ·
                      refine ⟨3171460887468431048120269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228614516624574730827025 3171460887468431048120269)
                      ·
                        rfl

theorem cell23_6176398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6176398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176398 prefixEnd_6176398 := by exact prefixLift 6176398
  have htrace : WordTrace (prefixWord ++ tailWord_6176398) baseStart_6176398 baseEnd_6176398 := by
    simpa [prefixWord, tailWord_6176398, baseEnd_6176398] using wordTrace_append hprefix tailTrace_6176398
  have hstable : (prefixWord ++ tailWord_6176398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176398).length < 2 ^ (prefixWord ++ tailWord_6176398).sum := by decide
  have hdescent : baseEnd_6176398 < baseStart_6176398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176414 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6176414 : Nat := 118140960795 + 6176414 * 2 ^ 59
def prefixEnd_6176414 : Nat := 4983230072969 + 3 ^ 40 * 6176414 * 2
def baseEnd_6176414 : Nat := 3171469103158902985520195

theorem tailTrace_6176414 : CollatzResearch.WordTrace tailWord_6176414 prefixEnd_6176414 3171469103158902985520195 := by
  unfold tailWord_6176414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159040680739300046951037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150181550297276266917072197 28159040680739300046951037)
  ·
    refine ⟨10559640255277237517606639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28159040680739300046951037 10559640255277237517606639)
    ·
      refine ⟨15839460382915856276409959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10559640255277237517606639 15839460382915856276409959)
      ·
        refine ⟨23759190574373784414614939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15839460382915856276409959 23759190574373784414614939)
        ·
          refine ⟨35638785861560676621922409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23759190574373784414614939 35638785861560676621922409)
          ·
            refine ⟨26729089396170507466441807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35638785861560676621922409 26729089396170507466441807)
            ·
              refine ⟨40093634094255761199662711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26729089396170507466441807 40093634094255761199662711)
              ·
                refine ⟨60140451141383641799494067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40093634094255761199662711 60140451141383641799494067)
                ·
                  refine ⟨90210676712075462699241101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60140451141383641799494067 90210676712075462699241101)
                  ·
                    refine ⟨33829003767028298512215413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90210676712075462699241101 33829003767028298512215413)
                    ·
                      refine ⟨3171469103158902985520195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33829003767028298512215413 3171469103158902985520195)
                      ·
                        rfl

theorem cell23_6176414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6176414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176414 prefixEnd_6176414 := by exact prefixLift 6176414
  have htrace : WordTrace (prefixWord ++ tailWord_6176414) baseStart_6176414 baseEnd_6176414 := by
    simpa [prefixWord, tailWord_6176414, baseEnd_6176414] using wordTrace_append hprefix tailTrace_6176414
  have hstable : (prefixWord ++ tailWord_6176414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176414).length < 2 ^ (prefixWord ++ tailWord_6176414).sum := by decide
  have hdescent : baseEnd_6176414 < baseStart_6176414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176434 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_6176434 : Nat := 118140960795 + 6176434 * 2 ^ 59
def prefixEnd_6176434 : Nat := 4983230072969 + 3 ^ 40 * 6176434 * 2
def baseEnd_6176434 : Nat := 352386596974665878585567

theorem tailTrace_6176434 : CollatzResearch.WordTrace tailWord_6176434 prefixEnd_6176434 352386596974665878585567 := by
  unfold tailWord_6176434
  simp only [CollatzResearch.WordTrace]
  refine ⟨56318263726460485947834089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150182036603894629194224237 56318263726460485947834089)
  ·
    refine ⟨42238697794845364460875567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56318263726460485947834089 42238697794845364460875567)
    ·
      refine ⟨63358046692268046691313351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42238697794845364460875567 63358046692268046691313351)
      ·
        refine ⟨95037070038402070036970027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63358046692268046691313351 95037070038402070036970027)
        ·
          refine ⟨142555605057603105055455041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95037070038402070036970027 142555605057603105055455041)
          ·
            refine ⟨106916703793202328791591281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142555605057603105055455041 106916703793202328791591281)
            ·
              refine ⟨80187527844901746593693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106916703793202328791591281 80187527844901746593693461)
              ·
                refine ⟨3758790367729769371579381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80187527844901746593693461 3758790367729769371579381)
                ·
                  refine ⟨352386596974665878585567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3758790367729769371579381 352386596974665878585567)
                  ·
                    rfl

theorem cell23_6176434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_6176434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176434 prefixEnd_6176434 := by exact prefixLift 6176434
  have htrace : WordTrace (prefixWord ++ tailWord_6176434) baseStart_6176434 baseEnd_6176434 := by
    simpa [prefixWord, tailWord_6176434, baseEnd_6176434] using wordTrace_append hprefix tailTrace_6176434
  have hstable : (prefixWord ++ tailWord_6176434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176434).length < 2 ^ (prefixWord ++ tailWord_6176434).sum := by decide
  have hdescent : baseEnd_6176434 < baseStart_6176434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176447 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 4, 5]
def baseStart_6176447 : Nat := 118140960795 + 6176447 * 2 ^ 59
def prefixEnd_6176447 : Nat := 4983230072969 + 3 ^ 40 * 6176447 * 2
def baseEnd_6176447 : Nat := 1057162016006833785469181

theorem tailTrace_6176447 : CollatzResearch.WordTrace tailWord_6176447 prefixEnd_6176447 1057162016006833785469181 := by
  unfold tailWord_6176447
  simp only [CollatzResearch.WordTrace]
  refine ⟨225273529054794847011559595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150182352703196564674373063 225273529054794847011559595)
  ·
    refine ⟨337910293582192270517339393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225273529054794847011559595 337910293582192270517339393)
    ·
      refine ⟨253432720186644202888004545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337910293582192270517339393 253432720186644202888004545)
      ·
        refine ⟨190074540139983152166003409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253432720186644202888004545 190074540139983152166003409)
        ·
          refine ⟨142555905104987364124502557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190074540139983152166003409 142555905104987364124502557)
          ·
            refine ⟨53458464414370261546688459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142555905104987364124502557 53458464414370261546688459)
            ·
              refine ⟨80187696621555392320032689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53458464414370261546688459 80187696621555392320032689)
              ·
                refine ⟨60140772466166544240024517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80187696621555392320032689 60140772466166544240024517)
                ·
                  refine ⟨11276394837406227045004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60140772466166544240024517 11276394837406227045004597)
                  ·
                    refine ⟨1057162016006833785469181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11276394837406227045004597 1057162016006833785469181)
                    ·
                      rfl

theorem cell23_6176447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_6176447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176447 prefixEnd_6176447 := by exact prefixLift 6176447
  have htrace : WordTrace (prefixWord ++ tailWord_6176447) baseStart_6176447 baseEnd_6176447 := by
    simpa [prefixWord, tailWord_6176447, baseEnd_6176447] using wordTrace_append hprefix tailTrace_6176447
  have hstable : (prefixWord ++ tailWord_6176447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176447).length < 2 ^ (prefixWord ++ tailWord_6176447).sum := by decide
  have hdescent : baseEnd_6176447 < baseStart_6176447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176484 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_6176484 : Nat := 118140960795 + 6176484 * 2 ^ 59
def prefixEnd_6176484 : Nat := 4983230072969 + 3 ^ 40 * 6176484 * 2
def baseEnd_6176484 : Nat := 3171505046804717711644873

theorem tailTrace_6176484 : CollatzResearch.WordTrace tailWord_6176484 prefixEnd_6176484 3171505046804717711644873 := by
  unfold tailWord_6176484
  simp only [CollatzResearch.WordTrace]
  refine ⟨112637439277830401165328253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150183252370440534887104337 112637439277830401165328253)
  ·
    refine ⟨42239039729186400436998095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112637439277830401165328253 42239039729186400436998095)
    ·
      refine ⟨63358559593779600655497143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42239039729186400436998095 63358559593779600655497143)
      ·
        refine ⟨95037839390669400983245715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63358559593779600655497143 95037839390669400983245715)
        ·
          refine ⟨142556759086004101474868573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95037839390669400983245715 142556759086004101474868573)
          ·
            refine ⟨53458784657251538053075715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142556759086004101474868573 53458784657251538053075715)
            ·
              refine ⟨80188176985877307079613573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53458784657251538053075715 80188176985877307079613573)
              ·
                refine ⟨15035283184851995077427545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80188176985877307079613573 15035283184851995077427545)
                ·
                  refine ⟨11276462388638996308070659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15035283184851995077427545 11276462388638996308070659)
                  ·
                    refine ⟨16914693582958494462105989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11276462388638996308070659 16914693582958494462105989)
                    ·
                      refine ⟨3171505046804717711644873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16914693582958494462105989 3171505046804717711644873)
                      ·
                        rfl

theorem cell23_6176484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_6176484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176484 prefixEnd_6176484 := by exact prefixLift 6176484
  have htrace : WordTrace (prefixWord ++ tailWord_6176484) baseStart_6176484 baseEnd_6176484 := by
    simpa [prefixWord, tailWord_6176484, baseEnd_6176484] using wordTrace_append hprefix tailTrace_6176484
  have hstable : (prefixWord ++ tailWord_6176484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176484).length < 2 ^ (prefixWord ++ tailWord_6176484).sum := by decide
  have hdescent : baseEnd_6176484 < baseStart_6176484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176561 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_6176561 : Nat := 118140960795 + 6176561 * 2 ^ 59
def prefixEnd_6176561 : Nat := 4983230072969 + 3 ^ 40 * 6176561 * 2
def baseEnd_6176561 : Nat := 3171544584815113910382019

theorem tailTrace_6176561 : CollatzResearch.WordTrace tailWord_6176561 prefixEnd_6176561 3171544584815113910382019 := by
  unfold tailWord_6176561
  simp only [CollatzResearch.WordTrace]
  refine ⟨225277686976381844481209537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150185124650921229654139691 225277686976381844481209537)
  ·
    refine ⟨168958265232286383360907153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225277686976381844481209537 168958265232286383360907153)
    ·
      refine ⟨126718698924214787520680365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168958265232286383360907153 126718698924214787520680365)
      ·
        refine ⟨47519512096580545320255137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126718698924214787520680365 47519512096580545320255137)
        ·
          refine ⟨35639634072435408990191353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47519512096580545320255137 35639634072435408990191353)
          ·
            refine ⟨26729725554326556742643515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35639634072435408990191353 26729725554326556742643515)
            ·
              refine ⟨40094588331489835113965273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26729725554326556742643515 40094588331489835113965273)
              ·
                refine ⟨30070941248617376335473955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40094588331489835113965273 30070941248617376335473955)
                ·
                  refine ⟨45106411872926064503210933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30070941248617376335473955 45106411872926064503210933)
                  ·
                    refine ⟨4228726113086818547176025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45106411872926064503210933 4228726113086818547176025)
                    ·
                      refine ⟨3171544584815113910382019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228726113086818547176025 3171544584815113910382019)
                      ·
                        rfl

theorem cell23_6176561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_6176561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176561 prefixEnd_6176561 := by exact prefixLift 6176561
  have htrace : WordTrace (prefixWord ++ tailWord_6176561) baseStart_6176561 baseEnd_6176561 := by
    simpa [prefixWord, tailWord_6176561, baseEnd_6176561] using wordTrace_append hprefix tailTrace_6176561
  have hstable : (prefixWord ++ tailWord_6176561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176561).length < 2 ^ (prefixWord ++ tailWord_6176561).sum := by decide
  have hdescent : baseEnd_6176561 < baseStart_6176561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176601 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 2, 4]
def baseStart_6176601 : Nat := 118140960795 + 6176601 * 2 ^ 59
def prefixEnd_6176601 : Nat := 4983230072969 + 3 ^ 40 * 6176601 * 2
def baseEnd_6176601 : Nat := 1057188374680431251293945

theorem tailTrace_6176601 : CollatzResearch.WordTrace tailWord_6176601 prefixEnd_6176601 1057188374680431251293945 := by
  unfold tailWord_6176601
  simp only [CollatzResearch.WordTrace]
  refine ⟨225279145896236931312665657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150186097264157954208443771 225279145896236931312665657)
  ·
    refine ⟨168959359422177698484499243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225279145896236931312665657 168959359422177698484499243)
    ·
      refine ⟨253439039133266547726748865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168959359422177698484499243 253439039133266547726748865)
      ·
        refine ⟨190079279349949910795061649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253439039133266547726748865 190079279349949910795061649)
        ·
          refine ⟨142559459512462433096296237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190079279349949910795061649 142559459512462433096296237)
          ·
            refine ⟨53459797317173412411111089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142559459512462433096296237 53459797317173412411111089)
            ·
              refine ⟨40094847987880059308333317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53459797317173412411111089 40094847987880059308333317)
              ·
                refine ⟨7517783997727511120312497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40094847987880059308333317 7517783997727511120312497)
                ·
                  refine ⟨5638337998295633340234373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7517783997727511120312497 5638337998295633340234373)
                  ·
                    refine ⟨1057188374680431251293945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638337998295633340234373 1057188374680431251293945)
                    ·
                      rfl

theorem cell23_6176601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 4].length) (baseStart_6176601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176601 prefixEnd_6176601 := by exact prefixLift 6176601
  have htrace : WordTrace (prefixWord ++ tailWord_6176601) baseStart_6176601 baseEnd_6176601 := by
    simpa [prefixWord, tailWord_6176601, baseEnd_6176601] using wordTrace_append hprefix tailTrace_6176601
  have hstable : (prefixWord ++ tailWord_6176601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176601).length < 2 ^ (prefixWord ++ tailWord_6176601).sum := by decide
  have hdescent : baseEnd_6176601 < baseStart_6176601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176638 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6176638 : Nat := 118140960795 + 6176638 * 2 ^ 59
def prefixEnd_6176638 : Nat := 4983230072969 + 3 ^ 40 * 6176638 * 2
def baseEnd_6176638 : Nat := 3171584122825510109119165

theorem tailTrace_6176638 : CollatzResearch.WordTrace tailWord_6176638 prefixEnd_6176638 3171584122825510109119165 := by
  unfold tailWord_6176638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160061924637860828970321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150186996931401924421175045 28160061924637860828970321)
  ·
    refine ⟨21120046443478395621727741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28160061924637860828970321 21120046443478395621727741)
    ·
      refine ⟨7920017416304398358147903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21120046443478395621727741 7920017416304398358147903)
      ·
        refine ⟨11880026124456597537221855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7920017416304398358147903 11880026124456597537221855)
        ·
          refine ⟨17820039186684896305832783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11880026124456597537221855 17820039186684896305832783)
          ·
            refine ⟨26730058780027344458749175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17820039186684896305832783 26730058780027344458749175)
            ·
              refine ⟨40095088170041016688123763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26730058780027344458749175 40095088170041016688123763)
              ·
                refine ⟨60142632255061525032185645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40095088170041016688123763 60142632255061525032185645)
                ·
                  refine ⟨22553487095648071887069617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60142632255061525032185645 22553487095648071887069617)
                  ·
                    refine ⟨16915115321736053915302213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22553487095648071887069617 16915115321736053915302213)
                    ·
                      refine ⟨3171584122825510109119165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16915115321736053915302213 3171584122825510109119165)
                      ·
                        rfl

theorem cell23_6176638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6176638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176638 prefixEnd_6176638 := by exact prefixLift 6176638
  have htrace : WordTrace (prefixWord ++ tailWord_6176638) baseStart_6176638 baseEnd_6176638 := by
    simpa [prefixWord, tailWord_6176638, baseEnd_6176638] using wordTrace_append hprefix tailTrace_6176638
  have hstable : (prefixWord ++ tailWord_6176638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176638).length < 2 ^ (prefixWord ++ tailWord_6176638).sum := by decide
  have hdescent : baseEnd_6176638 < baseStart_6176638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176702 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_6176702 : Nat := 118140960795 + 6176702 * 2 ^ 59
def prefixEnd_6176702 : Nat := 4983230072969 + 3 ^ 40 * 6176702 * 2
def baseEnd_6176702 : Nat := 3171616985587397858718871

theorem tailTrace_6176702 : CollatzResearch.WordTrace tailWord_6176702 prefixEnd_6176702 3171616985587397858718871 := by
  unfold tailWord_6176702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160353708608878195261545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150188553112580683708061573 28160353708608878195261545)
  ·
    refine ⟨21120265281456658646446159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28160353708608878195261545 21120265281456658646446159)
    ·
      refine ⟨31680397922184987969669239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21120265281456658646446159 31680397922184987969669239)
      ·
        refine ⟨47520596883277481954503859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31680397922184987969669239 47520596883277481954503859)
        ·
          refine ⟨71280895324916222931755789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47520596883277481954503859 71280895324916222931755789)
          ·
            refine ⟨26730335746843583599408421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71280895324916222931755789 26730335746843583599408421)
            ·
              refine ⟨5011937952533171924889079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26730335746843583599408421 5011937952533171924889079)
              ·
                refine ⟨7517906928799757887333619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011937952533171924889079 7517906928799757887333619)
                ·
                  refine ⟨11276860393199636831000429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517906928799757887333619 11276860393199636831000429)
                  ·
                    refine ⟨4228822647449863811625161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11276860393199636831000429 4228822647449863811625161)
                    ·
                      refine ⟨3171616985587397858718871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228822647449863811625161 3171616985587397858718871)
                      ·
                        rfl

theorem cell23_6176702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_6176702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176702 prefixEnd_6176702 := by exact prefixLift 6176702
  have htrace : WordTrace (prefixWord ++ tailWord_6176702) baseStart_6176702 baseEnd_6176702 := by
    simpa [prefixWord, tailWord_6176702, baseEnd_6176702] using wordTrace_append hprefix tailTrace_6176702
  have hstable : (prefixWord ++ tailWord_6176702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176702).length < 2 ^ (prefixWord ++ tailWord_6176702).sum := by decide
  have hdescent : baseEnd_6176702 < baseStart_6176702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176704 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 9]
def baseStart_6176704 : Nat := 118140960795 + 6176704 * 2 ^ 59
def prefixEnd_6176704 : Nat := 4983230072969 + 3 ^ 40 * 6176704 * 2
def baseEnd_6176704 : Nat := 352402001394300761210429

theorem tailTrace_6176704 : CollatzResearch.WordTrace tailWord_6176704 prefixEnd_6176704 352402001394300761210429 := by
  unfold tailWord_6176704
  simp only [CollatzResearch.WordTrace]
  refine ⟨112641451307431889951832583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150188601743242519935776777 112641451307431889951832583)
  ·
    refine ⟨168962176961147834927748875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112641451307431889951832583 168962176961147834927748875)
    ·
      refine ⟨253443265441721752391623313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168962176961147834927748875 253443265441721752391623313)
      ·
        refine ⟨190082449081291314293717485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253443265441721752391623313 190082449081291314293717485)
        ·
          refine ⟨71280918405484242860144057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190082449081291314293717485 71280918405484242860144057)
          ·
            refine ⟨53460688804113182145108043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71280918405484242860144057 53460688804113182145108043)
            ·
              refine ⟨80191033206169773217662065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53460688804113182145108043 80191033206169773217662065)
              ·
                refine ⟨60143274904627329913246549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80191033206169773217662065 60143274904627329913246549)
                ·
                  refine ⟨352402001394300761210429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60143274904627329913246549 352402001394300761210429)
                  ·
                    rfl

theorem cell23_6176704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_6176704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176704 prefixEnd_6176704 := by exact prefixLift 6176704
  have htrace : WordTrace (prefixWord ++ tailWord_6176704) baseStart_6176704 baseEnd_6176704 := by
    simpa [prefixWord, tailWord_6176704, baseEnd_6176704] using wordTrace_append hprefix tailTrace_6176704
  have hstable : (prefixWord ++ tailWord_6176704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176704).length < 2 ^ (prefixWord ++ tailWord_6176704).sum := by decide
  have hdescent : baseEnd_6176704 < baseStart_6176704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176751 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 2, 5]
def baseStart_6176751 : Nat := 118140960795 + 6176751 * 2 ^ 59
def prefixEnd_6176751 : Nat := 4983230072969 + 3 ^ 40 * 6176751 * 2
def baseEnd_6176751 : Nat := 1057214048713156055668715

theorem tailTrace_6176751 : CollatzResearch.WordTrace tailWord_6176751 prefixEnd_6176751 1057214048713156055668715 := by
  unfold tailWord_6176751
  simp only [CollatzResearch.WordTrace]
  refine ⟨225284616845693506930626107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150189744563795671287084071 225284616845693506930626107)
  ·
    refine ⟨337926925268540260395939161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225284616845693506930626107 337926925268540260395939161)
    ·
      refine ⟨253445193951405195296954371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337926925268540260395939161 253445193951405195296954371)
      ·
        refine ⟨380167790927107792945431557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253445193951405195296954371 380167790927107792945431557)
        ·
          refine ⟨71281460798832711177268417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380167790927107792945431557 71281460798832711177268417)
          ·
            refine ⟨53461095599124533382951313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71281460798832711177268417 53461095599124533382951313)
            ·
              refine ⟨40095821699343400037213485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53461095599124533382951313 40095821699343400037213485)
              ·
                refine ⟨15035933137253775013955057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40095821699343400037213485 15035933137253775013955057)
                ·
                  refine ⟨11276949852940331260466293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15035933137253775013955057 11276949852940331260466293)
                  ·
                    refine ⟨1057214048713156055668715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11276949852940331260466293 1057214048713156055668715)
                    ·
                      rfl

theorem cell23_6176751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_6176751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176751 prefixEnd_6176751 := by exact prefixLift 6176751
  have htrace : WordTrace (prefixWord ++ tailWord_6176751) baseStart_6176751 baseEnd_6176751 := by
    simpa [prefixWord, tailWord_6176751, baseEnd_6176751] using wordTrace_append hprefix tailTrace_6176751
  have hstable : (prefixWord ++ tailWord_6176751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176751).length < 2 ^ (prefixWord ++ tailWord_6176751).sum := by decide
  have hdescent : baseEnd_6176751 < baseStart_6176751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176772 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 7]
def baseStart_6176772 : Nat := 118140960795 + 6176772 * 2 ^ 59
def prefixEnd_6176772 : Nat := 4983230072969 + 3 ^ 40 * 6176772 * 2
def baseEnd_6176772 : Nat := 352405881025912509427061

theorem tailTrace_6176772 : CollatzResearch.WordTrace tailWord_6176772 prefixEnd_6176772 352405881025912509427061 := by
  unfold tailWord_6176772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112642691389308713758570285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150190255185744951678093713 112642691389308713758570285)
  ·
    refine ⟨42241009270990767659463857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112642691389308713758570285 42241009270990767659463857)
    ·
      refine ⟨31680756953243075744597893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42241009270990767659463857 31680756953243075744597893)
      ·
        refine ⟨5940141928733076702112105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31680756953243075744597893 5940141928733076702112105)
        ·
          refine ⟨4455106446549807526584079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940141928733076702112105 4455106446549807526584079)
          ·
            refine ⟨6682659669824711289876119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455106446549807526584079 6682659669824711289876119)
            ·
              refine ⟨10023989504737066934814179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682659669824711289876119 10023989504737066934814179)
              ·
                refine ⟨15035984257105600402221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10023989504737066934814179 15035984257105600402221269)
                ·
                  refine ⟨352405881025912509427061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15035984257105600402221269 352405881025912509427061)
                  ·
                    rfl

theorem cell23_6176772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_6176772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176772 prefixEnd_6176772 := by exact prefixLift 6176772
  have htrace : WordTrace (prefixWord ++ tailWord_6176772) baseStart_6176772 baseEnd_6176772 := by
    simpa [prefixWord, tailWord_6176772, baseEnd_6176772] using wordTrace_append hprefix tailTrace_6176772
  have hstable : (prefixWord ++ tailWord_6176772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176772).length < 2 ^ (prefixWord ++ tailWord_6176772).sum := by decide
  have hdescent : baseEnd_6176772 < baseStart_6176772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176778 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6176778 : Nat := 118140960795 + 6176778 * 2 ^ 59
def prefixEnd_6176778 : Nat := 4983230072969 + 3 ^ 40 * 6176778 * 2
def baseEnd_6176778 : Nat := 3171656010117139561368521

theorem tailTrace_6176778 : CollatzResearch.WordTrace tailWord_6176778 prefixEnd_6176778 3171656010117139561368521 := by
  unfold tailWord_6176778
  simp only [CollatzResearch.WordTrace]
  refine ⟨56321400404148922635464747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150190401077730460361239325 56321400404148922635464747)
  ·
    refine ⟨84482100606223383953197121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56321400404148922635464747 84482100606223383953197121)
    ·
      refine ⟨63361575454667537964897841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84482100606223383953197121 63361575454667537964897841)
      ·
        refine ⟨47521181591000653473673381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63361575454667537964897841 47521181591000653473673381)
        ·
          refine ⟨8910221548312622526313759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47521181591000653473673381 8910221548312622526313759)
          ·
            refine ⟨13365332322468933789470639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910221548312622526313759 13365332322468933789470639)
            ·
              refine ⟨20047998483703400684205959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13365332322468933789470639 20047998483703400684205959)
              ·
                refine ⟨30071997725555101026308939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20047998483703400684205959 30071997725555101026308939)
                ·
                  refine ⟨45107996588332651539463409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30071997725555101026308939 45107996588332651539463409)
                  ·
                    refine ⟨33830997441249488654597557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45107996588332651539463409 33830997441249488654597557)
                    ·
                      refine ⟨3171656010117139561368521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33830997441249488654597557 3171656010117139561368521)
                      ·
                        rfl

theorem cell23_6176778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6176778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176778 prefixEnd_6176778 := by exact prefixLift 6176778
  have htrace : WordTrace (prefixWord ++ tailWord_6176778) baseStart_6176778 baseEnd_6176778 := by
    simpa [prefixWord, tailWord_6176778, baseEnd_6176778] using wordTrace_append hprefix tailTrace_6176778
  have hstable : (prefixWord ++ tailWord_6176778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176778).length < 2 ^ (prefixWord ++ tailWord_6176778).sum := by decide
  have hdescent : baseEnd_6176778 < baseStart_6176778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176828 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 6]
def baseStart_6176828 : Nat := 118140960795 + 6176828 * 2 ^ 59
def prefixEnd_6176828 : Nat := 4983230072969 + 3 ^ 40 * 6176828 * 2
def baseEnd_6176828 : Nat := 352409076016651596193699

theorem tailTrace_6176828 : CollatzResearch.WordTrace tailWord_6176828 prefixEnd_6176828 352409076016651596193699 := by
  unfold tailWord_6176828
  simp only [CollatzResearch.WordTrace]
  refine ⟨112643712633207274540589569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150191616844276366054119425 112643712633207274540589569)
  ·
    refine ⟨84482784474905455905442177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112643712633207274540589569 84482784474905455905442177)
    ·
      refine ⟨63362088356179091929081633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84482784474905455905442177 63362088356179091929081633)
      ·
        refine ⟨47521566267134318946811225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63362088356179091929081633 47521566267134318946811225)
        ·
          refine ⟨35641174700350739210108419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47521566267134318946811225 35641174700350739210108419)
          ·
            refine ⟨53461762050526108815162629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35641174700350739210108419 53461762050526108815162629)
            ·
              refine ⟨10024080384473645402842993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53461762050526108815162629 10024080384473645402842993)
              ·
                refine ⟨7518060288355234052132245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10024080384473645402842993 7518060288355234052132245)
                ·
                  refine ⟨352409076016651596193699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7518060288355234052132245 352409076016651596193699)
                  ·
                    rfl

theorem cell23_6176828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_6176828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176828 prefixEnd_6176828 := by exact prefixLift 6176828
  have htrace : WordTrace (prefixWord ++ tailWord_6176828) baseStart_6176828 baseEnd_6176828 := by
    simpa [prefixWord, tailWord_6176828, baseEnd_6176828] using wordTrace_append hprefix tailTrace_6176828
  have hstable : (prefixWord ++ tailWord_6176828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176828).length < 2 ^ (prefixWord ++ tailWord_6176828).sum := by decide
  have hdescent : baseEnd_6176828 < baseStart_6176828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176832 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 1, 4]
def baseStart_6176832 : Nat := 118140960795 + 6176832 * 2 ^ 59
def prefixEnd_6176832 : Nat := 4983230072969 + 3 ^ 40 * 6176832 * 2
def baseEnd_6176832 : Nat := 1057227912690827450031091

theorem tailTrace_6176832 : CollatzResearch.WordTrace tailWord_6176832 prefixEnd_6176832 1057227912690827450031091 := by
  unfold tailWord_6176832
  simp only [CollatzResearch.WordTrace]
  refine ⟨112643785579200028882162375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150191714105600038509549833 112643785579200028882162375)
  ·
    refine ⟨168965678368800043323243563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112643785579200028882162375 168965678368800043323243563)
    ·
      refine ⟨253448517553200064984865345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168965678368800043323243563 253448517553200064984865345)
      ·
        refine ⟨190086388164900048738649009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253448517553200064984865345 190086388164900048738649009)
        ·
          refine ⟨142564791123675036553986757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190086388164900048738649009 142564791123675036553986757)
          ·
            refine ⟨26730898335689069353872517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142564791123675036553986757 26730898335689069353872517)
            ·
              refine ⟨5012043437941700503851097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26730898335689069353872517 5012043437941700503851097)
              ·
                refine ⟨3759032578456275377888323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012043437941700503851097 3759032578456275377888323)
                ·
                  refine ⟨5638548867684413066832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759032578456275377888323 5638548867684413066832485)
                  ·
                    refine ⟨1057227912690827450031091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638548867684413066832485 1057227912690827450031091)
                    ·
                      rfl

theorem cell23_6176832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_6176832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176832 prefixEnd_6176832 := by exact prefixLift 6176832
  have htrace : WordTrace (prefixWord ++ tailWord_6176832) baseStart_6176832 baseEnd_6176832 := by
    simpa [prefixWord, tailWord_6176832, baseEnd_6176832] using wordTrace_append hprefix tailTrace_6176832
  have hstable : (prefixWord ++ tailWord_6176832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176832).length < 2 ^ (prefixWord ++ tailWord_6176832).sum := by decide
  have hdescent : baseEnd_6176832 < baseStart_6176832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176841 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 5, 5]
def baseStart_6176841 : Nat := 118140960795 + 6176841 * 2 ^ 59
def prefixEnd_6176841 : Nat := 4983230072969 + 3 ^ 40 * 6176841 * 2
def baseEnd_6176841 : Nat := 1057229453132790938293577

theorem tailTrace_6176841 : CollatzResearch.WordTrace tailWord_6176841 prefixEnd_6176841 1057229453132790938293577 := by
  unfold tailWord_6176841
  simp only [CollatzResearch.WordTrace]
  refine ⟨225287899415367452301402377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150191932943578301534268251 225287899415367452301402377)
  ·
    refine ⟨168965924561525589226051783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225287899415367452301402377 168965924561525589226051783)
    ·
      refine ⟨253448886842288383839077675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168965924561525589226051783 253448886842288383839077675)
      ·
        refine ⟨380173330263432575758616513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253448886842288383839077675 380173330263432575758616513)
        ·
          refine ⟨285129997697574431818962385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380173330263432575758616513 285129997697574431818962385)
          ·
            refine ⟨213847498273180823864221789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285129997697574431818962385 213847498273180823864221789)
            ·
              refine ⟨80192811852442808949083171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213847498273180823864221789 80192811852442808949083171)
              ·
                refine ⟨120289217778664213423624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80192811852442808949083171 120289217778664213423624757)
                ·
                  refine ⟨11277114166749770008464821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120289217778664213423624757 11277114166749770008464821)
                  ·
                    refine ⟨1057229453132790938293577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11277114166749770008464821 1057229453132790938293577)
                    ·
                      rfl

theorem cell23_6176841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_6176841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176841 prefixEnd_6176841 := by exact prefixLift 6176841
  have htrace : WordTrace (prefixWord ++ tailWord_6176841) baseStart_6176841 baseEnd_6176841 := by
    simpa [prefixWord, tailWord_6176841, baseEnd_6176841] using wordTrace_append hprefix tailTrace_6176841
  have hstable : (prefixWord ++ tailWord_6176841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176841).length < 2 ^ (prefixWord ++ tailWord_6176841).sum := by decide
  have hdescent : baseEnd_6176841 < baseStart_6176841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176858 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_6176858 : Nat := 118140960795 + 6176858 * 2 ^ 59
def prefixEnd_6176858 : Nat := 4983230072969 + 3 ^ 40 * 6176858 * 2
def baseEnd_6176858 : Nat := 1057232362856499749456051

theorem tailTrace_6176858 : CollatzResearch.WordTrace tailWord_6176858 prefixEnd_6176858 1057232362856499749456051 := by
  unfold tailWord_6176858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56322129864076466051192807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150192346304203909469847485 56322129864076466051192807)
  ·
    refine ⟨84483194796114699076789211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56322129864076466051192807 84483194796114699076789211)
    ·
      refine ⟨126724792194172048615183817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84483194796114699076789211 126724792194172048615183817)
      ·
        refine ⟨95043594145629036461387863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126724792194172048615183817 95043594145629036461387863)
        ·
          refine ⟨142565391218443554692081795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95043594145629036461387863 142565391218443554692081795)
          ·
            refine ⟨213848086827665332038122693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142565391218443554692081795 213848086827665332038122693)
            ·
              refine ⟨40096516280187249757148005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213848086827665332038122693 40096516280187249757148005)
              ·
                refine ⟨7518096802535109329465251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40096516280187249757148005 7518096802535109329465251)
                ·
                  refine ⟨11277145203802663994197877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518096802535109329465251 11277145203802663994197877)
                  ·
                    refine ⟨1057232362856499749456051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11277145203802663994197877 1057232362856499749456051)
                    ·
                      rfl

theorem cell23_6176858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_6176858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176858 prefixEnd_6176858 := by exact prefixLift 6176858
  have htrace : WordTrace (prefixWord ++ tailWord_6176858) baseStart_6176858 baseEnd_6176858 := by
    simpa [prefixWord, tailWord_6176858, baseEnd_6176858] using wordTrace_append hprefix tailTrace_6176858
  have hstable : (prefixWord ++ tailWord_6176858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176858).length < 2 ^ (prefixWord ++ tailWord_6176858).sum := by decide
  have hdescent : baseEnd_6176858 < baseStart_6176858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176891 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_6176891 : Nat := 118140960795 + 6176891 * 2 ^ 59
def prefixEnd_6176891 : Nat := 4983230072969 + 3 ^ 40 * 6176891 * 2
def baseEnd_6176891 : Nat := 3171714033431097619255501

theorem tailTrace_6176891 : CollatzResearch.WordTrace tailWord_6176891 prefixEnd_6176891 3171714033431097619255501 := by
  unfold tailWord_6176891
  simp only [CollatzResearch.WordTrace]
  refine ⟨225289723065186310840722527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150193148710124207227148351 225289723065186310840722527)
  ·
    refine ⟨337934584597779466261083791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225289723065186310840722527 337934584597779466261083791)
    ·
      refine ⟨506901876896669199391625687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337934584597779466261083791 506901876896669199391625687)
      ·
        refine ⟨760352815345003799087438531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506901876896669199391625687 760352815345003799087438531)
        ·
          refine ⟨1140529223017505698631157797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760352815345003799087438531 1140529223017505698631157797)
          ·
            refine ⟨213849229315782318493342087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1140529223017505698631157797 213849229315782318493342087)
            ·
              refine ⟨320773843973673477740013131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213849229315782318493342087 320773843973673477740013131)
              ·
                refine ⟨481160765960510216610019697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320773843973673477740013131 481160765960510216610019697)
                ·
                  refine ⟨360870574470382662457514773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481160765960510216610019697 360870574470382662457514773)
                  ·
                    refine ⟨16915808178299187302696005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360870574470382662457514773 16915808178299187302696005)
                    ·
                      refine ⟨3171714033431097619255501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16915808178299187302696005 3171714033431097619255501)
                      ·
                        rfl

theorem cell23_6176891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_6176891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176891 prefixEnd_6176891 := by exact prefixLift 6176891
  have htrace : WordTrace (prefixWord ++ tailWord_6176891) baseStart_6176891 baseEnd_6176891 := by
    simpa [prefixWord, tailWord_6176891, baseEnd_6176891] using wordTrace_append hprefix tailTrace_6176891
  have hstable : (prefixWord ++ tailWord_6176891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176891).length < 2 ^ (prefixWord ++ tailWord_6176891).sum := by decide
  have hdescent : baseEnd_6176891 < baseStart_6176891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6176921 : Nat := 118140960795 + 6176921 * 2 ^ 59
def prefixEnd_6176921 : Nat := 4983230072969 + 3 ^ 40 * 6176921 * 2
def baseEnd_6176921 : Nat := 3171729437850732501880363

theorem tailTrace_6176921 : CollatzResearch.WordTrace tailWord_6176921 prefixEnd_6176921 3171729437850732501880363 := by
  unfold tailWord_6176921
  simp only [CollatzResearch.WordTrace]
  refine ⟨225290817255077625964314617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150193878170051750642876411 225290817255077625964314617)
  ·
    refine ⟨168968112941308219473235963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225290817255077625964314617 168968112941308219473235963)
    ·
      refine ⟨253452169411962329209853945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168968112941308219473235963 253452169411962329209853945)
      ·
        refine ⟨190089127058971746907390459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253452169411962329209853945 190089127058971746907390459)
        ·
          refine ⟨285133690588457620361085689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190089127058971746907390459 285133690588457620361085689)
          ·
            refine ⟨213850267941343215270814267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285133690588457620361085689 213850267941343215270814267)
            ·
              refine ⟨320775401912014822906221401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213850267941343215270814267 320775401912014822906221401)
              ·
                refine ⟨240581551434011117179666051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320775401912014822906221401 240581551434011117179666051)
                ·
                  refine ⟨360872327151016675769499077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240581551434011117179666051 360872327151016675769499077)
                  ·
                    refine ⟨67663561340815626706781077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 360872327151016675769499077 67663561340815626706781077)
                    ·
                      refine ⟨3171729437850732501880363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67663561340815626706781077 3171729437850732501880363)
                      ·
                        rfl

theorem cell23_6176921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6176921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176921 prefixEnd_6176921 := by exact prefixLift 6176921
  have htrace : WordTrace (prefixWord ++ tailWord_6176921) baseStart_6176921 baseEnd_6176921 := by
    simpa [prefixWord, tailWord_6176921, baseEnd_6176921] using wordTrace_append hprefix tailTrace_6176921
  have hstable : (prefixWord ++ tailWord_6176921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176921).length < 2 ^ (prefixWord ++ tailWord_6176921).sum := by decide
  have hdescent : baseEnd_6176921 < baseStart_6176921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176931 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 9]
def baseStart_6176931 : Nat := 118140960795 + 6176931 * 2 ^ 59
def prefixEnd_6176931 : Nat := 4983230072969 + 3 ^ 40 * 6176931 * 2
def baseEnd_6176931 : Nat := 1057244857552425820918439

theorem tailTrace_6176931 : CollatzResearch.WordTrace tailWord_6176931 prefixEnd_6176931 1057244857552425820918439 := by
  unfold tailWord_6176931
  simp only [CollatzResearch.WordTrace]
  refine ⟨225291181985041397672178647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150194121323360931781452431 225291181985041397672178647)
  ·
    refine ⟨337936772977562096508267971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225291181985041397672178647 337936772977562096508267971)
    ·
      refine ⟨506905159466343144762401957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337936772977562096508267971 506905159466343144762401957)
      ·
        refine ⟨95044717399939339642950367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506905159466343144762401957 95044717399939339642950367)
        ·
          refine ⟨142567076099909009464425551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95044717399939339642950367 142567076099909009464425551)
          ·
            refine ⟨213850614149863514196638327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142567076099909009464425551 213850614149863514196638327)
            ·
              refine ⟨320775921224795271294957491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213850614149863514196638327 320775921224795271294957491)
              ·
                refine ⟨481163881837192906942436237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320775921224795271294957491 481163881837192906942436237)
                ·
                  refine ⟨180436455688947340103413589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481163881837192906942436237 180436455688947340103413589)
                  ·
                    refine ⟨1057244857552425820918439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180436455688947340103413589 1057244857552425820918439)
                    ·
                      rfl

theorem cell23_6176931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_6176931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176931 prefixEnd_6176931 := by exact prefixLift 6176931
  have htrace : WordTrace (prefixWord ++ tailWord_6176931) baseStart_6176931 baseEnd_6176931 := by
    simpa [prefixWord, tailWord_6176931, baseEnd_6176931] using wordTrace_append hprefix tailTrace_6176931
  have hstable : (prefixWord ++ tailWord_6176931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176931).length < 2 ^ (prefixWord ++ tailWord_6176931).sum := by decide
  have hdescent : baseEnd_6176931 < baseStart_6176931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176935 : List Nat := [1, 1, 6, 2, 2, 2, 9]
def baseStart_6176935 : Nat := 118140960795 + 6176935 * 2 ^ 59
def prefixEnd_6176935 : Nat := 4983230072969 + 3 ^ 40 * 6176935 * 2
def baseEnd_6176935 : Nat := 39157242303455499346979

theorem tailTrace_6176935 : CollatzResearch.WordTrace tailWord_6176935 prefixEnd_6176935 39157242303455499346979 := by
  unfold tailWord_6176935
  simp only [CollatzResearch.WordTrace]
  refine ⟨225291327877026906355324259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150194218584684604236882839 225291327877026906355324259)
  ·
    refine ⟨337936991815540359532986389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225291327877026906355324259 337936991815540359532986389)
    ·
      refine ⟨15840796491353454353108737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 337936991815540359532986389 15840796491353454353108737)
      ·
        refine ⟨11880597368515090764831553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15840796491353454353108737 11880597368515090764831553)
        ·
          refine ⟨8910448026386318073623665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11880597368515090764831553 8910448026386318073623665)
          ·
            refine ⟨6682836019789738555217749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910448026386318073623665 6682836019789738555217749)
            ·
              refine ⟨39157242303455499346979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6682836019789738555217749 39157242303455499346979)
              ·
                rfl

theorem cell23_6176935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 9].length) (baseStart_6176935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176935 prefixEnd_6176935 := by exact prefixLift 6176935
  have htrace : WordTrace (prefixWord ++ tailWord_6176935) baseStart_6176935 baseEnd_6176935 := by
    simpa [prefixWord, tailWord_6176935, baseEnd_6176935] using wordTrace_append hprefix tailTrace_6176935
  have hstable : (prefixWord ++ tailWord_6176935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176935).length < 2 ^ (prefixWord ++ tailWord_6176935).sum := by decide
  have hdescent : baseEnd_6176935 < baseStart_6176935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176946 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_6176946 : Nat := 118140960795 + 6176946 * 2 ^ 59
def prefixEnd_6176946 : Nat := 4983230072969 + 3 ^ 40 * 6176946 * 2
def baseEnd_6176946 : Nat := 3171742274867094904067749

theorem tailTrace_6176946 : CollatzResearch.WordTrace tailWord_6176946 prefixEnd_6176946 3171742274867094904067749 := by
  unfold tailWord_6176946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56322932269996763808493673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150194486053324703489316461 56322932269996763808493673)
  ·
    refine ⟨42242199202497572856370255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56322932269996763808493673 42242199202497572856370255)
    ·
      refine ⟨63363298803746359284555383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42242199202497572856370255 63363298803746359284555383)
      ·
        refine ⟨95044948205619538926833075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63363298803746359284555383 95044948205619538926833075)
        ·
          refine ⟨142567422308429308390249613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95044948205619538926833075 142567422308429308390249613)
          ·
            refine ⟨53462783365660990646343605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142567422308429308390249613 53462783365660990646343605)
            ·
              refine ⟨5012135940530717873094713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53462783365660990646343605 5012135940530717873094713)
              ·
                refine ⟨3759101955398038404821035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012135940530717873094713 3759101955398038404821035)
                ·
                  refine ⟨5638652933097057607231553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759101955398038404821035 5638652933097057607231553)
                  ·
                    refine ⟨4228989699822793205423665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638652933097057607231553 4228989699822793205423665)
                    ·
                      refine ⟨3171742274867094904067749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228989699822793205423665 3171742274867094904067749)
                      ·
                        rfl

theorem cell23_6176946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_6176946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176946 prefixEnd_6176946 := by exact prefixLift 6176946
  have htrace : WordTrace (prefixWord ++ tailWord_6176946) baseStart_6176946 baseEnd_6176946 := by
    simpa [prefixWord, tailWord_6176946, baseEnd_6176946] using wordTrace_append hprefix tailTrace_6176946
  have hstable : (prefixWord ++ tailWord_6176946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176946).length < 2 ^ (prefixWord ++ tailWord_6176946).sum := by decide
  have hdescent : baseEnd_6176946 < baseStart_6176946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176955 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 3, 3, 2]
def baseStart_6176955 : Nat := 118140960795 + 6176955 * 2 ^ 59
def prefixEnd_6176955 : Nat := 4983230072969 + 3 ^ 40 * 6176955 * 2
def baseEnd_6176955 : Nat := 3171746896192985368855207

theorem tailTrace_6176955 : CollatzResearch.WordTrace tailWord_6176955 prefixEnd_6176955 3171746896192985368855207 := by
  unfold tailWord_6176955
  simp only [CollatzResearch.WordTrace]
  refine ⟨225292057336954449771052319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150194704891302966514034879 225292057336954449771052319)
  ·
    refine ⟨337938086005431674656578479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225292057336954449771052319 337938086005431674656578479)
    ·
      refine ⟨506907129008147511984867719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337938086005431674656578479 506907129008147511984867719)
      ·
        refine ⟨760360693512221267977301579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506907129008147511984867719 760360693512221267977301579)
        ·
          refine ⟨1140541040268331901965952369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760360693512221267977301579 1140541040268331901965952369)
          ·
            refine ⟨855405780201248926474464277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140541040268331901965952369 855405780201248926474464277)
            ·
              refine ⟨40097145946933543428490513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 855405780201248926474464277 40097145946933543428490513)
              ·
                refine ⟨30072859460200157571367885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40097145946933543428490513 30072859460200157571367885)
                ·
                  refine ⟨11277322297575059089262957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30072859460200157571367885 11277322297575059089262957)
                  ·
                    refine ⟨4228995861590647158473609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11277322297575059089262957 4228995861590647158473609)
                    ·
                      refine ⟨3171746896192985368855207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4228995861590647158473609 3171746896192985368855207)
                      ·
                        rfl

theorem cell23_6176955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3, 2].length) (baseStart_6176955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176955 prefixEnd_6176955 := by exact prefixLift 6176955
  have htrace : WordTrace (prefixWord ++ tailWord_6176955) baseStart_6176955 baseEnd_6176955 := by
    simpa [prefixWord, tailWord_6176955, baseEnd_6176955] using wordTrace_append hprefix tailTrace_6176955
  have hstable : (prefixWord ++ tailWord_6176955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176955).length < 2 ^ (prefixWord ++ tailWord_6176955).sum := by decide
  have hdescent : baseEnd_6176955 < baseStart_6176955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176956 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_6176956 : Nat := 118140960795 + 6176956 * 2 ^ 59
def prefixEnd_6176956 : Nat := 4983230072969 + 3 ^ 40 * 6176956 * 2
def baseEnd_6176956 : Nat := 1057249136557879954980901

theorem tailTrace_6176956 : CollatzResearch.WordTrace tailWord_6176956 prefixEnd_6176956 1057249136557879954980901 := by
  unfold tailWord_6176956
  simp only [CollatzResearch.WordTrace]
  refine ⟨112646046904975413470919361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150194729206633884627892481 112646046904975413470919361)
  ·
    refine ⟨84484535178731560103189521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112646046904975413470919361 84484535178731560103189521)
    ·
      refine ⟨63363401384048670077392141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84484535178731560103189521 63363401384048670077392141)
      ·
        refine ⟨23761275519018251279022053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63363401384048670077392141 23761275519018251279022053)
        ·
          refine ⟨4455239159815922114816635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23761275519018251279022053 4455239159815922114816635)
          ·
            refine ⟨6682858739723883172224953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455239159815922114816635 6682858739723883172224953)
            ·
              refine ⟨5012144054792912379168715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682858739723883172224953 5012144054792912379168715)
              ·
                refine ⟨7518216082189368568753073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012144054792912379168715 7518216082189368568753073)
                ·
                  refine ⟨5638662061642026426564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518216082189368568753073 5638662061642026426564805)
                  ·
                    refine ⟨1057249136557879954980901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638662061642026426564805 1057249136557879954980901)
                    ·
                      rfl

theorem cell23_6176956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_6176956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176956 prefixEnd_6176956 := by exact prefixLift 6176956
  have htrace : WordTrace (prefixWord ++ tailWord_6176956) baseStart_6176956 baseEnd_6176956 := by
    simpa [prefixWord, tailWord_6176956, baseEnd_6176956] using wordTrace_append hprefix tailTrace_6176956
  have hstable : (prefixWord ++ tailWord_6176956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176956).length < 2 ^ (prefixWord ++ tailWord_6176956).sum := by decide
  have hdescent : baseEnd_6176956 < baseStart_6176956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6176985 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 4, 2]
def baseStart_6176985 : Nat := 118140960795 + 6176985 * 2 ^ 59
def prefixEnd_6176985 : Nat := 4983230072969 + 3 ^ 40 * 6176985 * 2
def baseEnd_6176985 : Nat := 3171762300612620251480069

theorem tailTrace_6176985 : CollatzResearch.WordTrace tailWord_6176985 prefixEnd_6176985 3171762300612620251480069 := by
  unfold tailWord_6176985
  simp only [CollatzResearch.WordTrace]
  refine ⟨225293151526845764894644409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150195434351230509929762939 225293151526845764894644409)
  ·
    refine ⟨168969863645134323670983307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225293151526845764894644409 168969863645134323670983307)
    ·
      refine ⟨253454795467701485506474961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168969863645134323670983307 253454795467701485506474961)
      ·
        refine ⟨190091096600776114129856221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253454795467701485506474961 190091096600776114129856221)
        ·
          refine ⟨71284161225291042798696083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190091096600776114129856221 71284161225291042798696083)
          ·
            refine ⟨106926241837936564198044125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71284161225291042798696083 106926241837936564198044125)
            ·
              refine ⟨40097340689226211574266547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106926241837936564198044125 40097340689226211574266547)
              ·
                refine ⟨60146011033839317361399821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40097340689226211574266547 60146011033839317361399821)
                ·
                  refine ⟨22554754137689744010524933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60146011033839317361399821 22554754137689744010524933)
                  ·
                    refine ⟨4229016400816827001973425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22554754137689744010524933 4229016400816827001973425)
                    ·
                      refine ⟨3171762300612620251480069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229016400816827001973425 3171762300612620251480069)
                      ·
                        rfl

theorem cell23_6176985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_6176985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6176985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6176985 prefixEnd_6176985 := by exact prefixLift 6176985
  have htrace : WordTrace (prefixWord ++ tailWord_6176985) baseStart_6176985 baseEnd_6176985 := by
    simpa [prefixWord, tailWord_6176985, baseEnd_6176985] using wordTrace_append hprefix tailTrace_6176985
  have hstable : (prefixWord ++ tailWord_6176985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6176985).length < 2 ^ (prefixWord ++ tailWord_6176985).sum := by decide
  have hdescent : baseEnd_6176985 < baseStart_6176985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6176985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177053 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6177053 : Nat := 118140960795 + 6177053 * 2 ^ 59
def prefixEnd_6177053 : Nat := 4983230072969 + 3 ^ 40 * 6177053 * 2
def baseEnd_6177053 : Nat := 3171797217297125985429757

theorem tailTrace_6177053 : CollatzResearch.WordTrace tailWord_6177053 prefixEnd_6177053 3171797217297125985429757 := by
  unfold tailWord_6177053
  simp only [CollatzResearch.WordTrace]
  refine ⟨225295631690599412508119813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150197087793732941672079875 225295631690599412508119813)
  ·
    refine ⟨42242930941987389845272465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225295631690599412508119813 42242930941987389845272465)
    ·
      refine ⟨31682198206490542383954349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42242930941987389845272465 31682198206490542383954349)
      ·
        refine ⟨11880824327433953393982881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31682198206490542383954349 11880824327433953393982881)
        ·
          refine ⟨8910618245575465045487161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11880824327433953393982881 8910618245575465045487161)
          ·
            refine ⟨6682963684181598784115371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910618245575465045487161 6682963684181598784115371)
            ·
              refine ⟨10024445526272398176173057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682963684181598784115371 10024445526272398176173057)
              ·
                refine ⟨7518334144704298632129793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10024445526272398176173057 7518334144704298632129793)
                ·
                  refine ⟨5638750608528223974097345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518334144704298632129793 5638750608528223974097345)
                  ·
                    refine ⟨4229062956396167980573009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638750608528223974097345 4229062956396167980573009)
                    ·
                      refine ⟨3171797217297125985429757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229062956396167980573009 3171797217297125985429757)
                      ·
                        rfl

theorem cell23_6177053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6177053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177053 prefixEnd_6177053 := by exact prefixLift 6177053
  have htrace : WordTrace (prefixWord ++ tailWord_6177053) baseStart_6177053 baseEnd_6177053 := by
    simpa [prefixWord, tailWord_6177053, baseEnd_6177053] using wordTrace_append hprefix tailTrace_6177053
  have hstable : (prefixWord ++ tailWord_6177053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177053).length < 2 ^ (prefixWord ++ tailWord_6177053).sum := by decide
  have hdescent : baseEnd_6177053 < baseStart_6177053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177070 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6177070 : Nat := 118140960795 + 6177070 * 2 ^ 59
def prefixEnd_6177070 : Nat := 4983230072969 + 3 ^ 40 * 6177070 * 2
def baseEnd_6177070 : Nat := 3171805946468252418917179

theorem tailTrace_6177070 : CollatzResearch.WordTrace tailWord_6177070 prefixEnd_6177070 3171805946468252418917179 := by
  unfold tailWord_6177070
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162031466442228051436083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150197501154358549607659109 28162031466442228051436083)
  ·
    refine ⟨42243047199663342077154125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162031466442228051436083 42243047199663342077154125)
    ·
      refine ⟨15841142699873753278932797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42243047199663342077154125 15841142699873753278932797)
      ·
        refine ⟨5940428512452657479599799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15841142699873753278932797 5940428512452657479599799)
        ·
          refine ⟨8910642768678986219399699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940428512452657479599799 8910642768678986219399699)
          ·
            refine ⟨13365964153018479329099549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910642768678986219399699 13365964153018479329099549)
            ·
              refine ⟨5012236557381929748412331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13365964153018479329099549 5012236557381929748412331)
              ·
                refine ⟨7518354836072894622618497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012236557381929748412331 7518354836072894622618497)
                ·
                  refine ⟨5638766127054670966963873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518354836072894622618497 5638766127054670966963873)
                  ·
                    refine ⟨4229074595291003225222905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638766127054670966963873 4229074595291003225222905)
                    ·
                      refine ⟨3171805946468252418917179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229074595291003225222905 3171805946468252418917179)
                      ·
                        rfl

theorem cell23_6177070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6177070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177070 prefixEnd_6177070 := by exact prefixLift 6177070
  have htrace : WordTrace (prefixWord ++ tailWord_6177070) baseStart_6177070 baseEnd_6177070 := by
    simpa [prefixWord, tailWord_6177070, baseEnd_6177070] using wordTrace_append hprefix tailTrace_6177070
  have hstable : (prefixWord ++ tailWord_6177070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177070).length < 2 ^ (prefixWord ++ tailWord_6177070).sum := by decide
  have hdescent : baseEnd_6177070 < baseStart_6177070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177088 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_6177088 : Nat := 118140960795 + 6177088 * 2 ^ 59
def prefixEnd_6177088 : Nat := 4983230072969 + 3 ^ 40 * 6177088 * 2
def baseEnd_6177088 : Nat := 3171815189120033348492095

theorem tailTrace_6177088 : CollatzResearch.WordTrace tailWord_6177088 prefixEnd_6177088 3171815189120033348492095 := by
  unfold tailWord_6177088
  simp only [CollatzResearch.WordTrace]
  refine ⟨112648454122736306742821959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150197938830315075657095945 112648454122736306742821959)
  ·
    refine ⟨168972681184104460114232939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112648454122736306742821959 168972681184104460114232939)
    ·
      refine ⟨253459021776156690171349409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168972681184104460114232939 253459021776156690171349409)
      ·
        refine ⟨190094266332117517628512057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253459021776156690171349409 190094266332117517628512057)
        ·
          refine ⟨142570699749088138221384043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190094266332117517628512057 142570699749088138221384043)
          ·
            refine ⟨213856049623632207332076065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142570699749088138221384043 213856049623632207332076065)
            ·
              refine ⟨160392037217724155499057049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213856049623632207332076065 160392037217724155499057049)
              ·
                refine ⟨120294027913293116624292787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160392037217724155499057049 120294027913293116624292787)
                ·
                  refine ⟨180441041869939674936439181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120294027913293116624292787 180441041869939674936439181)
                  ·
                    refine ⟨67665390701227378101164693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180441041869939674936439181 67665390701227378101164693)
                    ·
                      refine ⟨3171815189120033348492095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67665390701227378101164693 3171815189120033348492095)
                      ·
                        rfl

theorem cell23_6177088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_6177088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177088 prefixEnd_6177088 := by exact prefixLift 6177088
  have htrace : WordTrace (prefixWord ++ tailWord_6177088) baseStart_6177088 baseEnd_6177088 := by
    simpa [prefixWord, tailWord_6177088, baseEnd_6177088] using wordTrace_append hprefix tailTrace_6177088
  have hstable : (prefixWord ++ tailWord_6177088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177088).length < 2 ^ (prefixWord ++ tailWord_6177088).sum := by decide
  have hdescent : baseEnd_6177088 < baseStart_6177088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177095 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_6177095 : Nat := 118140960795 + 6177095 * 2 ^ 59
def prefixEnd_6177095 : Nat := 4983230072969 + 3 ^ 40 * 6177095 * 2
def baseEnd_6177095 : Nat := 3171818783484614821104563

theorem tailTrace_6177095 : CollatzResearch.WordTrace tailWord_6177095 prefixEnd_6177095 3171818783484614821104563 := by
  unfold tailWord_6177095
  simp only [CollatzResearch.WordTrace]
  refine ⟨225297163556447253681148739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150198109037631502454099159 225297163556447253681148739)
  ·
    refine ⟨337945745334670880521723109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225297163556447253681148739 337945745334670880521723109)
    ·
      refine ⟨63364827250250790097823083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337945745334670880521723109 63364827250250790097823083)
      ·
        refine ⟨95047240875376185146734625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63364827250250790097823083 95047240875376185146734625)
        ·
          refine ⟨71285430656532138860050969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95047240875376185146734625 71285430656532138860050969)
          ·
            refine ⟨53464072992399104145038227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71285430656532138860050969 53464072992399104145038227)
            ·
              refine ⟨80196109488598656217557341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53464072992399104145038227 80196109488598656217557341)
              ·
                refine ⟨30073541058224496081584003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80196109488598656217557341 30073541058224496081584003)
                ·
                  refine ⟨45110311587336744122376005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30073541058224496081584003 45110311587336744122376005)
                  ·
                    refine ⟨8458183422625639522945501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45110311587336744122376005 8458183422625639522945501)
                    ·
                      refine ⟨3171818783484614821104563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458183422625639522945501 3171818783484614821104563)
                      ·
                        rfl

theorem cell23_6177095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_6177095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177095 prefixEnd_6177095 := by exact prefixLift 6177095
  have htrace : WordTrace (prefixWord ++ tailWord_6177095) baseStart_6177095 baseEnd_6177095 := by
    simpa [prefixWord, tailWord_6177095, baseEnd_6177095] using wordTrace_append hprefix tailTrace_6177095
  have hstable : (prefixWord ++ tailWord_6177095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177095).length < 2 ^ (prefixWord ++ tailWord_6177095).sum := by decide
  have hdescent : baseEnd_6177095 < baseStart_6177095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177132 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 6]
def baseStart_6177132 : Nat := 118140960795 + 6177132 * 2 ^ 59
def prefixEnd_6177132 : Nat := 4983230072969 + 3 ^ 40 * 6177132 * 2
def baseEnd_6177132 : Nat := 352426420252092352926877

theorem tailTrace_6177132 : CollatzResearch.WordTrace tailWord_6177132 prefixEnd_6177132 352426420252092352926877 := by
  unfold tailWord_6177132
  simp only [CollatzResearch.WordTrace]
  refine ⟨112649256528656604500122825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150199008704875472666830433 112649256528656604500122825)
  ·
    refine ⟨84486942396492453375092119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112649256528656604500122825 84486942396492453375092119)
    ·
      refine ⟨126730413594738680062638179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84486942396492453375092119 126730413594738680062638179)
      ·
        refine ⟨190095620392108020093957269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126730413594738680062638179 190095620392108020093957269)
        ·
          refine ⟨8910732205880063441904247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190095620392108020093957269 8910732205880063441904247)
          ·
            refine ⟨13366098308820095162856371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910732205880063441904247 13366098308820095162856371)
            ·
              refine ⟨20049147463230142744284557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13366098308820095162856371 20049147463230142744284557)
              ·
                refine ⟨7518430298711303529106709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20049147463230142744284557 7518430298711303529106709)
                ·
                  refine ⟨352426420252092352926877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7518430298711303529106709 352426420252092352926877)
                  ·
                    rfl

theorem cell23_6177132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_6177132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177132 prefixEnd_6177132 := by exact prefixLift 6177132
  have htrace : WordTrace (prefixWord ++ tailWord_6177132) baseStart_6177132 baseEnd_6177132 := by
    simpa [prefixWord, tailWord_6177132, baseEnd_6177132] using wordTrace_append hprefix tailTrace_6177132
  have hstable : (prefixWord ++ tailWord_6177132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177132).length < 2 ^ (prefixWord ++ tailWord_6177132).sum := by decide
  have hdescent : baseEnd_6177132 < baseStart_6177132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177202 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_6177202 : Nat := 118140960795 + 6177202 * 2 ^ 59
def prefixEnd_6177202 : Nat := 4983230072969 + 3 ^ 40 * 6177202 * 2
def baseEnd_6177202 : Nat := 3171873725914645902466571

theorem tailTrace_6177202 : CollatzResearch.WordTrace tailWord_6177202 prefixEnd_6177202 3171873725914645902466571 := by
  unfold tailWord_6177202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56325266541764902738823465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150200710778039740636862573 56325266541764902738823465)
  ·
    refine ⟨42243949906323677054117599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56325266541764902738823465 42243949906323677054117599)
    ·
      refine ⟨63365924859485515581176399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42243949906323677054117599 63365924859485515581176399)
      ·
        refine ⟨95048887289228273371764599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63365924859485515581176399 95048887289228273371764599)
        ·
          refine ⟨142573330933842410057646899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95048887289228273371764599 142573330933842410057646899)
          ·
            refine ⟨213859996400763615086470349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142573330933842410057646899 213859996400763615086470349)
            ·
              refine ⟨80197498650286355657426381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213859996400763615086470349 80197498650286355657426381)
              ·
                refine ⟨30074061993857383371534893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80197498650286355657426381 30074061993857383371534893)
                ·
                  refine ⟨11277773247696518764325585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30074061993857383371534893 11277773247696518764325585)
                  ·
                    refine ⟨8458329935772389073244189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11277773247696518764325585 8458329935772389073244189)
                    ·
                      refine ⟨3171873725914645902466571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458329935772389073244189 3171873725914645902466571)
                      ·
                        rfl

theorem cell23_6177202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_6177202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177202 prefixEnd_6177202 := by exact prefixLift 6177202
  have htrace : WordTrace (prefixWord ++ tailWord_6177202) baseStart_6177202 baseEnd_6177202 := by
    simpa [prefixWord, tailWord_6177202, baseEnd_6177202] using wordTrace_append hprefix tailTrace_6177202
  have hstable : (prefixWord ++ tailWord_6177202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177202).length < 2 ^ (prefixWord ++ tailWord_6177202).sum := by decide
  have hdescent : baseEnd_6177202 < baseStart_6177202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177262 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_6177262 : Nat := 118140960795 + 6177262 * 2 ^ 59
def prefixEnd_6177262 : Nat := 4983230072969 + 3 ^ 40 * 6177262 * 2
def baseEnd_6177262 : Nat := 3171904534753915667716295

theorem tailTrace_6177262 : CollatzResearch.WordTrace tailWord_6177262 prefixEnd_6177262 3171904534753915667716295 := by
  unfold tailWord_6177262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162906818355280150309755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150202169697894827468318693 28162906818355280150309755)
  ·
    refine ⟨42244360227532920225464633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162906818355280150309755 42244360227532920225464633)
    ·
      refine ⟨31683270170649690169098475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42244360227532920225464633 31683270170649690169098475)
      ·
        refine ⟨47524905255974535253647713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31683270170649690169098475 47524905255974535253647713)
        ·
          refine ⟨35643678941980901440235785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47524905255974535253647713 35643678941980901440235785)
          ·
            refine ⟨26732759206485676080176839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35643678941980901440235785 26732759206485676080176839)
            ·
              refine ⟨40099138809728514120265259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26732759206485676080176839 40099138809728514120265259)
              ·
                refine ⟨60148708214592771180397889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40099138809728514120265259 60148708214592771180397889)
                ·
                  refine ⟨45111531160944578385298417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60148708214592771180397889 45111531160944578385298417)
                  ·
                    refine ⟨33833648370708433788973813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45111531160944578385298417 33833648370708433788973813)
                    ·
                      refine ⟨3171904534753915667716295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33833648370708433788973813 3171904534753915667716295)
                      ·
                        rfl

theorem cell23_6177262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_6177262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177262 prefixEnd_6177262 := by exact prefixLift 6177262
  have htrace : WordTrace (prefixWord ++ tailWord_6177262) baseStart_6177262 baseEnd_6177262 := by
    simpa [prefixWord, tailWord_6177262, baseEnd_6177262] using wordTrace_append hprefix tailTrace_6177262
  have hstable : (prefixWord ++ tailWord_6177262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177262).length < 2 ^ (prefixWord ++ tailWord_6177262).sum := by decide
  have hdescent : baseEnd_6177262 < baseStart_6177262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177300 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6177300 : Nat := 118140960795 + 6177300 * 2 ^ 59
def prefixEnd_6177300 : Nat := 4983230072969 + 3 ^ 40 * 6177300 * 2
def baseEnd_6177300 : Nat := 3171924047018786519041121

theorem tailTrace_6177300 : CollatzResearch.WordTrace tailWord_6177300 prefixEnd_6177300 3171924047018786519041121 := by
  unfold tailWord_6177300
  simp only [CollatzResearch.WordTrace]
  refine ⟨112652320260352286846180677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150203093680469715794907569 112652320260352286846180677)
  ·
    refine ⟨21122310048816053783658877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112652320260352286846180677 21122310048816053783658877)
    ·
      refine ⟨7920866268306020168872079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21122310048816053783658877 7920866268306020168872079)
      ·
        refine ⟨11881299402459030253308119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7920866268306020168872079 11881299402459030253308119)
        ·
          refine ⟨17821949103688545379962179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11881299402459030253308119 17821949103688545379962179)
          ·
            refine ⟨26732923655532818069943269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17821949103688545379962179 26732923655532818069943269)
            ·
              refine ⟨5012423185412403388114363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26732923655532818069943269 5012423185412403388114363)
              ·
                refine ⟨7518634778118605082171545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012423185412403388114363 7518634778118605082171545)
                ·
                  refine ⟨5638976083588953811628659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518634778118605082171545 5638976083588953811628659)
                  ·
                    refine ⟨8458464125383430717442989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5638976083588953811628659 8458464125383430717442989)
                    ·
                      refine ⟨3171924047018786519041121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458464125383430717442989 3171924047018786519041121)
                      ·
                        rfl

theorem cell23_6177300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6177300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177300 prefixEnd_6177300 := by exact prefixLift 6177300
  have htrace : WordTrace (prefixWord ++ tailWord_6177300) baseStart_6177300 baseEnd_6177300 := by
    simpa [prefixWord, tailWord_6177300, baseEnd_6177300] using wordTrace_append hprefix tailTrace_6177300
  have hstable : (prefixWord ++ tailWord_6177300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177300).length < 2 ^ (prefixWord ++ tailWord_6177300).sum := by decide
  have hdescent : baseEnd_6177300 < baseStart_6177300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6177305 : Nat := 118140960795 + 6177305 * 2 ^ 59
def prefixEnd_6177305 : Nat := 4983230072969 + 3 ^ 40 * 6177305 * 2
def baseEnd_6177305 : Nat := 3171926614422058999478597

theorem tailTrace_6177305 : CollatzResearch.WordTrace tailWord_6177305 prefixEnd_6177305 3171926614422058999478597 := by
  unfold tailWord_6177305
  simp only [CollatzResearch.WordTrace]
  refine ⟨225304822885686459546293369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150203215257124306364195579 225304822885686459546293369)
  ·
    refine ⟨168978617164264844659720027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225304822885686459546293369 168978617164264844659720027)
    ·
      refine ⟨253467925746397266989580041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168978617164264844659720027 253467925746397266989580041)
      ·
        refine ⟨190100944309797950242185031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253467925746397266989580041 190100944309797950242185031)
        ·
          refine ⟨285151416464696925363277547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190100944309797950242185031 285151416464696925363277547)
          ·
            refine ⟨427727124697045388044916321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285151416464696925363277547 427727124697045388044916321)
            ·
              refine ⟨320795343522784041033687241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427727124697045388044916321 320795343522784041033687241)
              ·
                refine ⟨240596507642088030775265431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320795343522784041033687241 240596507642088030775265431)
                ·
                  refine ⟨360894761463132046162898147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240596507642088030775265431 360894761463132046162898147)
                  ·
                    refine ⟨541342142194698069244347221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 360894761463132046162898147 541342142194698069244347221)
                    ·
                      refine ⟨3171926614422058999478597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 541342142194698069244347221 3171926614422058999478597)
                      ·
                        rfl

theorem cell23_6177305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6177305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177305 prefixEnd_6177305 := by exact prefixLift 6177305
  have htrace : WordTrace (prefixWord ++ tailWord_6177305) baseStart_6177305 baseEnd_6177305 := by
    simpa [prefixWord, tailWord_6177305, baseEnd_6177305] using wordTrace_append hprefix tailTrace_6177305
  have hstable : (prefixWord ++ tailWord_6177305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177305).length < 2 ^ (prefixWord ++ tailWord_6177305).sum := by decide
  have hdescent : baseEnd_6177305 < baseStart_6177305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177349 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_6177349 : Nat := 118140960795 + 6177349 * 2 ^ 59
def prefixEnd_6177349 : Nat := 4983230072969 + 3 ^ 40 * 6177349 * 2
def baseEnd_6177349 : Nat := 3171949207570856827328395

theorem tailTrace_6177349 : CollatzResearch.WordTrace tailWord_6177349 prefixEnd_6177349 3171949207570856827328395 := by
  unfold tailWord_6177349
  simp only [CollatzResearch.WordTrace]
  refine ⟨225306427697527055060895101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150204285131684703373930067 225306427697527055060895101)
  ·
    refine ⟨84489910386572645647835663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225306427697527055060895101 84489910386572645647835663)
    ·
      refine ⟨126734865579858968471753495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84489910386572645647835663 126734865579858968471753495)
      ·
        refine ⟨190102298369788452707630243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126734865579858968471753495 190102298369788452707630243)
        ·
          refine ⟨285153447554682679061445365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190102298369788452707630243 285153447554682679061445365)
          ·
            refine ⟨26733135708251501162010503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285153447554682679061445365 26733135708251501162010503)
            ·
              refine ⟨40099703562377251743015755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26733135708251501162010503 40099703562377251743015755)
              ·
                refine ⟨60149555343565877614523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40099703562377251743015755 60149555343565877614523633)
                ·
                  refine ⟨45112166507674408210892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60149555343565877614523633 45112166507674408210892725)
                  ·
                    refine ⟨4229265610094475769771193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45112166507674408210892725 4229265610094475769771193)
                    ·
                      refine ⟨3171949207570856827328395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229265610094475769771193 3171949207570856827328395)
                      ·
                        rfl

theorem cell23_6177349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_6177349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177349 prefixEnd_6177349 := by exact prefixLift 6177349
  have htrace : WordTrace (prefixWord ++ tailWord_6177349) baseStart_6177349 baseEnd_6177349 := by
    simpa [prefixWord, tailWord_6177349, baseEnd_6177349] using wordTrace_append hprefix tailTrace_6177349
  have hstable : (prefixWord ++ tailWord_6177349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177349).length < 2 ^ (prefixWord ++ tailWord_6177349).sum := by decide
  have hdescent : baseEnd_6177349 < baseStart_6177349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177379 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 6, 2]
def baseStart_6177379 : Nat := 118140960795 + 6177379 * 2 ^ 59
def prefixEnd_6177379 : Nat := 4983230072969 + 3 ^ 40 * 6177379 * 2
def baseEnd_6177379 : Nat := 3171964611990491709953257

theorem tailTrace_6177379 : CollatzResearch.WordTrace tailWord_6177379 prefixEnd_6177379 3171964611990491709953257 := by
  unfold tailWord_6177379
  simp only [CollatzResearch.WordTrace]
  refine ⟨225307521887418370184487191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150205014591612246789658127 225307521887418370184487191)
  ·
    refine ⟨337961282831127555276730787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225307521887418370184487191 337961282831127555276730787)
    ·
      refine ⟨506941924246691332915096181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337961282831127555276730787 506941924246691332915096181)
      ·
        refine ⟨47525805398127312460790267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 506941924246691332915096181 47525805398127312460790267)
        ·
          refine ⟨71288708097190968691185401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47525805398127312460790267 71288708097190968691185401)
          ·
            refine ⟨53466531072893226518389051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71288708097190968691185401 53466531072893226518389051)
            ·
              refine ⟨80199796609339839777583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53466531072893226518389051 80199796609339839777583577)
              ·
                refine ⟨60149847457004879833187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80199796609339839777583577 60149847457004879833187683)
                ·
                  refine ⟨90224771185507319749781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60149847457004879833187683 90224771185507319749781525)
                  ·
                    refine ⟨4229286149320655613271009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90224771185507319749781525 4229286149320655613271009)
                    ·
                      refine ⟨3171964611990491709953257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229286149320655613271009 3171964611990491709953257)
                      ·
                        rfl

theorem cell23_6177379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_6177379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177379 prefixEnd_6177379 := by exact prefixLift 6177379
  have htrace : WordTrace (prefixWord ++ tailWord_6177379) baseStart_6177379 baseEnd_6177379 := by
    simpa [prefixWord, tailWord_6177379, baseEnd_6177379] using wordTrace_append hprefix tailTrace_6177379
  have hstable : (prefixWord ++ tailWord_6177379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177379).length < 2 ^ (prefixWord ++ tailWord_6177379).sum := by decide
  have hdescent : baseEnd_6177379 < baseStart_6177379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177399 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_6177399 : Nat := 118140960795 + 6177399 * 2 ^ 59
def prefixEnd_6177399 : Nat := 4983230072969 + 3 ^ 40 * 6177399 * 2
def baseEnd_6177399 : Nat := 3171974881603581631703165

theorem tailTrace_6177399 : CollatzResearch.WordTrace tailWord_6177399 prefixEnd_6177399 3171974881603581631703165 := by
  unfold tailWord_6177399
  simp only [CollatzResearch.WordTrace]
  refine ⟨225308251347345913600215251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150205500898230609066810167 225308251347345913600215251)
  ·
    refine ⟨337962377021018870400322877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225308251347345913600215251 337962377021018870400322877)
    ·
      refine ⟨126735891382882076400121079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337962377021018870400322877 126735891382882076400121079)
      ·
        refine ⟨190103837074323114600181619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126735891382882076400121079 190103837074323114600181619)
        ·
          refine ⟨285155755611484671900272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190103837074323114600181619 285155755611484671900272429)
          ·
            refine ⟨106933408354306751962602161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285155755611484671900272429 106933408354306751962602161)
            ·
              refine ⟨80200056265730063971951621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106933408354306751962602161 80200056265730063971951621)
              ·
                refine ⟨15037510549824386994740929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80200056265730063971951621 15037510549824386994740929)
                ·
                  refine ⟨11278132912368290246055697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15037510549824386994740929 11278132912368290246055697)
                  ·
                    refine ⟨8458599684276217684541773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11278132912368290246055697 8458599684276217684541773)
                    ·
                      refine ⟨3171974881603581631703165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458599684276217684541773 3171974881603581631703165)
                      ·
                        rfl

theorem cell23_6177399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_6177399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177399 prefixEnd_6177399 := by exact prefixLift 6177399
  have htrace : WordTrace (prefixWord ++ tailWord_6177399) baseStart_6177399 baseEnd_6177399 := by
    simpa [prefixWord, tailWord_6177399, baseEnd_6177399] using wordTrace_append hprefix tailTrace_6177399
  have hstable : (prefixWord ++ tailWord_6177399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177399).length < 2 ^ (prefixWord ++ tailWord_6177399).sum := by decide
  have hdescent : baseEnd_6177399 < baseStart_6177399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177440 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 1, 4]
def baseStart_6177440 : Nat := 118140960795 + 6177440 * 2 ^ 59
def prefixEnd_6177440 : Nat := 4983230072969 + 3 ^ 40 * 6177440 * 2
def baseEnd_6177440 : Nat := 1057331978103471990430159

theorem tailTrace_6177440 : CollatzResearch.WordTrace tailWord_6177440 prefixEnd_6177440 1057331978103471990430159 := by
  unfold tailWord_6177440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112654873370098688801228887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150206497826798251734971849 112654873370098688801228887)
  ·
    refine ⟨168982310055148033201843331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112654873370098688801228887 168982310055148033201843331)
    ·
      refine ⟨253473465082722049802764997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168982310055148033201843331 253473465082722049802764997)
      ·
        refine ⟨47526274703010384338018437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253473465082722049802764997 47526274703010384338018437)
        ·
          refine ⟨8911176506814447063378457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47526274703010384338018437 8911176506814447063378457)
          ·
            refine ⟨6683382380110835297533843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8911176506814447063378457 6683382380110835297533843)
            ·
              refine ⟨10025073570166252946300765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683382380110835297533843 10025073570166252946300765)
              ·
                refine ⟨3759402588812344854862787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10025073570166252946300765 3759402588812344854862787)
                ·
                  refine ⟨5639103883218517282294181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759402588812344854862787 5639103883218517282294181)
                  ·
                    refine ⟨1057331978103471990430159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639103883218517282294181 1057331978103471990430159)
                    ·
                      rfl

theorem cell23_6177440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_6177440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177440 prefixEnd_6177440 := by exact prefixLift 6177440
  have htrace : WordTrace (prefixWord ++ tailWord_6177440) baseStart_6177440 baseEnd_6177440 := by
    simpa [prefixWord, tailWord_6177440, baseEnd_6177440] using wordTrace_append hprefix tailTrace_6177440
  have hstable : (prefixWord ++ tailWord_6177440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177440).length < 2 ^ (prefixWord ++ tailWord_6177440).sum := by decide
  have hdescent : baseEnd_6177440 < baseStart_6177440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177450 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6177450 : Nat := 118140960795 + 6177450 * 2 ^ 59
def prefixEnd_6177450 : Nat := 4983230072969 + 3 ^ 40 * 6177450 * 2
def baseEnd_6177450 : Nat := 3172001069116960932165431

theorem tailTrace_6177450 : CollatzResearch.WordTrace tailWord_6177450 prefixEnd_6177450 3172001069116960932165431 := by
  unfold tailWord_6177450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327527867540287327580451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150206740980107432873547869 56327527867540287327580451)
  ·
    refine ⟨84491291801310430991370677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56327527867540287327580451 84491291801310430991370677)
    ·
      refine ⟨7921058606372852905441001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84491291801310430991370677 7921058606372852905441001)
      ·
        refine ⟨5940793954779639679080751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7921058606372852905441001 5940793954779639679080751)
        ·
          refine ⟨8911190932169459518621127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940793954779639679080751 8911190932169459518621127)
          ·
            refine ⟨13366786398254189277931691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911190932169459518621127 13366786398254189277931691)
            ·
              refine ⟨20050179597381283916897537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13366786398254189277931691 20050179597381283916897537)
              ·
                refine ⟨15037634698035962937673153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20050179597381283916897537 15037634698035962937673153)
                ·
                  refine ⟨11278226023526972203254865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15037634698035962937673153 11278226023526972203254865)
                  ·
                    refine ⟨8458669517645229152441149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11278226023526972203254865 8458669517645229152441149)
                    ·
                      refine ⟨3172001069116960932165431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458669517645229152441149 3172001069116960932165431)
                      ·
                        rfl

theorem cell23_6177450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6177450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177450 prefixEnd_6177450 := by exact prefixLift 6177450
  have htrace : WordTrace (prefixWord ++ tailWord_6177450) baseStart_6177450 baseEnd_6177450 := by
    simpa [prefixWord, tailWord_6177450, baseEnd_6177450] using wordTrace_append hprefix tailTrace_6177450
  have hstable : (prefixWord ++ tailWord_6177450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177450).length < 2 ^ (prefixWord ++ tailWord_6177450).sum := by decide
  have hdescent : baseEnd_6177450 < baseStart_6177450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177457 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 1, 4]
def baseStart_6177457 : Nat := 118140960795 + 6177457 * 2 ^ 59
def prefixEnd_6177457 : Nat := 4983230072969 + 3 ^ 40 * 6177457 * 2
def baseEnd_6177457 : Nat := 1057334887827180801592633

theorem tailTrace_6177457 : CollatzResearch.WordTrace tailWord_6177457 prefixEnd_6177457 1057334887827180801592633 := by
  unfold tailWord_6177457
  simp only [CollatzResearch.WordTrace]
  refine ⟨225310366781135789505826625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150206911187423859670551083 225310366781135789505826625)
  ·
    refine ⟨168982775085851842129369969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225310366781135789505826625 168982775085851842129369969)
    ·
      refine ⟨126737081314388881597027477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168982775085851842129369969 126737081314388881597027477)
      ·
        refine ⟨5940800686611978824860663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126737081314388881597027477 5940800686611978824860663)
        ·
          refine ⟨8911201029917968237290995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940800686611978824860663 8911201029917968237290995)
          ·
            refine ⟨13366801544876952355936493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911201029917968237290995 13366801544876952355936493)
            ·
              refine ⟨5012550579328857133476185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13366801544876952355936493 5012550579328857133476185)
              ·
                refine ⟨3759412934496642850107139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012550579328857133476185 3759412934496642850107139)
                ·
                  refine ⟨5639119401744964275160709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759412934496642850107139 5639119401744964275160709)
                  ·
                    refine ⟨1057334887827180801592633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639119401744964275160709 1057334887827180801592633)
                    ·
                      rfl

theorem cell23_6177457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_6177457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177457 prefixEnd_6177457 := by exact prefixLift 6177457
  have htrace : WordTrace (prefixWord ++ tailWord_6177457) baseStart_6177457 baseEnd_6177457 := by
    simpa [prefixWord, tailWord_6177457, baseEnd_6177457] using wordTrace_append hprefix tailTrace_6177457
  have hstable : (prefixWord ++ tailWord_6177457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177457).length < 2 ^ (prefixWord ++ tailWord_6177457).sum := by decide
  have hdescent : baseEnd_6177457 < baseStart_6177457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177479 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 6, 4]
def baseStart_6177479 : Nat := 118140960795 + 6177479 * 2 ^ 59
def prefixEnd_6177479 : Nat := 4983230072969 + 3 ^ 40 * 6177479 * 2
def baseEnd_6177479 : Nat := 1057338653351980439567599

theorem tailTrace_6177479 : CollatzResearch.WordTrace tailWord_6177479 prefixEnd_6177479 1057338653351980439567599 := by
  unfold tailWord_6177479
  simp only [CollatzResearch.WordTrace]
  refine ⟨225311169187056087263127491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150207446124704058175418327 225311169187056087263127491)
  ·
    refine ⟨337966753780584130894691237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225311169187056087263127491 337966753780584130894691237)
    ·
      refine ⟨63368766333859524542754607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337966753780584130894691237 63368766333859524542754607)
      ·
        refine ⟨95053149500789286814131911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63368766333859524542754607 95053149500789286814131911)
        ·
          refine ⟨142579724251183930221197867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95053149500789286814131911 142579724251183930221197867)
          ·
            refine ⟨213869586376775895331796801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142579724251183930221197867 213869586376775895331796801)
            ·
              refine ⟨160402189782581921498847601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213869586376775895331796801 160402189782581921498847601)
              ·
                refine ⟨120301642336936441124135701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160402189782581921498847601 120301642336936441124135701)
                ·
                  refine ⟨5639139484543895677693861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120301642336936441124135701 5639139484543895677693861)
                  ·
                    refine ⟨1057338653351980439567599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639139484543895677693861 1057338653351980439567599)
                    ·
                      rfl

theorem cell23_6177479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_6177479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177479 prefixEnd_6177479 := by exact prefixLift 6177479
  have htrace : WordTrace (prefixWord ++ tailWord_6177479) baseStart_6177479 baseEnd_6177479 := by
    simpa [prefixWord, tailWord_6177479, baseEnd_6177479] using wordTrace_append hprefix tailTrace_6177479
  have hstable : (prefixWord ++ tailWord_6177479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177479).length < 2 ^ (prefixWord ++ tailWord_6177479).sum := by decide
  have hdescent : baseEnd_6177479 < baseStart_6177479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177486 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6177486 : Nat := 118140960795 + 6177486 * 2 ^ 59
def prefixEnd_6177486 : Nat := 4983230072969 + 3 ^ 40 * 6177486 * 2
def baseEnd_6177486 : Nat := 3172019554420522791315265

theorem tailTrace_6177486 : CollatzResearch.WordTrace tailWord_6177486 prefixEnd_6177486 3172019554420522791315265 := by
  unfold tailWord_6177486
  simp only [CollatzResearch.WordTrace]
  refine ⟨28163928062253840932329039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150207616332020484972421541 28163928062253840932329039)
  ·
    refine ⟨42245892093380761398493559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28163928062253840932329039 42245892093380761398493559)
    ·
      refine ⟨63368838140071142097740339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42245892093380761398493559 63368838140071142097740339)
      ·
        refine ⟨95053257210106713146610509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63368838140071142097740339 95053257210106713146610509)
        ·
          refine ⟨35644971453790017429978941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95053257210106713146610509 35644971453790017429978941)
          ·
            refine ⟨13366864295171256536242103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35644971453790017429978941 13366864295171256536242103)
            ·
              refine ⟨20050296442756884804363155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13366864295171256536242103 20050296442756884804363155)
              ·
                refine ⟨30075444664135327206544733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20050296442756884804363155 30075444664135327206544733)
                ·
                  refine ⟨11278291749050747702454275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30075444664135327206544733 11278291749050747702454275)
                  ·
                    refine ⟨16917437623576121553681413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11278291749050747702454275 16917437623576121553681413)
                    ·
                      refine ⟨3172019554420522791315265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16917437623576121553681413 3172019554420522791315265)
                      ·
                        rfl

theorem cell23_6177486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6177486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177486 prefixEnd_6177486 := by exact prefixLift 6177486
  have htrace : WordTrace (prefixWord ++ tailWord_6177486) baseStart_6177486 baseEnd_6177486 := by
    simpa [prefixWord, tailWord_6177486, baseEnd_6177486] using wordTrace_append hprefix tailTrace_6177486
  have hstable : (prefixWord ++ tailWord_6177486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177486).length < 2 ^ (prefixWord ++ tailWord_6177486).sum := by decide
  have hdescent : baseEnd_6177486 < baseStart_6177486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177490 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6177490 : Nat := 118140960795 + 6177490 * 2 ^ 59
def prefixEnd_6177490 : Nat := 4983230072969 + 3 ^ 40 * 6177490 * 2
def baseEnd_6177490 : Nat := 3172021608343140775665247

theorem tailTrace_6177490 : CollatzResearch.WordTrace tailWord_6177490 prefixEnd_6177490 3172021608343140775665247 := by
  unfold tailWord_6177490
  simp only [CollatzResearch.WordTrace]
  refine ⟨56327892597504059035444481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150207713593344157427851949 56327892597504059035444481)
  ·
    refine ⟨42245919448128044276583361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56327892597504059035444481 42245919448128044276583361)
    ·
      refine ⟨31684439586096033207437521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42245919448128044276583361 31684439586096033207437521)
      ·
        refine ⟨23763329689572024905578141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31684439586096033207437521 23763329689572024905578141)
        ·
          refine ⟨8911248633589509339591803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23763329689572024905578141 8911248633589509339591803)
          ·
            refine ⟨13366872950384264009387705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911248633589509339591803 13366872950384264009387705)
            ·
              refine ⟨10025154712788198007040779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13366872950384264009387705 10025154712788198007040779)
              ·
                refine ⟨15037732069182297010561169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10025154712788198007040779 15037732069182297010561169)
                ·
                  refine ⟨11278299051886722757920877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15037732069182297010561169 11278299051886722757920877)
                  ·
                    refine ⟨4229362144457521034220329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11278299051886722757920877 4229362144457521034220329)
                    ·
                      refine ⟨3172021608343140775665247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229362144457521034220329 3172021608343140775665247)
                      ·
                        rfl

theorem cell23_6177490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6177490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177490 prefixEnd_6177490 := by exact prefixLift 6177490
  have htrace : WordTrace (prefixWord ++ tailWord_6177490) baseStart_6177490 baseEnd_6177490 := by
    simpa [prefixWord, tailWord_6177490, baseEnd_6177490] using wordTrace_append hprefix tailTrace_6177490
  have hstable : (prefixWord ++ tailWord_6177490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177490).length < 2 ^ (prefixWord ++ tailWord_6177490).sum := by decide
  have hdescent : baseEnd_6177490 < baseStart_6177490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177500 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6177500 : Nat := 118140960795 + 6177500 * 2 ^ 59
def prefixEnd_6177500 : Nat := 4983230072969 + 3 ^ 40 * 6177500 * 2
def baseEnd_6177500 : Nat := 1057342247716561912180067

theorem tailTrace_6177500 : CollatzResearch.WordTrace tailWord_6177500 prefixEnd_6177500 1057342247716561912180067 := by
  unfold tailWord_6177500
  simp only [CollatzResearch.WordTrace]
  refine ⟨112655967559990003924820977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150207956746653338566427969 112655967559990003924820977)
  ·
    refine ⟨84491975669992502943615733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112655967559990003924820977 84491975669992502943615733)
    ·
      refine ⟨7921122719061797150963975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84491975669992502943615733 7921122719061797150963975)
      ·
        refine ⟨11881684078592695726445963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921122719061797150963975 11881684078592695726445963)
        ·
          refine ⟨17822526117889043589668945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11881684078592695726445963 17822526117889043589668945)
          ·
            refine ⟨13366894588416782692251709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17822526117889043589668945 13366894588416782692251709)
            ·
              refine ⟨5012585470656293509594391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13366894588416782692251709 5012585470656293509594391)
              ·
                refine ⟨7518878205984440264391587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012585470656293509594391 7518878205984440264391587)
                ·
                  refine ⟨11278317308976660396587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518878205984440264391587 11278317308976660396587381)
                  ·
                    refine ⟨1057342247716561912180067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11278317308976660396587381 1057342247716561912180067)
                    ·
                      rfl

theorem cell23_6177500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6177500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177500 prefixEnd_6177500 := by exact prefixLift 6177500
  have htrace : WordTrace (prefixWord ++ tailWord_6177500) baseStart_6177500 baseEnd_6177500 := by
    simpa [prefixWord, tailWord_6177500, baseEnd_6177500] using wordTrace_append hprefix tailTrace_6177500
  have hstable : (prefixWord ++ tailWord_6177500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177500).length < 2 ^ (prefixWord ++ tailWord_6177500).sum := by decide
  have hdescent : baseEnd_6177500 < baseStart_6177500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177503 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 1, 1, 4]
def baseStart_6177503 : Nat := 118140960795 + 6177503 * 2 ^ 59
def prefixEnd_6177503 : Nat := 4983230072969 + 3 ^ 40 * 6177503 * 2
def baseEnd_6177503 : Nat := 3172028283591649224802687

theorem tailTrace_6177503 : CollatzResearch.WordTrace tailWord_6177503 prefixEnd_6177503 3172028283591649224802687 := by
  unfold tailWord_6177503
  simp only [CollatzResearch.WordTrace]
  refine ⟨225312044538969139362001163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150208029692646092908000775 225312044538969139362001163)
  ·
    refine ⟨337968066808453709043001745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225312044538969139362001163 337968066808453709043001745)
    ·
      refine ⟨253476050106340281782251309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337968066808453709043001745 253476050106340281782251309)
      ·
        refine ⟨95053518789877605668344241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253476050106340281782251309 95053518789877605668344241)
        ·
          refine ⟨71290139092408204251258181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95053518789877605668344241 71290139092408204251258181)
          ·
            refine ⟨13366901079826538297110909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71290139092408204251258181 13366901079826538297110909)
            ·
              refine ⟨5012587904934951861416591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13366901079826538297110909 5012587904934951861416591)
              ·
                refine ⟨7518881857402427792124887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012587904934951861416591 7518881857402427792124887)
                ·
                  refine ⟨11278322786103641688187331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518881857402427792124887 11278322786103641688187331)
                  ·
                    refine ⟨16917484179155462532280997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11278322786103641688187331 16917484179155462532280997)
                    ·
                      refine ⟨3172028283591649224802687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16917484179155462532280997 3172028283591649224802687)
                      ·
                        rfl

theorem cell23_6177503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_6177503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177503 prefixEnd_6177503 := by exact prefixLift 6177503
  have htrace : WordTrace (prefixWord ++ tailWord_6177503) baseStart_6177503 baseEnd_6177503 := by
    simpa [prefixWord, tailWord_6177503, baseEnd_6177503] using wordTrace_append hprefix tailTrace_6177503
  have hstable : (prefixWord ++ tailWord_6177503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177503).length < 2 ^ (prefixWord ++ tailWord_6177503).sum := by decide
  have hdescent : baseEnd_6177503 < baseStart_6177503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177520 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 1, 2, 2]
def baseStart_6177520 : Nat := 118140960795 + 6177520 * 2 ^ 59
def prefixEnd_6177520 : Nat := 4983230072969 + 3 ^ 40 * 6177520 * 2
def baseEnd_6177520 : Nat := 3172037012762775658290109

theorem tailTrace_6177520 : CollatzResearch.WordTrace tailWord_6177520 prefixEnd_6177520 3172037012762775658290109 := by
  unfold tailWord_6177520
  simp only [CollatzResearch.WordTrace]
  refine ⟨112656332289953775632685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150208443053271700843580009 112656332289953775632685007)
  ·
    refine ⟨168984498434930663449027511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112656332289953775632685007 168984498434930663449027511)
    ·
      refine ⟨253476747652395995173541267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168984498434930663449027511 253476747652395995173541267)
      ·
        refine ⟨380215121478593992760311901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253476747652395995173541267 380215121478593992760311901)
        ·
          refine ⟨142580670554472747285116963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380215121478593992760311901 142580670554472747285116963)
          ·
            refine ⟨213871005831709120927675445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142580670554472747285116963 213871005831709120927675445)
            ·
              refine ⟨20050406796722730086969573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213871005831709120927675445 20050406796722730086969573)
              ·
                refine ⟨3759451274385511891306795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20050406796722730086969573 3759451274385511891306795)
                ·
                  refine ⟨5639176911578267836960193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759451274385511891306795 5639176911578267836960193)
                  ·
                    refine ⟨4229382683683700877720145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5639176911578267836960193 4229382683683700877720145)
                    ·
                      refine ⟨3172037012762775658290109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229382683683700877720145 3172037012762775658290109)
                      ·
                        rfl

theorem cell23_6177520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 1, 2, 2].length) (baseStart_6177520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177520 prefixEnd_6177520 := by exact prefixLift 6177520
  have htrace : WordTrace (prefixWord ++ tailWord_6177520) baseStart_6177520 baseEnd_6177520 := by
    simpa [prefixWord, tailWord_6177520, baseEnd_6177520] using wordTrace_append hprefix tailTrace_6177520
  have hstable : (prefixWord ++ tailWord_6177520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177520).length < 2 ^ (prefixWord ++ tailWord_6177520).sum := by decide
  have hdescent : baseEnd_6177520 < baseStart_6177520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177554 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6177554 : Nat := 118140960795 + 6177554 * 2 ^ 59
def prefixEnd_6177554 : Nat := 4983230072969 + 3 ^ 40 * 6177554 * 2
def baseEnd_6177554 : Nat := 3172054471105028525264953

theorem tailTrace_6177554 : CollatzResearch.WordTrace tailWord_6177554 prefixEnd_6177554 3172054471105028525264953 := by
  unfold tailWord_6177554
  simp only [CollatzResearch.WordTrace]
  refine ⟨56328476165446093768026929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150209269774522916714738477 56328476165446093768026929)
  ·
    refine ⟨42246357124084570326020197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56328476165446093768026929 42246357124084570326020197)
    ·
      refine ⟨7921191960765856936128787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42246357124084570326020197 7921191960765856936128787)
      ·
        refine ⟨11881787941148785404193181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921191960765856936128787 11881787941148785404193181)
        ·
          refine ⟨4455670477930794526572443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11881787941148785404193181 4455670477930794526572443)
          ·
            refine ⟨6683505716896191789858665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455670477930794526572443 6683505716896191789858665)
            ·
              refine ⟨5012629287672143842393999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683505716896191789858665 5012629287672143842393999)
              ·
                refine ⟨7518943931508215763590999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012629287672143842393999 7518943931508215763590999)
                ·
                  refine ⟨11278415897262323645386499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518943931508215763590999 11278415897262323645386499)
                  ·
                    refine ⟨16917623845893485468079749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11278415897262323645386499 16917623845893485468079749)
                    ·
                      refine ⟨3172054471105028525264953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16917623845893485468079749 3172054471105028525264953)
                      ·
                        rfl

theorem cell23_6177554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6177554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177554 prefixEnd_6177554 := by exact prefixLift 6177554
  have htrace : WordTrace (prefixWord ++ tailWord_6177554) baseStart_6177554 baseEnd_6177554 := by
    simpa [prefixWord, tailWord_6177554, baseEnd_6177554] using wordTrace_append hprefix tailTrace_6177554
  have hstable : (prefixWord ++ tailWord_6177554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177554).length < 2 ^ (prefixWord ++ tailWord_6177554).sum := by decide
  have hdescent : baseEnd_6177554 < baseStart_6177554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177569 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_6177569 : Nat := 118140960795 + 6177569 * 2 ^ 59
def prefixEnd_6177569 : Nat := 4983230072969 + 3 ^ 40 * 6177569 * 2
def baseEnd_6177569 : Nat := 1057354057771615322192461

theorem tailTrace_6177569 : CollatzResearch.WordTrace tailWord_6177569 prefixEnd_6177569 1057354057771615322192461 := by
  unfold tailWord_6177569
  simp only [CollatzResearch.WordTrace]
  refine ⟨225314451756730032633903761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150209634504486688422602507 225314451756730032633903761)
  ·
    refine ⟨168985838817547524475427821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225314451756730032633903761 168985838817547524475427821)
    ·
      refine ⟨63369689556580321678285433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168985838817547524475427821 63369689556580321678285433)
      ·
        refine ⟨47527267167435241258714075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63369689556580321678285433 47527267167435241258714075)
        ·
          refine ⟨71290900751152861888071113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47527267167435241258714075 71290900751152861888071113)
          ·
            refine ⟨53468175563364646416053335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71290900751152861888071113 53468175563364646416053335)
            ·
              refine ⟨80202263345046969624080003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53468175563364646416053335 80202263345046969624080003)
              ·
                refine ⟨120303395017570454436120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80202263345046969624080003 120303395017570454436120005)
                ·
                  refine ⟨22556886565794460206772501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120303395017570454436120005 22556886565794460206772501)
                  ·
                    refine ⟨1057354057771615322192461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22556886565794460206772501 1057354057771615322192461)
                    ·
                      rfl

theorem cell23_6177569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_6177569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177569 prefixEnd_6177569 := by exact prefixLift 6177569
  have htrace : WordTrace (prefixWord ++ tailWord_6177569) baseStart_6177569 baseEnd_6177569 := by
    simpa [prefixWord, tailWord_6177569, baseEnd_6177569] using wordTrace_append hprefix tailTrace_6177569
  have hstable : (prefixWord ++ tailWord_6177569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177569).length < 2 ^ (prefixWord ++ tailWord_6177569).sum := by decide
  have hdescent : baseEnd_6177569 < baseStart_6177569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177570 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_6177570 : Nat := 118140960795 + 6177570 * 2 ^ 59
def prefixEnd_6177570 : Nat := 4983230072969 + 3 ^ 40 * 6177570 * 2
def baseEnd_6177570 : Nat := 3172062686795500462664879

theorem tailTrace_6177570 : CollatzResearch.WordTrace tailWord_6177570 prefixEnd_6177570 3172062686795500462664879 := by
  unfold tailWord_6177570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56328622057431602451172541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150209658819817606536460109 56328622057431602451172541)
  ·
    refine ⟨21123233271536850919189703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56328622057431602451172541 21123233271536850919189703)
    ·
      refine ⟨31684849907305276378784555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21123233271536850919189703 31684849907305276378784555)
      ·
        refine ⟨47527274860957914568176833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31684849907305276378784555 47527274860957914568176833)
        ·
          refine ⟨35645456145718435926132625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47527274860957914568176833 35645456145718435926132625)
          ·
            refine ⟨26734092109288826944599469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35645456145718435926132625 26734092109288826944599469)
            ·
              refine ⟨10025284540983310104224801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26734092109288826944599469 10025284540983310104224801)
              ·
                refine ⟨7518963405737482578168601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025284540983310104224801 7518963405737482578168601)
                ·
                  refine ⟨5639222554303111933626451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518963405737482578168601 5639222554303111933626451)
                  ·
                    refine ⟨8458833831454667900439677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639222554303111933626451 8458833831454667900439677)
                    ·
                      refine ⟨3172062686795500462664879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8458833831454667900439677 3172062686795500462664879)
                      ·
                        rfl

theorem cell23_6177570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_6177570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177570 prefixEnd_6177570 := by exact prefixLift 6177570
  have htrace : WordTrace (prefixWord ++ tailWord_6177570) baseStart_6177570 baseEnd_6177570 := by
    simpa [prefixWord, tailWord_6177570, baseEnd_6177570] using wordTrace_append hprefix tailTrace_6177570
  have hstable : (prefixWord ++ tailWord_6177570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177570).length < 2 ^ (prefixWord ++ tailWord_6177570).sum := by decide
  have hdescent : baseEnd_6177570 < baseStart_6177570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177597 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6177597 : Nat := 118140960795 + 6177597 * 2 ^ 59
def prefixEnd_6177597 : Nat := 4983230072969 + 3 ^ 40 * 6177597 * 2
def baseEnd_6177597 : Nat := 3172076550773171857027255

theorem tailTrace_6177597 : CollatzResearch.WordTrace tailWord_6177597 prefixEnd_6177597 3172076550773171857027255 := by
  unfold tailWord_6177597
  simp only [CollatzResearch.WordTrace]
  refine ⟨225315473000628593415923045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150210315333752395610615363 225315473000628593415923045)
  ·
    refine ⟨42246651187617861265485571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225315473000628593415923045 42246651187617861265485571)
    ·
      refine ⟨63369976781426791898228357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42246651187617861265485571 63369976781426791898228357)
      ·
        refine ⟨11881870646517523480917817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63369976781426791898228357 11881870646517523480917817)
        ·
          refine ⟨8911402984888142610688363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11881870646517523480917817 8911402984888142610688363)
          ·
            refine ⟨13367104477332213916032545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911402984888142610688363 13367104477332213916032545)
            ·
              refine ⟨10025328357999160437024409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367104477332213916032545 10025328357999160437024409)
              ·
                refine ⟨7518996268499370327768307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025328357999160437024409 7518996268499370327768307)
                ·
                  refine ⟨11278494402749055491652461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7518996268499370327768307 11278494402749055491652461)
                  ·
                    refine ⟨4229435401030895809369673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11278494402749055491652461 4229435401030895809369673)
                    ·
                      refine ⟨3172076550773171857027255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229435401030895809369673 3172076550773171857027255)
                      ·
                        rfl

theorem cell23_6177597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6177597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177597 prefixEnd_6177597 := by exact prefixLift 6177597
  have htrace : WordTrace (prefixWord ++ tailWord_6177597) baseStart_6177597 baseEnd_6177597 := by
    simpa [prefixWord, tailWord_6177597, baseEnd_6177597] using wordTrace_append hprefix tailTrace_6177597
  have hstable : (prefixWord ++ tailWord_6177597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177597).length < 2 ^ (prefixWord ++ tailWord_6177597).sum := by decide
  have hdescent : baseEnd_6177597 < baseStart_6177597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177659 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 8]
def baseStart_6177659 : Nat := 118140960795 + 6177659 * 2 ^ 59
def prefixEnd_6177659 : Nat := 4983230072969 + 3 ^ 40 * 6177659 * 2
def baseEnd_6177659 : Nat := 1057369462191250204817323

theorem tailTrace_6177659 : CollatzResearch.WordTrace tailWord_6177659 prefixEnd_6177659 1057369462191250204817323 := by
  unfold tailWord_6177659
  simp only [CollatzResearch.WordTrace]
  refine ⟨225317734326403978004680031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150211822884269318669786687 225317734326403978004680031)
  ·
    refine ⟨337976601489605967007020047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225317734326403978004680031 337976601489605967007020047)
    ·
      refine ⟨506964902234408950510530071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337976601489605967007020047 506964902234408950510530071)
      ·
        refine ⟨760447353351613425765795107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506964902234408950510530071 760447353351613425765795107)
        ·
          refine ⟨1140671030027420138648692661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760447353351613425765795107 1140671030027420138648692661)
          ·
            refine ⟨106937909065070637998314937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1140671030027420138648692661 106937909065070637998314937)
            ·
              refine ⟨80203431798802978498736203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106937909065070637998314937 80203431798802978498736203)
              ·
                refine ⟨120305147698204467748104305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80203431798802978498736203 120305147698204467748104305)
                ·
                  refine ⟨90228860773653350811078229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120305147698204467748104305 90228860773653350811078229)
                  ·
                    refine ⟨1057369462191250204817323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90228860773653350811078229 1057369462191250204817323)
                    ·
                      rfl

theorem cell23_6177659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_6177659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177659 prefixEnd_6177659 := by exact prefixLift 6177659
  have htrace : WordTrace (prefixWord ++ tailWord_6177659) baseStart_6177659 baseEnd_6177659 := by
    simpa [prefixWord, tailWord_6177659, baseEnd_6177659] using wordTrace_append hprefix tailTrace_6177659
  have hstable : (prefixWord ++ tailWord_6177659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177659).length < 2 ^ (prefixWord ++ tailWord_6177659).sum := by decide
  have hdescent : baseEnd_6177659 < baseStart_6177659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177693 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6177693 : Nat := 118140960795 + 6177693 * 2 ^ 59
def prefixEnd_6177693 : Nat := 4983230072969 + 3 ^ 40 * 6177693 * 2
def baseEnd_6177693 : Nat := 1057375281638667827142271

theorem tailTrace_6177693 : CollatzResearch.WordTrace tailWord_6177693 prefixEnd_6177693 1057375281638667827142271 := by
  unfold tailWord_6177693
  simp only [CollatzResearch.WordTrace]
  refine ⟨225318974408280801811417733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150212649605520534540945155 225318974408280801811417733)
  ·
    refine ⟨42247307701552650339640825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225318974408280801811417733 42247307701552650339640825)
    ·
      refine ⟨31685480776164487754730619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42247307701552650339640825 31685480776164487754730619)
      ·
        refine ⟨47528221164246731632095929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31685480776164487754730619 47528221164246731632095929)
        ·
          refine ⟨35646165873185048724071947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47528221164246731632095929 35646165873185048724071947)
          ·
            refine ⟨53469248809777573086107921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35646165873185048724071947 53469248809777573086107921)
            ·
              refine ⟨40101936607333179814580941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53469248809777573086107921 40101936607333179814580941)
              ·
                refine ⟨15038226227749942430467853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40101936607333179814580941 15038226227749942430467853)
                ·
                  refine ⟨5639334835406228411425445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15038226227749942430467853 5639334835406228411425445)
                  ·
                    refine ⟨1057375281638667827142271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639334835406228411425445 1057375281638667827142271)
                    ·
                      rfl

theorem cell23_6177693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6177693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177693 prefixEnd_6177693 := by exact prefixLift 6177693
  have htrace : WordTrace (prefixWord ++ tailWord_6177693) baseStart_6177693 baseEnd_6177693 := by
    simpa [prefixWord, tailWord_6177693, baseEnd_6177693] using wordTrace_append hprefix tailTrace_6177693
  have hstable : (prefixWord ++ tailWord_6177693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177693).length < 2 ^ (prefixWord ++ tailWord_6177693).sum := by decide
  have hdescent : baseEnd_6177693 < baseStart_6177693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177720 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_6177720 : Nat := 118140960795 + 6177720 * 2 ^ 59
def prefixEnd_6177720 : Nat := 4983230072969 + 3 ^ 40 * 6177720 * 2
def baseEnd_6177720 : Nat := 3172139708893674875789189

theorem tailTrace_6177720 : CollatzResearch.WordTrace tailWord_6177720 prefixEnd_6177720 3172139708893674875789189 := by
  unfold tailWord_6177720
  simp only [CollatzResearch.WordTrace]
  refine ⟨112659979589591492711325307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150213306119455323615100409 112659979589591492711325307)
  ·
    refine ⟨168989969384387239066987961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112659979589591492711325307 168989969384387239066987961)
    ·
      refine ⟨126742477038290429300240971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168989969384387239066987961 126742477038290429300240971)
      ·
        refine ⟨190113715557435643950361457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126742477038290429300240971 190113715557435643950361457)
        ·
          refine ⟨142585286668076732962771093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190113715557435643950361457 142585286668076732962771093)
          ·
            refine ⟨6683685312566096857629895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142585286668076732962771093 6683685312566096857629895)
            ·
              refine ⟨10025527968849145286444843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683685312566096857629895 10025527968849145286444843)
              ·
                refine ⟨15038291953273717929667265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10025527968849145286444843 15038291953273717929667265)
                ·
                  refine ⟨11278718964955288447250449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15038291953273717929667265 11278718964955288447250449)
                  ·
                    refine ⟨8459039223716466335437837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11278718964955288447250449 8459039223716466335437837)
                    ·
                      refine ⟨3172139708893674875789189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459039223716466335437837 3172139708893674875789189)
                      ·
                        rfl

theorem cell23_6177720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_6177720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177720 prefixEnd_6177720 := by exact prefixLift 6177720
  have htrace : WordTrace (prefixWord ++ tailWord_6177720) baseStart_6177720 baseEnd_6177720 := by
    simpa [prefixWord, tailWord_6177720, baseEnd_6177720] using wordTrace_append hprefix tailTrace_6177720
  have hstable : (prefixWord ++ tailWord_6177720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177720).length < 2 ^ (prefixWord ++ tailWord_6177720).sum := by decide
  have hdescent : baseEnd_6177720 < baseStart_6177720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177770 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_6177770 : Nat := 118140960795 + 6177770 * 2 ^ 59
def prefixEnd_6177770 : Nat := 4983230072969 + 3 ^ 40 * 6177770 * 2
def baseEnd_6177770 : Nat := 1057388460975466560054653

theorem tailTrace_6177770 : CollatzResearch.WordTrace tailWord_6177770 prefixEnd_6177770 1057388460975466560054653 := by
  unfold tailWord_6177770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56330445707250460990492691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150214521886001229307980509 56330445707250460990492691)
  ·
    refine ⟨84495668560875691485739037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56330445707250460990492691 84495668560875691485739037)
    ·
      refine ⟨31685875710328384307152139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84495668560875691485739037 31685875710328384307152139)
      ·
        refine ⟨47528813565492576460728209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31685875710328384307152139 47528813565492576460728209)
        ·
          refine ⟨35646610174119432345546157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47528813565492576460728209 35646610174119432345546157)
          ·
            refine ⟨13367478815294787129579809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35646610174119432345546157 13367478815294787129579809)
            ·
              refine ⟨10025609111471090347184857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367478815294787129579809 10025609111471090347184857)
              ·
                refine ⟨7519206833603317760388643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025609111471090347184857 7519206833603317760388643)
                ·
                  refine ⟨11278810250404976640582965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519206833603317760388643 11278810250404976640582965)
                  ·
                    refine ⟨1057388460975466560054653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11278810250404976640582965 1057388460975466560054653)
                    ·
                      rfl

theorem cell23_6177770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_6177770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177770 prefixEnd_6177770 := by exact prefixLift 6177770
  have htrace : WordTrace (prefixWord ++ tailWord_6177770) baseStart_6177770 baseEnd_6177770 := by
    simpa [prefixWord, tailWord_6177770, baseEnd_6177770] using wordTrace_append hprefix tailTrace_6177770
  have hstable : (prefixWord ++ tailWord_6177770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177770).length < 2 ^ (prefixWord ++ tailWord_6177770).sum := by decide
  have hdescent : baseEnd_6177770 < baseStart_6177770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_6177776 : Nat := 118140960795 + 6177776 * 2 ^ 59
def prefixEnd_6177776 : Nat := 4983230072969 + 3 ^ 40 * 6177776 * 2
def baseEnd_6177776 : Nat := 3172168463810326656688931

theorem tailTrace_6177776 : CollatzResearch.WordTrace tailWord_6177776 prefixEnd_6177776 3172168463810326656688931 := by
  unfold tailWord_6177776
  simp only [CollatzResearch.WordTrace]
  refine ⟨112661000833490053493344591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150214667777986737991126121 112661000833490053493344591)
  ·
    refine ⟨168991501250235080240016887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112661000833490053493344591 168991501250235080240016887)
    ·
      refine ⟨253487251875352620360025331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168991501250235080240016887 253487251875352620360025331)
      ·
        refine ⟨380230877813028930540037997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253487251875352620360025331 380230877813028930540037997)
        ·
          refine ⟨142586579179885848952514249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380230877813028930540037997 142586579179885848952514249)
          ·
            refine ⟨106939934384914386714385687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142586579179885848952514249 106939934384914386714385687)
            ·
              refine ⟨160409901577371580071578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106939934384914386714385687 160409901577371580071578531)
              ·
                refine ⟨240614852366057370107367797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160409901577371580071578531 240614852366057370107367797)
                ·
                  refine ⟨22557642409317878447565731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240614852366057370107367797 22557642409317878447565731)
                  ·
                    refine ⟨33836463613976817671348597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22557642409317878447565731 33836463613976817671348597)
                    ·
                      refine ⟨3172168463810326656688931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33836463613976817671348597 3172168463810326656688931)
                      ·
                        rfl

theorem cell23_6177776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_6177776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177776 prefixEnd_6177776 := by exact prefixLift 6177776
  have htrace : WordTrace (prefixWord ++ tailWord_6177776) baseStart_6177776 baseEnd_6177776 := by
    simpa [prefixWord, tailWord_6177776, baseEnd_6177776] using wordTrace_append hprefix tailTrace_6177776
  have hstable : (prefixWord ++ tailWord_6177776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177776).length < 2 ^ (prefixWord ++ tailWord_6177776).sum := by decide
  have hdescent : baseEnd_6177776 < baseStart_6177776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177793 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6177793 : Nat := 118140960795 + 6177793 * 2 ^ 59
def prefixEnd_6177793 : Nat := 4983230072969 + 3 ^ 40 * 6177793 * 2
def baseEnd_6177793 : Nat := 3172177192981453090176353

theorem tailTrace_6177793 : CollatzResearch.WordTrace tailWord_6177793 prefixEnd_6177793 3172177192981453090176353 := by
  unfold tailWord_6177793
  simp only [CollatzResearch.WordTrace]
  refine ⟨225322621707918518890058033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150215081138612345926705355 225322621707918518890058033)
  ·
    refine ⟨168991966280938889167543525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225322621707918518890058033 168991966280938889167543525)
    ·
      refine ⟨31685993677676041718914411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168991966280938889167543525 31685993677676041718914411)
      ·
        refine ⟨47528990516514062578371617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31685993677676041718914411 47528990516514062578371617)
        ·
          refine ⟨35646742887385546933778713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47528990516514062578371617 35646742887385546933778713)
          ·
            refine ⟨26735057165539160200334035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35646742887385546933778713 26735057165539160200334035)
            ·
              refine ⟨40102585748308740300501053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26735057165539160200334035 40102585748308740300501053)
              ·
                refine ⟨15038469655615777612687895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40102585748308740300501053 15038469655615777612687895)
                ·
                  refine ⟨22557704483423666419031843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15038469655615777612687895 22557704483423666419031843)
                  ·
                    refine ⟨33836556725135499628547765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22557704483423666419031843 33836556725135499628547765)
                    ·
                      refine ⟨3172177192981453090176353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33836556725135499628547765 3172177192981453090176353)
                      ·
                        rfl

theorem cell23_6177793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6177793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177793 prefixEnd_6177793 := by exact prefixLift 6177793
  have htrace : WordTrace (prefixWord ++ tailWord_6177793) baseStart_6177793 baseEnd_6177793 := by
    simpa [prefixWord, tailWord_6177793, baseEnd_6177793] using wordTrace_append hprefix tailTrace_6177793
  have hstable : (prefixWord ++ tailWord_6177793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177793).length < 2 ^ (prefixWord ++ tailWord_6177793).sum := by decide
  have hdescent : baseEnd_6177793 < baseStart_6177793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177813 : List Nat := [1, 3, 2, 1, 4, 2, 2, 8]
def baseStart_6177813 : Nat := 118140960795 + 6177813 * 2 ^ 59
def prefixEnd_6177813 : Nat := 4983230072969 + 3 ^ 40 * 6177813 * 2
def baseEnd_6177813 : Nat := 117488424540538630071343

theorem tailTrace_6177813 : CollatzResearch.WordTrace tailWord_6177813 prefixEnd_6177813 117488424540538630071343 := by
  unfold tailWord_6177813
  simp only [CollatzResearch.WordTrace]
  refine ⟨225323351167846062305786093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150215567445230708203857395 225323351167846062305786093)
  ·
    refine ⟨84496256687942273364669785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225323351167846062305786093 84496256687942273364669785)
    ·
      refine ⟨63372192515956705023502339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84496256687942273364669785 63372192515956705023502339)
      ·
        refine ⟨95058288773935057535253509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63372192515956705023502339 95058288773935057535253509)
        ·
          refine ⟨17823429145112823287860033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95058288773935057535253509 17823429145112823287860033)
          ·
            refine ⟨13367571858834617465895025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17823429145112823287860033 13367571858834617465895025)
            ·
              refine ⟨10025678894125963099421269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367571858834617465895025 10025678894125963099421269)
              ·
                refine ⟨117488424540538630071343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10025678894125963099421269 117488424540538630071343)
                ·
                  rfl

theorem cell23_6177813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 8].length) (baseStart_6177813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177813 prefixEnd_6177813 := by exact prefixLift 6177813
  have htrace : WordTrace (prefixWord ++ tailWord_6177813) baseStart_6177813 baseEnd_6177813 := by
    simpa [prefixWord, tailWord_6177813, baseEnd_6177813] using wordTrace_append hprefix tailTrace_6177813
  have hstable : (prefixWord ++ tailWord_6177813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177813).length < 2 ^ (prefixWord ++ tailWord_6177813).sum := by decide
  have hdescent : baseEnd_6177813 < baseStart_6177813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177824 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6177824 : Nat := 118140960795 + 6177824 * 2 ^ 59
def prefixEnd_6177824 : Nat := 4983230072969 + 3 ^ 40 * 6177824 * 2
def baseEnd_6177824 : Nat := 3172193110881742468888711

theorem tailTrace_6177824 : CollatzResearch.WordTrace tailWord_6177824 prefixEnd_6177824 3172193110881742468888711 := by
  unfold tailWord_6177824
  simp only [CollatzResearch.WordTrace]
  refine ⟨112661876185403105592218263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150215834913870807456291017 112661876185403105592218263)
  ·
    refine ⟨168992814278104658388327395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112661876185403105592218263 168992814278104658388327395)
    ·
      refine ⟨253489221417156987582491093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168992814278104658388327395 253489221417156987582491093)
      ·
        refine ⟨5941153626964616896464635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 253489221417156987582491093 5941153626964616896464635)
        ·
          refine ⟨8911730440446925344696953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941153626964616896464635 8911730440446925344696953)
          ·
            refine ⟨6683797830335194008522715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8911730440446925344696953 6683797830335194008522715)
            ·
              refine ⟨10025696745502791012784073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683797830335194008522715 10025696745502791012784073)
              ·
                refine ⟨7519272559127093259588055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025696745502791012784073 7519272559127093259588055)
                ·
                  refine ⟨11278908838690639889382083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519272559127093259588055 11278908838690639889382083)
                  ·
                    refine ⟨16918363258035959834073125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11278908838690639889382083 16918363258035959834073125)
                    ·
                      refine ⟨3172193110881742468888711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16918363258035959834073125 3172193110881742468888711)
                      ·
                        rfl

theorem cell23_6177824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6177824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177824 prefixEnd_6177824 := by exact prefixLift 6177824
  have htrace : WordTrace (prefixWord ++ tailWord_6177824) baseStart_6177824 baseEnd_6177824 := by
    simpa [prefixWord, tailWord_6177824, baseEnd_6177824] using wordTrace_append hprefix tailTrace_6177824
  have hstable : (prefixWord ++ tailWord_6177824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177824).length < 2 ^ (prefixWord ++ tailWord_6177824).sum := by decide
  have hdescent : baseEnd_6177824 < baseStart_6177824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177827 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 3]
def baseStart_6177827 : Nat := 118140960795 + 6177827 * 2 ^ 59
def prefixEnd_6177827 : Nat := 4983230072969 + 3 ^ 40 * 6177827 * 2
def baseEnd_6177827 : Nat := 3172194651323705957151197

theorem tailTrace_6177827 : CollatzResearch.WordTrace tailWord_6177827 prefixEnd_6177827 3172194651323705957151197 := by
  unfold tailWord_6177827
  simp only [CollatzResearch.WordTrace]
  refine ⟨225323861789795342696795735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150215907859863561797863823 225323861789795342696795735)
  ·
    refine ⟨337985792684693014045193603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225323861789795342696795735 337985792684693014045193603)
    ·
      refine ⟨506978689027039521067790405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337985792684693014045193603 506978689027039521067790405)
      ·
        refine ⟨95058504192569910200210701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506978689027039521067790405 95058504192569910200210701)
        ·
          refine ⟨35646939072213716325079013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95058504192569910200210701 35646939072213716325079013)
          ·
            refine ⟨6683801076040071810952315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35646939072213716325079013 6683801076040071810952315)
            ·
              refine ⟨10025701614060107716428473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683801076040071810952315 10025701614060107716428473)
              ·
                refine ⟨7519276210545080787321355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025701614060107716428473 7519276210545080787321355)
                ·
                  refine ⟨11278914315817621180982033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519276210545080787321355 11278914315817621180982033)
                  ·
                    refine ⟨8459185736863215885736525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11278914315817621180982033 8459185736863215885736525)
                    ·
                      refine ⟨3172194651323705957151197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459185736863215885736525 3172194651323705957151197)
                      ·
                        rfl

theorem cell23_6177827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_6177827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177827 prefixEnd_6177827 := by exact prefixLift 6177827
  have htrace : WordTrace (prefixWord ++ tailWord_6177827) baseStart_6177827 baseEnd_6177827 := by
    simpa [prefixWord, tailWord_6177827, baseEnd_6177827] using wordTrace_append hprefix tailTrace_6177827
  have hstable : (prefixWord ++ tailWord_6177827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177827).length < 2 ^ (prefixWord ++ tailWord_6177827).sum := by decide
  have hdescent : baseEnd_6177827 < baseStart_6177827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177863 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_6177863 : Nat := 118140960795 + 6177863 * 2 ^ 59
def prefixEnd_6177863 : Nat := 4983230072969 + 3 ^ 40 * 6177863 * 2
def baseEnd_6177863 : Nat := 3172213136627267816301031

theorem tailTrace_6177863 : CollatzResearch.WordTrace tailWord_6177863 prefixEnd_6177863 3172213136627267816301031 := by
  unfold tailWord_6177863
  simp only [CollatzResearch.WordTrace]
  refine ⟨225325174817664920845106243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150216783211776613896737495 225325174817664920845106243)
  ·
    refine ⟨337987762226497381267659365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225325174817664920845106243 337987762226497381267659365)
    ·
      refine ⟨63372705417468258987686131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337987762226497381267659365 63372705417468258987686131)
      ·
        refine ⟨95059058126202388481529197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63372705417468258987686131 95059058126202388481529197)
        ·
          refine ⟨35647146797325895680573449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95059058126202388481529197 35647146797325895680573449)
          ·
            refine ⟨26735360097994421760430087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35647146797325895680573449 26735360097994421760430087)
            ·
              refine ⟨40103040146991632640645131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26735360097994421760430087 40103040146991632640645131)
              ·
                refine ⟨60154560220487448960967697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40103040146991632640645131 60154560220487448960967697)
                ·
                  refine ⟨45115920165365586720725773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60154560220487448960967697 45115920165365586720725773)
                  ·
                    refine ⟨16918470062012095020272165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45115920165365586720725773 16918470062012095020272165)
                    ·
                      refine ⟨3172213136627267816301031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16918470062012095020272165 3172213136627267816301031)
                      ·
                        rfl

theorem cell23_6177863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_6177863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177863 prefixEnd_6177863 := by exact prefixLift 6177863
  have htrace : WordTrace (prefixWord ++ tailWord_6177863) baseStart_6177863 baseEnd_6177863 := by
    simpa [prefixWord, tailWord_6177863, baseEnd_6177863] using wordTrace_append hprefix tailTrace_6177863
  have hstable : (prefixWord ++ tailWord_6177863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177863).length < 2 ^ (prefixWord ++ tailWord_6177863).sum := by decide
  have hdescent : baseEnd_6177863 < baseStart_6177863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177893 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6177893 : Nat := 118140960795 + 6177893 * 2 ^ 59
def prefixEnd_6177893 : Nat := 4983230072969 + 3 ^ 40 * 6177893 * 2
def baseEnd_6177893 : Nat := 3172228541046902698925893

theorem tailTrace_6177893 : CollatzResearch.WordTrace tailWord_6177893 prefixEnd_6177893 3172228541046902698925893 := by
  unfold tailWord_6177893
  simp only [CollatzResearch.WordTrace]
  refine ⟨225326269007556235968698333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150217512671704157312465555 225326269007556235968698333)
  ·
    refine ⟨84497350877833588488261875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225326269007556235968698333 84497350877833588488261875)
    ·
      refine ⟨126746026316750382732392813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84497350877833588488261875 126746026316750382732392813)
      ·
        refine ⟨47529759868781393524647305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126746026316750382732392813 47529759868781393524647305)
        ·
          refine ⟨35647319901586045143485479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47529759868781393524647305 35647319901586045143485479)
          ·
            refine ⟨53470979852379067715228219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35647319901586045143485479 53470979852379067715228219)
            ·
              refine ⟨80206469778568601572842329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53470979852379067715228219 80206469778568601572842329)
              ·
                refine ⟨60154852333926451179631747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80206469778568601572842329 60154852333926451179631747)
                ·
                  refine ⟨90232278500889676769447621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60154852333926451179631747 90232278500889676769447621)
                  ·
                    refine ⟨16918552218916814394271429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90232278500889676769447621 16918552218916814394271429)
                    ·
                      refine ⟨3172228541046902698925893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16918552218916814394271429 3172228541046902698925893)
                      ·
                        rfl

theorem cell23_6177893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6177893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177893 prefixEnd_6177893 := by exact prefixLift 6177893
  have htrace : WordTrace (prefixWord ++ tailWord_6177893) baseStart_6177893 baseEnd_6177893 := by
    simpa [prefixWord, tailWord_6177893, baseEnd_6177893] using wordTrace_append hprefix tailTrace_6177893
  have hstable : (prefixWord ++ tailWord_6177893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177893).length < 2 ^ (prefixWord ++ tailWord_6177893).sum := by decide
  have hdescent : baseEnd_6177893 < baseStart_6177893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177901 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6177901 : Nat := 118140960795 + 6177901 * 2 ^ 59
def prefixEnd_6177901 : Nat := 4983230072969 + 3 ^ 40 * 6177901 * 2
def baseEnd_6177901 : Nat := 3172232648892138667625857

theorem tailTrace_6177901 : CollatzResearch.WordTrace tailWord_6177901 prefixEnd_6177901 3172232648892138667625857 := by
  unfold tailWord_6177901
  simp only [CollatzResearch.WordTrace]
  refine ⟨225326560791527253334989557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150217707194351502223326371 225326560791527253334989557)
  ·
    refine ⟨21124365074205680000155271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225326560791527253334989557 21124365074205680000155271)
    ·
      refine ⟨31686547611308520000232907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21124365074205680000155271 31686547611308520000232907)
      ·
        refine ⟨47529821416962780000349361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31686547611308520000232907 47529821416962780000349361)
        ·
          refine ⟨35647366062722085000262021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47529821416962780000349361 35647366062722085000262021)
          ·
            refine ⟨6683881136760390937549129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35647366062722085000262021 6683881136760390937549129)
            ·
              refine ⟨5012910852570293203161847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683881136760390937549129 5012910852570293203161847)
              ·
                refine ⟨7519366278855439804742771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012910852570293203161847 7519366278855439804742771)
                ·
                  refine ⟨11279049418283159707114157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519366278855439804742771 11279049418283159707114157)
                  ·
                    refine ⟨4229643531856184890167809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11279049418283159707114157 4229643531856184890167809)
                    ·
                      refine ⟨3172232648892138667625857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229643531856184890167809 3172232648892138667625857)
                      ·
                        rfl

theorem cell23_6177901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6177901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177901 prefixEnd_6177901 := by exact prefixLift 6177901
  have htrace : WordTrace (prefixWord ++ tailWord_6177901) baseStart_6177901 baseEnd_6177901 := by
    simpa [prefixWord, tailWord_6177901, baseEnd_6177901] using wordTrace_append hprefix tailTrace_6177901
  have hstable : (prefixWord ++ tailWord_6177901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177901).length < 2 ^ (prefixWord ++ tailWord_6177901).sum := by decide
  have hdescent : baseEnd_6177901 < baseStart_6177901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177910 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6177910 : Nat := 118140960795 + 6177910 * 2 ^ 59
def prefixEnd_6177910 : Nat := 4983230072969 + 3 ^ 40 * 6177910 * 2
def baseEnd_6177910 : Nat := 3172237270218029132413315

theorem tailTrace_6177910 : CollatzResearch.WordTrace tailWord_6177910 prefixEnd_6177910 3172237270218029132413315 := by
  unfold tailWord_6177910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082930565530915492004199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150217926032329765248044789 14082930565530915492004199)
  ·
    refine ⟨21124395848296373238006299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14082930565530915492004199 21124395848296373238006299)
    ·
      refine ⟨31686593772444559857009449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21124395848296373238006299 31686593772444559857009449)
      ·
        refine ⟨23764945329333419892757087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31686593772444559857009449 23764945329333419892757087)
        ·
          refine ⟨35647417994000129839135631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23764945329333419892757087 35647417994000129839135631)
          ·
            refine ⟨53471126991000194758703447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35647417994000129839135631 53471126991000194758703447)
            ·
              refine ⟨80206690486500292138055171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53471126991000194758703447 80206690486500292138055171)
              ·
                refine ⟨120310035729750438207082757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80206690486500292138055171 120310035729750438207082757)
                ·
                  refine ⟨22558131699328207163828017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120310035729750438207082757 22558131699328207163828017)
                  ·
                    refine ⟨16918598774496155372871013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22558131699328207163828017 16918598774496155372871013)
                    ·
                      refine ⟨3172237270218029132413315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16918598774496155372871013 3172237270218029132413315)
                      ·
                        rfl

theorem cell23_6177910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6177910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177910 prefixEnd_6177910 := by exact prefixLift 6177910
  have htrace : WordTrace (prefixWord ++ tailWord_6177910) baseStart_6177910 baseEnd_6177910 := by
    simpa [prefixWord, tailWord_6177910, baseEnd_6177910] using wordTrace_append hprefix tailTrace_6177910
  have hstable : (prefixWord ++ tailWord_6177910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177910).length < 2 ^ (prefixWord ++ tailWord_6177910).sum := by decide
  have hdescent : baseEnd_6177910 < baseStart_6177910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177920 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 5]
def baseStart_6177920 : Nat := 118140960795 + 6177920 * 2 ^ 59
def prefixEnd_6177920 : Nat := 4983230072969 + 3 ^ 40 * 6177920 * 2
def baseEnd_6177920 : Nat := 352471378336063788143141

theorem tailTrace_6177920 : CollatzResearch.WordTrace tailWord_6177920 prefixEnd_6177920 352471378336063788143141 := by
  unfold tailWord_6177920
  simp only [CollatzResearch.WordTrace]
  refine ⟨112663626889229209789965607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150218169185638946386620809 112663626889229209789965607)
  ·
    refine ⟨168995440333843814684948411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112663626889229209789965607 168995440333843814684948411)
    ·
      refine ⟨253493160500765722027422617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168995440333843814684948411 253493160500765722027422617)
      ·
        refine ⟨190119870375574291520566963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253493160500765722027422617 190119870375574291520566963)
        ·
          refine ⟨285179805563361437280850445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190119870375574291520566963 285179805563361437280850445)
          ·
            refine ⟨106942427086260538980318917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285179805563361437280850445 106942427086260538980318917)
            ·
              refine ⟨20051705078673851058809797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106942427086260538980318917 20051705078673851058809797)
              ·
                refine ⟨3759694702251347073526837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20051705078673851058809797 3759694702251347073526837)
                ·
                  refine ⟨352471378336063788143141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3759694702251347073526837 352471378336063788143141)
                  ·
                    rfl

theorem cell23_6177920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 5].length) (baseStart_6177920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177920 prefixEnd_6177920 := by exact prefixLift 6177920
  have htrace : WordTrace (prefixWord ++ tailWord_6177920) baseStart_6177920 baseEnd_6177920 := by
    simpa [prefixWord, tailWord_6177920, baseEnd_6177920] using wordTrace_append hprefix tailTrace_6177920
  have hstable : (prefixWord ++ tailWord_6177920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177920).length < 2 ^ (prefixWord ++ tailWord_6177920).sum := by decide
  have hdescent : baseEnd_6177920 < baseStart_6177920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177930 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6177930 : Nat := 118140960795 + 6177930 * 2 ^ 59
def prefixEnd_6177930 : Nat := 4983230072969 + 3 ^ 40 * 6177930 * 2
def baseEnd_6177930 : Nat := 3172247539831119054163223

theorem tailTrace_6177930 : CollatzResearch.WordTrace tailWord_6177930 prefixEnd_6177930 3172247539831119054163223 := by
  unfold tailWord_6177930
  simp only [CollatzResearch.WordTrace]
  refine ⟨56331904627105547821948811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150218412338948127525196829 56331904627105547821948811)
  ·
    refine ⟨84497856940658321732923217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56331904627105547821948811 84497856940658321732923217)
    ·
      refine ⟨63373392705493741299692413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84497856940658321732923217 63373392705493741299692413)
      ·
        refine ⟨23765022264560152987384655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63373392705493741299692413 23765022264560152987384655)
        ·
          refine ⟨35647533396840229481076983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23765022264560152987384655 35647533396840229481076983)
          ·
            refine ⟨53471300095260344221615475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35647533396840229481076983 53471300095260344221615475)
            ·
              refine ⟨80206950142890516332423213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53471300095260344221615475 80206950142890516332423213)
              ·
                refine ⟨30077606303583943624658705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80206950142890516332423213 30077606303583943624658705)
                ·
                  refine ⟨22558204727687957718494029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30077606303583943624658705 22558204727687957718494029)
                  ·
                    refine ⟨8459326772882984144435261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22558204727687957718494029 8459326772882984144435261)
                    ·
                      refine ⟨3172247539831119054163223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459326772882984144435261 3172247539831119054163223)
                      ·
                        rfl

theorem cell23_6177930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6177930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177930 prefixEnd_6177930 := by exact prefixLift 6177930
  have htrace : WordTrace (prefixWord ++ tailWord_6177930) baseStart_6177930 baseEnd_6177930 := by
    simpa [prefixWord, tailWord_6177930, baseEnd_6177930] using wordTrace_append hprefix tailTrace_6177930
  have hstable : (prefixWord ++ tailWord_6177930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177930).length < 2 ^ (prefixWord ++ tailWord_6177930).sum := by decide
  have hdescent : baseEnd_6177930 < baseStart_6177930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177970 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6177970 : Nat := 118140960795 + 6177970 * 2 ^ 59
def prefixEnd_6177970 : Nat := 4983230072969 + 3 ^ 40 * 6177970 * 2
def baseEnd_6177970 : Nat := 3172268079057298897663039

theorem tailTrace_6177970 : CollatzResearch.WordTrace tailWord_6177970 prefixEnd_6177970 3172268079057298897663039 := by
  unfold tailWord_6177970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332269357069319529812841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150219384952184852079500909 56332269357069319529812841)
  ·
    refine ⟨42249202017801989647359631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56332269357069319529812841 42249202017801989647359631)
    ·
      refine ⟨63373803026702984471039447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42249202017801989647359631 63373803026702984471039447)
      ·
        refine ⟨95060704540054476706559171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63373803026702984471039447 95060704540054476706559171)
        ·
          refine ⟨142591056810081715059838757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95060704540054476706559171 142591056810081715059838757)
          ·
            refine ⟨26735823151890321573719767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142591056810081715059838757 26735823151890321573719767)
            ·
              refine ⟨40103734727835482360579651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26735823151890321573719767 40103734727835482360579651)
              ·
                refine ⟨60155602091753223540869477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40103734727835482360579651 60155602091753223540869477)
                ·
                  refine ⟨11279175392203729413913027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60155602091753223540869477 11279175392203729413913027)
                  ·
                    refine ⟨16918763088305594120869541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11279175392203729413913027 16918763088305594120869541)
                    ·
                      refine ⟨3172268079057298897663039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16918763088305594120869541 3172268079057298897663039)
                      ·
                        rfl

theorem cell23_6177970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6177970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177970 prefixEnd_6177970 := by exact prefixLift 6177970
  have htrace : WordTrace (prefixWord ++ tailWord_6177970) baseStart_6177970 baseEnd_6177970 := by
    simpa [prefixWord, tailWord_6177970, baseEnd_6177970] using wordTrace_append hprefix tailTrace_6177970
  have hstable : (prefixWord ++ tailWord_6177970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177970).length < 2 ^ (prefixWord ++ tailWord_6177970).sum := by decide
  have hdescent : baseEnd_6177970 < baseStart_6177970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6177983 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_6177983 : Nat := 118140960795 + 6177983 * 2 ^ 59
def prefixEnd_6177983 : Nat := 4983230072969 + 3 ^ 40 * 6177983 * 2
def baseEnd_6177983 : Nat := 3172274754305807346800479

theorem tailTrace_6177983 : CollatzResearch.WordTrace tailWord_6177983 prefixEnd_6177983 3172274754305807346800479 := by
  unfold tailWord_6177983
  simp only [CollatzResearch.WordTrace]
  refine ⟨225329551577230181339474603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150219701051486787559649735 225329551577230181339474603)
  ·
    refine ⟨337994327365845272009211905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225329551577230181339474603 337994327365845272009211905)
    ·
      refine ⟨253495745524383954006908929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337994327365845272009211905 253495745524383954006908929)
      ·
        refine ⟨190121809143287965505181697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253495745524383954006908929 190121809143287965505181697)
        ·
          refine ⟨142591356857465974128886273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190121809143287965505181697 142591356857465974128886273)
          ·
            refine ⟨106943517643099480596664705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142591356857465974128886273 106943517643099480596664705)
            ·
              refine ⟨80207638232324610447498529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106943517643099480596664705 80207638232324610447498529)
              ·
                refine ⟨60155728674243457835623897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80207638232324610447498529 60155728674243457835623897)
                ·
                  refine ⟨45116796505682593376717923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60155728674243457835623897 45116796505682593376717923)
                  ·
                    refine ⟨67675194758523890065076885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45116796505682593376717923 67675194758523890065076885)
                    ·
                      refine ⟨3172274754305807346800479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67675194758523890065076885 3172274754305807346800479)
                      ·
                        rfl

theorem cell23_6177983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_6177983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6177983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6177983 prefixEnd_6177983 := by exact prefixLift 6177983
  have htrace : WordTrace (prefixWord ++ tailWord_6177983) baseStart_6177983 baseEnd_6177983 := by
    simpa [prefixWord, tailWord_6177983, baseEnd_6177983] using wordTrace_append hprefix tailTrace_6177983
  have hstable : (prefixWord ++ tailWord_6177983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6177983).length < 2 ^ (prefixWord ++ tailWord_6177983).sum := by decide
  have hdescent : baseEnd_6177983 < baseStart_6177983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6177983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178071 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 1, 1, 3]
def baseStart_6178071 : Nat := 118140960795 + 6178071 * 2 ^ 59
def prefixEnd_6178071 : Nat := 4983230072969 + 3 ^ 40 * 6178071 * 2
def baseEnd_6178071 : Nat := 3172319940603403002500075

theorem tailTrace_6178071 : CollatzResearch.WordTrace tailWord_6178071 prefixEnd_6178071 3172319940603403002500075 := by
  unfold tailWord_6178071
  simp only [CollatzResearch.WordTrace]
  refine ⟨225332761200911372368678067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150221840800607581579118711 225332761200911372368678067)
  ·
    refine ⟨337999141801367058553017101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225332761200911372368678067 337999141801367058553017101)
    ·
      refine ⟨126749678175512646957381413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337999141801367058553017101 126749678175512646957381413)
      ·
        refine ⟨23765564657908621304509015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126749678175512646957381413 23765564657908621304509015)
        ·
          refine ⟨35648346986862931956763523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23765564657908621304509015 35648346986862931956763523)
          ·
            refine ⟨53472520480294397935145285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35648346986862931956763523 53472520480294397935145285)
            ·
              refine ⟨10026097590055199612839741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53472520480294397935145285 10026097590055199612839741)
              ·
                refine ⟨3759786596270699854814903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10026097590055199612839741 3759786596270699854814903)
                ·
                  refine ⟨5639679894406049782222355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759786596270699854814903 5639679894406049782222355)
                  ·
                    refine ⟨8459519841609074673333533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639679894406049782222355 8459519841609074673333533)
                    ·
                      refine ⟨3172319940603403002500075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459519841609074673333533 3172319940603403002500075)
                      ·
                        rfl

theorem cell23_6178071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_6178071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178071 prefixEnd_6178071 := by exact prefixLift 6178071
  have htrace : WordTrace (prefixWord ++ tailWord_6178071) baseStart_6178071 baseEnd_6178071 := by
    simpa [prefixWord, tailWord_6178071, baseEnd_6178071] using wordTrace_append hprefix tailTrace_6178071
  have hstable : (prefixWord ++ tailWord_6178071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178071).length < 2 ^ (prefixWord ++ tailWord_6178071).sum := by decide
  have hdescent : baseEnd_6178071 < baseStart_6178071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178074 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_6178074 : Nat := 118140960795 + 6178074 * 2 ^ 59
def prefixEnd_6178074 : Nat := 4983230072969 + 3 ^ 40 * 6178074 * 2
def baseEnd_6178074 : Nat := 1057440493681788830254187

theorem tailTrace_6178074 : CollatzResearch.WordTrace tailWord_6178074 prefixEnd_6178074 1057440493681788830254187 := by
  unfold tailWord_6178074
  simp only [CollatzResearch.WordTrace]
  refine ⟨56333217654975125970259319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150221913746600335920691517 56333217654975125970259319)
  ·
    refine ⟨84499826482462688955388979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56333217654975125970259319 84499826482462688955388979)
    ·
      refine ⟨126749739723694033433083469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84499826482462688955388979 126749739723694033433083469)
      ·
        refine ⟨47531152396385262537406301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126749739723694033433083469 47531152396385262537406301)
        ·
          refine ⟨17824182148644473451527363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47531152396385262537406301 17824182148644473451527363)
          ·
            refine ⟨26736273222966710177291045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17824182148644473451527363 26736273222966710177291045)
            ·
              refine ⟨5013051229306258158242071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26736273222966710177291045 5013051229306258158242071)
              ·
                refine ⟨7519576843959387237363107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013051229306258158242071 7519576843959387237363107)
                ·
                  refine ⟨11279365265939080856044661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519576843959387237363107 11279365265939080856044661)
                  ·
                    refine ⟨1057440493681788830254187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11279365265939080856044661 1057440493681788830254187)
                    ·
                      rfl

theorem cell23_6178074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_6178074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178074 prefixEnd_6178074 := by exact prefixLift 6178074
  have htrace : WordTrace (prefixWord ++ tailWord_6178074) baseStart_6178074 baseEnd_6178074 := by
    simpa [prefixWord, tailWord_6178074, baseEnd_6178074] using wordTrace_append hprefix tailTrace_6178074
  have hstable : (prefixWord ++ tailWord_6178074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178074).length < 2 ^ (prefixWord ++ tailWord_6178074).sum := by decide
  have hdescent : baseEnd_6178074 < baseStart_6178074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178078 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6178078 : Nat := 118140960795 + 6178078 * 2 ^ 59
def prefixEnd_6178078 : Nat := 4983230072969 + 3 ^ 40 * 6178078 * 2
def baseEnd_6178078 : Nat := 352480392774220497234727

theorem tailTrace_6178078 : CollatzResearch.WordTrace tailWord_6178078 prefixEnd_6178078 352480392774220497234727 := by
  unfold tailWord_6178078
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166627063985751570522861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150222011007924008376121925 28166627063985751570522861)
  ·
    refine ⟨10562485148994656838946073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28166627063985751570522861 10562485148994656838946073)
    ·
      refine ⟨7921863861745992629209555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10562485148994656838946073 7921863861745992629209555)
      ·
        refine ⟨11882795792618988943814333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921863861745992629209555 11882795792618988943814333)
        ·
          refine ⟨4456048422232120853930375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11882795792618988943814333 4456048422232120853930375)
          ·
            refine ⟨6684072633348181280895563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456048422232120853930375 6684072633348181280895563)
            ·
              refine ⟨10026108950022271921343345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684072633348181280895563 10026108950022271921343345)
              ·
                refine ⟨7519581712516703941007509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026108950022271921343345 7519581712516703941007509)
                ·
                  refine ⟨352480392774220497234727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7519581712516703941007509 352480392774220497234727)
                  ·
                    rfl

theorem cell23_6178078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6178078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178078 prefixEnd_6178078 := by exact prefixLift 6178078
  have htrace : WordTrace (prefixWord ++ tailWord_6178078) baseStart_6178078 baseEnd_6178078 := by
    simpa [prefixWord, tailWord_6178078, baseEnd_6178078] using wordTrace_append hprefix tailTrace_6178078
  have hstable : (prefixWord ++ tailWord_6178078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178078).length < 2 ^ (prefixWord ++ tailWord_6178078).sum := by decide
  have hdescent : baseEnd_6178078 < baseStart_6178078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178097 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6178097 : Nat := 118140960795 + 6178097 * 2 ^ 59
def prefixEnd_6178097 : Nat := 4983230072969 + 3 ^ 40 * 6178097 * 2
def baseEnd_6178097 : Nat := 3172333291100419900774955

theorem tailTrace_6178097 : CollatzResearch.WordTrace tailWord_6178097 prefixEnd_6178097 3172333291100419900774955 := by
  unfold tailWord_6178097
  simp only [CollatzResearch.WordTrace]
  refine ⟨225333709498817178809124545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150222472999211452539416363 225333709498817178809124545)
  ·
    refine ⟨169000282124112884106843409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225333709498817178809124545 169000282124112884106843409)
    ·
      refine ⟨126750211593084663080132557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169000282124112884106843409 126750211593084663080132557)
      ·
        refine ⟨47531329347406748655049709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126750211593084663080132557 47531329347406748655049709)
        ·
          refine ⟨17824248505277530745643641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47531329347406748655049709 17824248505277530745643641)
          ·
            refine ⟨13368186378958148059232731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17824248505277530745643641 13368186378958148059232731)
            ·
              refine ⟨20052279568437222088849097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368186378958148059232731 20052279568437222088849097)
              ·
                refine ⟨15039209676327916566636823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20052279568437222088849097 15039209676327916566636823)
                ·
                  refine ⟨22558814514491874849955235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15039209676327916566636823 22558814514491874849955235)
                  ·
                    refine ⟨33838221771737812274932853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22558814514491874849955235 33838221771737812274932853)
                    ·
                      refine ⟨3172333291100419900774955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33838221771737812274932853 3172333291100419900774955)
                      ·
                        rfl

theorem cell23_6178097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6178097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178097 prefixEnd_6178097 := by exact prefixLift 6178097
  have htrace : WordTrace (prefixWord ++ tailWord_6178097) baseStart_6178097 baseEnd_6178097 := by
    simpa [prefixWord, tailWord_6178097, baseEnd_6178097] using wordTrace_append hprefix tailTrace_6178097
  have hstable : (prefixWord ++ tailWord_6178097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178097).length < 2 ^ (prefixWord ++ tailWord_6178097).sum := by decide
  have hdescent : baseEnd_6178097 < baseStart_6178097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178130 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_6178130 : Nat := 118140960795 + 6178130 * 2 ^ 59
def prefixEnd_6178130 : Nat := 4983230072969 + 3 ^ 40 * 6178130 * 2
def baseEnd_6178130 : Nat := 1057450078654006090554101

theorem tailTrace_6178130 : CollatzResearch.WordTrace tailWord_6178130 prefixEnd_6178130 1057450078654006090554101 := by
  unfold tailWord_6178130
  simp only [CollatzResearch.WordTrace]
  refine ⟨56333728276924406361268961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150223275405131750296717229 56333728276924406361268961)
  ·
    refine ⟨42250296207693304770951721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56333728276924406361268961 42250296207693304770951721)
    ·
      refine ⟨31687722155769978578213791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42250296207693304770951721 31687722155769978578213791)
      ·
        refine ⟨47531583233654967867320687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31687722155769978578213791 47531583233654967867320687)
        ·
          refine ⟨71297374850482451800981031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47531583233654967867320687 71297374850482451800981031)
          ·
            refine ⟨106946062275723677701471547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71297374850482451800981031 106946062275723677701471547)
            ·
              refine ⟨160419093413585516552207321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106946062275723677701471547 160419093413585516552207321)
              ·
                refine ⟨120314320060189137414155491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160419093413585516552207321 120314320060189137414155491)
                ·
                  refine ⟨180471480090283706121233237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120314320060189137414155491 180471480090283706121233237)
                  ·
                    refine ⟨1057450078654006090554101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180471480090283706121233237 1057450078654006090554101)
                    ·
                      rfl

theorem cell23_6178130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_6178130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178130 prefixEnd_6178130 := by exact prefixLift 6178130
  have htrace : WordTrace (prefixWord ++ tailWord_6178130) baseStart_6178130 baseEnd_6178130 := by
    simpa [prefixWord, tailWord_6178130, baseEnd_6178130] using wordTrace_append hprefix tailTrace_6178130
  have hstable : (prefixWord ++ tailWord_6178130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178130).length < 2 ^ (prefixWord ++ tailWord_6178130).sum := by decide
  have hdescent : baseEnd_6178130 < baseStart_6178130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178144 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_6178144 : Nat := 118140960795 + 6178144 * 2 ^ 59
def prefixEnd_6178144 : Nat := 4983230072969 + 3 ^ 40 * 6178144 * 2
def baseEnd_6178144 : Nat := 3172357424691181216887239

theorem tailTrace_6178144 : CollatzResearch.WordTrace tailWord_6178144 prefixEnd_6178144 3172357424691181216887239 := by
  unfold tailWord_6178144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112667711864823452918042743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150223615819764603890723657 112667711864823452918042743)
  ·
    refine ⟨169001567797235179377064115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112667711864823452918042743 169001567797235179377064115)
    ·
      refine ⟨253502351695852769065596173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169001567797235179377064115 253502351695852769065596173)
      ·
        refine ⟨95063381885944788399598565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253502351695852769065596173 95063381885944788399598565)
        ·
          refine ⟨17824384103614647824924731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95063381885944788399598565 17824384103614647824924731)
          ·
            refine ⟨26736576155421971737387097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17824384103614647824924731 26736576155421971737387097)
            ·
              refine ⟨20052432116566478803040323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26736576155421971737387097 20052432116566478803040323)
              ·
                refine ⟨30078648174849718204560485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20052432116566478803040323 30078648174849718204560485)
                ·
                  refine ⟨5639746532784322163355091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30078648174849718204560485 5639746532784322163355091)
                  ·
                    refine ⟨8459619799176483245032637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639746532784322163355091 8459619799176483245032637)
                    ·
                      refine ⟨3172357424691181216887239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459619799176483245032637 3172357424691181216887239)
                      ·
                        rfl

theorem cell23_6178144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_6178144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178144 prefixEnd_6178144 := by exact prefixLift 6178144
  have htrace : WordTrace (prefixWord ++ tailWord_6178144) baseStart_6178144 baseEnd_6178144 := by
    simpa [prefixWord, tailWord_6178144, baseEnd_6178144] using wordTrace_append hprefix tailTrace_6178144
  have hstable : (prefixWord ++ tailWord_6178144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178144).length < 2 ^ (prefixWord ++ tailWord_6178144).sum := by decide
  have hdescent : baseEnd_6178144 < baseStart_6178144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178160 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_6178160 : Nat := 118140960795 + 6178160 * 2 ^ 59
def prefixEnd_6178160 : Nat := 4983230072969 + 3 ^ 40 * 6178160 * 2
def baseEnd_6178160 : Nat := 1057455213460551051429055

theorem tailTrace_6178160 : CollatzResearch.WordTrace tailWord_6178160 prefixEnd_6178160 1057455213460551051429055 := by
  unfold tailWord_6178160
  simp only [CollatzResearch.WordTrace]
  refine ⟨112668003648794470284333967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150224004865059293712445289 112668003648794470284333967)
  ·
    refine ⟨169002005473191705426500951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112668003648794470284333967 169002005473191705426500951)
    ·
      refine ⟨253503008209787558139751427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169002005473191705426500951 253503008209787558139751427)
      ·
        refine ⟨380254512314681337209627141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253503008209787558139751427 380254512314681337209627141)
        ·
          refine ⟨71297721059002750726805089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380254512314681337209627141 71297721059002750726805089)
          ·
            refine ⟨53473290794252063045103817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71297721059002750726805089 53473290794252063045103817)
            ·
              refine ⟨40104968095689047283827863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53473290794252063045103817 40104968095689047283827863)
              ·
                refine ⟨60157452143533570925741795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40104968095689047283827863 60157452143533570925741795)
                ·
                  refine ⟨90236178215300356388612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60157452143533570925741795 90236178215300356388612693)
                  ·
                    refine ⟨1057455213460551051429055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90236178215300356388612693 1057455213460551051429055)
                    ·
                      rfl

theorem cell23_6178160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_6178160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178160 prefixEnd_6178160 := by exact prefixLift 6178160
  have htrace : WordTrace (prefixWord ++ tailWord_6178160) baseStart_6178160 baseEnd_6178160 := by
    simpa [prefixWord, tailWord_6178160, baseEnd_6178160] using wordTrace_append hprefix tailTrace_6178160
  have hstable : (prefixWord ++ tailWord_6178160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178160).length < 2 ^ (prefixWord ++ tailWord_6178160).sum := by decide
  have hdescent : baseEnd_6178160 < baseStart_6178160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178161 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_6178161 : Nat := 118140960795 + 6178161 * 2 ^ 59
def prefixEnd_6178161 : Nat := 4983230072969 + 3 ^ 40 * 6178161 * 2
def baseEnd_6178161 : Nat := 3172366153862307650374661

theorem tailTrace_6178161 : CollatzResearch.WordTrace tailWord_6178161 prefixEnd_6178161 3172366153862307650374661 := by
  unfold tailWord_6178161
  simp only [CollatzResearch.WordTrace]
  refine ⟨225336043770585317739454337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150224029180390211826302891 225336043770585317739454337)
  ·
    refine ⟨169002032827938988304590753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225336043770585317739454337 169002032827938988304590753)
    ·
      refine ⟨126751524620954241228443065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169002032827938988304590753 126751524620954241228443065)
      ·
        refine ⟨95063643465715680921332299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126751524620954241228443065 95063643465715680921332299)
        ·
          refine ⟨142595465198573521381998449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95063643465715680921332299 142595465198573521381998449)
          ·
            refine ⟨106946598898930141036498837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142595465198573521381998449 106946598898930141036498837)
            ·
              refine ⟨5013121823387350361085883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106946598898930141036498837 5013121823387350361085883)
              ·
                refine ⟨7519682735081025541628825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013121823387350361085883 7519682735081025541628825)
                ·
                  refine ⟨5639762051310769156221619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519682735081025541628825 5639762051310769156221619)
                  ·
                    refine ⟨8459643076966153734332429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639762051310769156221619 8459643076966153734332429)
                    ·
                      refine ⟨3172366153862307650374661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459643076966153734332429 3172366153862307650374661)
                      ·
                        rfl

theorem cell23_6178161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_6178161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178161 prefixEnd_6178161 := by exact prefixLift 6178161
  have htrace : WordTrace (prefixWord ++ tailWord_6178161) baseStart_6178161 baseEnd_6178161 := by
    simpa [prefixWord, tailWord_6178161, baseEnd_6178161] using wordTrace_append hprefix tailTrace_6178161
  have hstable : (prefixWord ++ tailWord_6178161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178161).length < 2 ^ (prefixWord ++ tailWord_6178161).sum := by decide
  have hdescent : baseEnd_6178161 < baseStart_6178161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178170 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_6178170 : Nat := 118140960795 + 6178170 * 2 ^ 59
def prefixEnd_6178170 : Nat := 4983230072969 + 3 ^ 40 * 6178170 * 2
def baseEnd_6178170 : Nat := 3172370775188198115162119

theorem tailTrace_6178170 : CollatzResearch.WordTrace tailWord_6178170 prefixEnd_6178170 3172370775188198115162119 := by
  unfold tailWord_6178170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56334093006888178069132991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150224248018368474851021309 56334093006888178069132991)
  ·
    refine ⟨84501139510332267103699487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56334093006888178069132991 84501139510332267103699487)
    ·
      refine ⟨126751709265498400655549231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84501139510332267103699487 126751709265498400655549231)
      ·
        refine ⟨190127563898247600983323847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126751709265498400655549231 190127563898247600983323847)
        ·
          refine ⟨285191345847371401474985771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190127563898247600983323847 285191345847371401474985771)
          ·
            refine ⟨427787018771057102212478657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285191345847371401474985771 427787018771057102212478657)
            ·
              refine ⟨320840264078292826659358993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427787018771057102212478657 320840264078292826659358993)
              ·
                refine ⟨240630198058719619994519245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320840264078292826659358993 240630198058719619994519245)
                ·
                  refine ⟨90236324272019857497944717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240630198058719619994519245 90236324272019857497944717)
                  ·
                    refine ⟨33838621602007446561729269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90236324272019857497944717 33838621602007446561729269)
                    ·
                      refine ⟨3172370775188198115162119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33838621602007446561729269 3172370775188198115162119)
                      ·
                        rfl

theorem cell23_6178170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_6178170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178170 prefixEnd_6178170 := by exact prefixLift 6178170
  have htrace : WordTrace (prefixWord ++ tailWord_6178170) baseStart_6178170 baseEnd_6178170 := by
    simpa [prefixWord, tailWord_6178170, baseEnd_6178170] using wordTrace_append hprefix tailTrace_6178170
  have hstable : (prefixWord ++ tailWord_6178170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178170).length < 2 ^ (prefixWord ++ tailWord_6178170).sum := by decide
  have hdescent : baseEnd_6178170 < baseStart_6178170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178184 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_6178184 : Nat := 118140960795 + 6178184 * 2 ^ 59
def prefixEnd_6178184 : Nat := 4983230072969 + 3 ^ 40 * 6178184 * 2
def baseEnd_6178184 : Nat := 3172377963917361060387055

theorem tailTrace_6178184 : CollatzResearch.WordTrace tailWord_6178184 prefixEnd_6178184 3172377963917361060387055 := by
  unfold tailWord_6178184
  simp only [CollatzResearch.WordTrace]
  refine ⟨112668441324750996333770803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150224588433001328445027737 112668441324750996333770803)
  ·
    refine ⟨169002661987126494500656205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112668441324750996333770803 169002661987126494500656205)
    ·
      refine ⟨63375998245172435437746077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169002661987126494500656205 63375998245172435437746077)
      ·
        refine ⟨23765999341939663289154779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63375998245172435437746077 23765999341939663289154779)
        ·
          refine ⟨35648999012909494933732169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23765999341939663289154779 35648999012909494933732169)
          ·
            refine ⟨26736749259682121200299127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35648999012909494933732169 26736749259682121200299127)
            ·
              refine ⟨40105123889523181800448691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26736749259682121200299127 40105123889523181800448691)
              ·
                refine ⟨60157685834284772700673037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40105123889523181800448691 60157685834284772700673037)
                ·
                  refine ⟨22559132187856789762752389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60157685834284772700673037 22559132187856789762752389)
                  ·
                    refine ⟨4229837285223148080516073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22559132187856789762752389 4229837285223148080516073)
                    ·
                      refine ⟨3172377963917361060387055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229837285223148080516073 3172377963917361060387055)
                      ·
                        rfl

theorem cell23_6178184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_6178184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178184 prefixEnd_6178184 := by exact prefixLift 6178184
  have htrace : WordTrace (prefixWord ++ tailWord_6178184) baseStart_6178184 baseEnd_6178184 := by
    simpa [prefixWord, tailWord_6178184, baseEnd_6178184] using wordTrace_append hprefix tailTrace_6178184
  have hstable : (prefixWord ++ tailWord_6178184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178184).length < 2 ^ (prefixWord ++ tailWord_6178184).sum := by decide
  have hdescent : baseEnd_6178184 < baseStart_6178184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178201 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 2, 2, 2]
def baseStart_6178201 : Nat := 118140960795 + 6178201 * 2 ^ 59
def prefixEnd_6178201 : Nat := 4983230072969 + 3 ^ 40 * 6178201 * 2
def baseEnd_6178201 : Nat := 3172386693088487493874477

theorem tailTrace_6178201 : CollatzResearch.WordTrace tailWord_6178201 prefixEnd_6178201 3172386693088487493874477 := by
  unfold tailWord_6178201
  simp only [CollatzResearch.WordTrace]
  refine ⟨225337502690440404570910457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150225001793626936380606971 225337502690440404570910457)
  ·
    refine ⟨169003127017830303428182843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225337502690440404570910457 169003127017830303428182843)
    ·
      refine ⟨253504690526745455142274265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169003127017830303428182843 253504690526745455142274265)
      ·
        refine ⟨190128517895059091356705699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253504690526745455142274265 190128517895059091356705699)
        ·
          refine ⟨285192776842588637035058549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190128517895059091356705699 285192776842588637035058549)
          ·
            refine ⟨26736822828992684722036739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285192776842588637035058549 26736822828992684722036739)
            ·
              refine ⟨40105234243489027083055109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26736822828992684722036739 40105234243489027083055109)
              ·
                refine ⟨7519731420654192578072833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40105234243489027083055109 7519731420654192578072833)
                ·
                  refine ⟨5639798565490644433554625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519731420654192578072833 5639798565490644433554625)
                  ·
                    refine ⟨4229848924117983325165969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5639798565490644433554625 4229848924117983325165969)
                    ·
                      refine ⟨3172386693088487493874477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4229848924117983325165969 3172386693088487493874477)
                      ·
                        rfl

theorem cell23_6178201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_6178201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178201 prefixEnd_6178201 := by exact prefixLift 6178201
  have htrace : WordTrace (prefixWord ++ tailWord_6178201) baseStart_6178201 baseEnd_6178201 := by
    simpa [prefixWord, tailWord_6178201, baseEnd_6178201] using wordTrace_append hprefix tailTrace_6178201
  have hstable : (prefixWord ++ tailWord_6178201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178201).length < 2 ^ (prefixWord ++ tailWord_6178201).sum := by decide
  have hdescent : baseEnd_6178201 < baseStart_6178201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178237 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_6178237 : Nat := 118140960795 + 6178237 * 2 ^ 59
def prefixEnd_6178237 : Nat := 4983230072969 + 3 ^ 40 * 6178237 * 2
def baseEnd_6178237 : Nat := 1057468392797349784341437

theorem tailTrace_6178237 : CollatzResearch.WordTrace tailWord_6178237 prefixEnd_6178237 1057468392797349784341437 := by
  unfold tailWord_6178237
  simp only [CollatzResearch.WordTrace]
  refine ⟨225338815718309982719220965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150225877145539988479480643 225338815718309982719220965)
  ·
    refine ⟨42251027947183121759853931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225338815718309982719220965 42251027947183121759853931)
    ·
      refine ⟨63376541920774682639780897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42251027947183121759853931 63376541920774682639780897)
      ·
        refine ⟨47532406440581011979835673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63376541920774682639780897 47532406440581011979835673)
        ·
          refine ⟨35649304830435758984876755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47532406440581011979835673 35649304830435758984876755)
          ·
            refine ⟨53473957245653638477315133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35649304830435758984876755 53473957245653638477315133)
            ·
              refine ⟨20052733967120114428993175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53473957245653638477315133 20052733967120114428993175)
              ·
                refine ⟨30079100950680171643489763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20052733967120114428993175 30079100950680171643489763)
                ·
                  refine ⟨45118651426020257465234645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30079100950680171643489763 45118651426020257465234645)
                  ·
                    refine ⟨1057468392797349784341437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45118651426020257465234645 1057468392797349784341437)
                    ·
                      rfl

theorem cell23_6178237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_6178237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178237 prefixEnd_6178237 := by exact prefixLift 6178237
  have htrace : WordTrace (prefixWord ++ tailWord_6178237) baseStart_6178237 baseEnd_6178237 := by
    simpa [prefixWord, tailWord_6178237, baseEnd_6178237] using wordTrace_append hprefix tailTrace_6178237
  have hstable : (prefixWord ++ tailWord_6178237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178237).length < 2 ^ (prefixWord ++ tailWord_6178237).sum := by decide
  have hdescent : baseEnd_6178237 < baseStart_6178237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178311 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6178311 : Nat := 118140960795 + 6178311 * 2 ^ 59
def prefixEnd_6178311 : Nat := 4983230072969 + 3 ^ 40 * 6178311 * 2
def baseEnd_6178311 : Nat := 3172443175960482063498971

theorem tailTrace_6178311 : CollatzResearch.WordTrace tailWord_6178311 prefixEnd_6178311 3172443175960482063498971 := by
  unfold tailWord_6178311
  simp only [CollatzResearch.WordTrace]
  refine ⟨225341514720041893357414787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150227676480027928904943191 225341514720041893357414787)
  ·
    refine ⟨338012272080062840036122181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225341514720041893357414787 338012272080062840036122181)
    ·
      refine ⟨63377301015011782506772909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338012272080062840036122181 63377301015011782506772909)
      ·
        refine ⟨23766487880629418440039841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63377301015011782506772909 23766487880629418440039841)
        ·
          refine ⟨17824865910472063830029881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23766487880629418440039841 17824865910472063830029881)
          ·
            refine ⟨13368649432854047872522411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17824865910472063830029881 13368649432854047872522411)
            ·
              refine ⟨20052974149281071808783617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368649432854047872522411 20052974149281071808783617)
              ·
                refine ⟨15039730611960803856587713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20052974149281071808783617 15039730611960803856587713)
                ·
                  refine ⟨11279797958970602892440785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15039730611960803856587713 11279797958970602892440785)
                  ·
                    refine ⟨8459848469227952169330589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11279797958970602892440785 8459848469227952169330589)
                    ·
                      refine ⟨3172443175960482063498971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459848469227952169330589 3172443175960482063498971)
                      ·
                        rfl

theorem cell23_6178311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6178311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178311 prefixEnd_6178311 := by exact prefixLift 6178311
  have htrace : WordTrace (prefixWord ++ tailWord_6178311) baseStart_6178311 baseEnd_6178311 := by
    simpa [prefixWord, tailWord_6178311, baseEnd_6178311] using wordTrace_append hprefix tailTrace_6178311
  have hstable : (prefixWord ++ tailWord_6178311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178311).length < 2 ^ (prefixWord ++ tailWord_6178311).sum := by decide
  have hdescent : baseEnd_6178311 < baseStart_6178311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178318 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_6178318 : Nat := 118140960795 + 6178318 * 2 ^ 59
def prefixEnd_6178318 : Nat := 4983230072969 + 3 ^ 40 * 6178318 * 2
def baseEnd_6178318 : Nat := 1057482256775021178703813

theorem tailTrace_6178318 : CollatzResearch.WordTrace tailWord_6178318 prefixEnd_6178318 1057482256775021178703813 := by
  unfold tailWord_6178318
  simp only [CollatzResearch.WordTrace]
  refine ⟨28167721253877066694114951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150227846687344355701946405 28167721253877066694114951)
  ·
    refine ⟨42251581880815600041172427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28167721253877066694114951 42251581880815600041172427)
    ·
      refine ⟨63377372821223400061758641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42251581880815600041172427 63377372821223400061758641)
      ·
        refine ⟨47533029615917550046318981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63377372821223400061758641 47533029615917550046318981)
        ·
          refine ⟨8912443052984540633684809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47533029615917550046318981 8912443052984540633684809)
          ·
            refine ⟨6684332289738405475263607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8912443052984540633684809 6684332289738405475263607)
            ·
              refine ⟨10026498434607608212895411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684332289738405475263607 10026498434607608212895411)
              ·
                refine ⟨15039747651911412319343117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10026498434607608212895411 15039747651911412319343117)
                ·
                  refine ⟨5639905369466779619753669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15039747651911412319343117 5639905369466779619753669)
                  ·
                    refine ⟨1057482256775021178703813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639905369466779619753669 1057482256775021178703813)
                    ·
                      rfl

theorem cell23_6178318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_6178318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178318 prefixEnd_6178318 := by exact prefixLift 6178318
  have htrace : WordTrace (prefixWord ++ tailWord_6178318) baseStart_6178318 baseEnd_6178318 := by
    simpa [prefixWord, tailWord_6178318, baseEnd_6178318] using wordTrace_append hprefix tailTrace_6178318
  have hstable : (prefixWord ++ tailWord_6178318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178318).length < 2 ^ (prefixWord ++ tailWord_6178318).sum := by decide
  have hdescent : baseEnd_6178318 < baseStart_6178318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178375 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 1, 1, 3]
def baseStart_6178375 : Nat := 118140960795 + 6178375 * 2 ^ 59
def prefixEnd_6178375 : Nat := 4983230072969 + 3 ^ 40 * 6178375 * 2
def baseEnd_6178375 : Nat := 3172476038722369813098677

theorem tailTrace_6178375 : CollatzResearch.WordTrace tailWord_6178375 prefixEnd_6178375 3172476038722369813098677 := by
  unfold tailWord_6178375
  simp only [CollatzResearch.WordTrace]
  refine ⟨225343848991810032287744579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150229232661206688191829719 225343848991810032287744579)
  ·
    refine ⟨338015773487715048431616869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225343848991810032287744579 338015773487715048431616869)
    ·
      refine ⟨63377957528946571580928163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338015773487715048431616869 63377957528946571580928163)
      ·
        refine ⟨95066936293419857371392245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63377957528946571580928163 95066936293419857371392245)
        ·
          refine ⟨8912525277508111628568023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95066936293419857371392245 8912525277508111628568023)
          ·
            refine ⟨13368787916262167442852035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912525277508111628568023 13368787916262167442852035)
            ·
              refine ⟨20053181874393251164278053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368787916262167442852035 20053181874393251164278053)
              ·
                refine ⟨3759971601448734593302135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20053181874393251164278053 3759971601448734593302135)
                ·
                  refine ⟨5639957402173101889953203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759971601448734593302135 5639957402173101889953203)
                  ·
                    refine ⟨8459936103259652834929805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5639957402173101889953203 8459936103259652834929805)
                    ·
                      refine ⟨3172476038722369813098677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459936103259652834929805 3172476038722369813098677)
                      ·
                        rfl

theorem cell23_6178375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_6178375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178375 prefixEnd_6178375 := by exact prefixLift 6178375
  have htrace : WordTrace (prefixWord ++ tailWord_6178375) baseStart_6178375 baseEnd_6178375 := by
    simpa [prefixWord, tailWord_6178375, baseEnd_6178375] using wordTrace_append hprefix tailTrace_6178375
  have hstable : (prefixWord ++ tailWord_6178375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178375).length < 2 ^ (prefixWord ++ tailWord_6178375).sum := by decide
  have hdescent : baseEnd_6178375 < baseStart_6178375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178377 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_6178377 : Nat := 118140960795 + 6178377 * 2 ^ 59
def prefixEnd_6178377 : Nat := 4983230072969 + 3 ^ 40 * 6178377 * 2
def baseEnd_6178377 : Nat := 3172477065683678805273667

theorem tailTrace_6178377 : CollatzResearch.WordTrace tailWord_6178377 prefixEnd_6178377 3172477065683678805273667 := by
  unfold tailWord_6178377
  simp only [CollatzResearch.WordTrace]
  refine ⟨225343921937802786629317385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150229281291868524419544923 225343921937802786629317385)
  ·
    refine ⟨169007941453352089971988039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225343921937802786629317385 169007941453352089971988039)
    ·
      refine ⟨253511912180028134957982059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169007941453352089971988039 253511912180028134957982059)
      ·
        refine ⟨380267868270042202436973089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253511912180028134957982059 380267868270042202436973089)
        ·
          refine ⟨285200901202531651827729817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380267868270042202436973089 285200901202531651827729817)
          ·
            refine ⟨213900675901898738870797363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285200901202531651827729817 213900675901898738870797363)
            ·
              refine ⟨320851013852848108306196045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213900675901898738870797363 320851013852848108306196045)
              ·
                refine ⟨120319130194818040614823517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320851013852848108306196045 120319130194818040614823517)
                ·
                  refine ⟨45119673823056765230558819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120319130194818040614823517 45119673823056765230558819)
                  ·
                    refine ⟨67679510734585147845838229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45119673823056765230558819 67679510734585147845838229)
                    ·
                      refine ⟨3172477065683678805273667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67679510734585147845838229 3172477065683678805273667)
                      ·
                        rfl

theorem cell23_6178377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_6178377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178377 prefixEnd_6178377 := by exact prefixLift 6178377
  have htrace : WordTrace (prefixWord ++ tailWord_6178377) baseStart_6178377 baseEnd_6178377 := by
    simpa [prefixWord, tailWord_6178377, baseEnd_6178377] using wordTrace_append hprefix tailTrace_6178377
  have hstable : (prefixWord ++ tailWord_6178377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178377).length < 2 ^ (prefixWord ++ tailWord_6178377).sum := by decide
  have hdescent : baseEnd_6178377 < baseStart_6178377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178384 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_6178384 : Nat := 118140960795 + 6178384 * 2 ^ 59
def prefixEnd_6178384 : Nat := 4983230072969 + 3 ^ 40 * 6178384 * 2
def baseEnd_6178384 : Nat := 3172480660048260277886135

theorem tailTrace_6178384 : CollatzResearch.WordTrace tailWord_6178384 prefixEnd_6178384 3172480660048260277886135 := by
  unfold tailWord_6178384
  simp only [CollatzResearch.WordTrace]
  refine ⟨112672088624388713412411103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150229451499184951216548137 112672088624388713412411103)
  ·
    refine ⟨169008132936583070118616655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112672088624388713412411103 169008132936583070118616655)
    ·
      refine ⟨253512199404874605177924983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169008132936583070118616655 253512199404874605177924983)
      ·
        refine ⟨380268299107311907766887475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253512199404874605177924983 380268299107311907766887475)
        ·
          refine ⟨570402448660967861650331213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380268299107311907766887475 570402448660967861650331213)
          ·
            refine ⟨213900918247862948118874205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570402448660967861650331213 213900918247862948118874205)
            ·
              refine ⟨80212844342948605544577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213900918247862948118874205 80212844342948605544577827)
              ·
                refine ⟨120319266514422908316866741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80212844342948605544577827 120319266514422908316866741)
                ·
                  refine ⟨11279931235727147654706257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120319266514422908316866741 11279931235727147654706257)
                  ·
                    refine ⟨8459948426795360741029693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11279931235727147654706257 8459948426795360741029693)
                    ·
                      refine ⟨3172480660048260277886135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459948426795360741029693 3172480660048260277886135)
                      ·
                        rfl

theorem cell23_6178384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_6178384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178384 prefixEnd_6178384 := by exact prefixLift 6178384
  have htrace : WordTrace (prefixWord ++ tailWord_6178384) baseStart_6178384 baseEnd_6178384 := by
    simpa [prefixWord, tailWord_6178384, baseEnd_6178384] using wordTrace_append hprefix tailTrace_6178384
  have hstable : (prefixWord ++ tailWord_6178384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178384).length < 2 ^ (prefixWord ++ tailWord_6178384).sum := by decide
  have hdescent : baseEnd_6178384 < baseStart_6178384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178391 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 2, 4]
def baseStart_6178391 : Nat := 118140960795 + 6178391 * 2 ^ 59
def prefixEnd_6178391 : Nat := 4983230072969 + 3 ^ 40 * 6178391 * 2
def baseEnd_6178391 : Nat := 1057494751470947250166201

theorem tailTrace_6178391 : CollatzResearch.WordTrace tailWord_6178391 prefixEnd_6178391 1057494751470947250166201 := by
  unfold tailWord_6178391
  simp only [CollatzResearch.WordTrace]
  refine ⟨225344432559752067020327027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150229621706501378013551351 225344432559752067020327027)
  ·
    refine ⟨338016648839628100530490541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225344432559752067020327027 338016648839628100530490541)
    ·
      refine ⟨126756243314860537698933953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338016648839628100530490541 126756243314860537698933953)
      ·
        refine ⟨95067182486145403274200465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126756243314860537698933953 95067182486145403274200465)
        ·
          refine ⟨71300386864609052455650349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95067182486145403274200465 71300386864609052455650349)
          ·
            refine ⟨26737645074228394670868881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71300386864609052455650349 26737645074228394670868881)
            ·
              refine ⟨20053233805671296003151661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26737645074228394670868881 20053233805671296003151661)
              ·
                refine ⟨7519962677126736001181873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20053233805671296003151661 7519962677126736001181873)
                ·
                  refine ⟨5639972007845052000886405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519962677126736001181873 5639972007845052000886405)
                  ·
                    refine ⟨1057494751470947250166201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639972007845052000886405 1057494751470947250166201)
                    ·
                      rfl

theorem cell23_6178391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_6178391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178391 prefixEnd_6178391 := by exact prefixLift 6178391
  have htrace : WordTrace (prefixWord ++ tailWord_6178391) baseStart_6178391 baseEnd_6178391 := by
    simpa [prefixWord, tailWord_6178391, baseEnd_6178391] using wordTrace_append hprefix tailTrace_6178391
  have hstable : (prefixWord ++ tailWord_6178391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178391).length < 2 ^ (prefixWord ++ tailWord_6178391).sum := by decide
  have hdescent : baseEnd_6178391 < baseStart_6178391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178401 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_6178401 : Nat := 118140960795 + 6178401 * 2 ^ 59
def prefixEnd_6178401 : Nat := 4983230072969 + 3 ^ 40 * 6178401 * 2
def baseEnd_6178401 : Nat := 3172489389219386711373557

theorem tailTrace_6178401 : CollatzResearch.WordTrace tailWord_6178401 prefixEnd_6178401 3172489389219386711373557 := by
  unfold tailWord_6178401
  simp only [CollatzResearch.WordTrace]
  refine ⟨225344797289715838728191057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150229864859810559152127371 225344797289715838728191057)
  ·
    refine ⟨169008597967286879046143293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225344797289715838728191057 169008597967286879046143293)
    ·
      refine ⟨63378224237732579642303735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169008597967286879046143293 63378224237732579642303735)
      ·
        refine ⟨95067336356598869463455603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63378224237732579642303735 95067336356598869463455603)
        ·
          refine ⟨142601004534898304195183405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95067336356598869463455603 142601004534898304195183405)
          ·
            refine ⟨53475376700586864073193777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142601004534898304195183405 53475376700586864073193777)
            ·
              refine ⟨40106532525440148054895333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53475376700586864073193777 40106532525440148054895333)
              ·
                refine ⟨7519974848520027760292875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40106532525440148054895333 7519974848520027760292875)
                ·
                  refine ⟨11279962272780041640439313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519974848520027760292875 11279962272780041640439313)
                  ·
                    refine ⟨8459971704585031230329485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11279962272780041640439313 8459971704585031230329485)
                    ·
                      refine ⟨3172489389219386711373557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459971704585031230329485 3172489389219386711373557)
                      ·
                        rfl

theorem cell23_6178401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_6178401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178401 prefixEnd_6178401 := by exact prefixLift 6178401
  have htrace : WordTrace (prefixWord ++ tailWord_6178401) baseStart_6178401 baseEnd_6178401 := by
    simpa [prefixWord, tailWord_6178401, baseEnd_6178401] using wordTrace_append hprefix tailTrace_6178401
  have hstable : (prefixWord ++ tailWord_6178401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178401).length < 2 ^ (prefixWord ++ tailWord_6178401).sum := by decide
  have hdescent : baseEnd_6178401 < baseStart_6178401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178418 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6178418 : Nat := 118140960795 + 6178418 * 2 ^ 59
def prefixEnd_6178418 : Nat := 4983230072969 + 3 ^ 40 * 6178418 * 2
def baseEnd_6178418 : Nat := 3172498118390513144860979

theorem tailTrace_6178418 : CollatzResearch.WordTrace tailWord_6178418 prefixEnd_6178418 3172498118390513144860979 := by
  unfold tailWord_6178418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56336354332663562657889977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150230278220436167087706605 56336354332663562657889977)
  ·
    refine ⟨42252265749497671993417483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56336354332663562657889977 42252265749497671993417483)
    ·
      refine ⟨63378398624246507990126225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42252265749497671993417483 63378398624246507990126225)
      ·
        refine ⟨47533798968184880992594669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63378398624246507990126225 47533798968184880992594669)
        ·
          refine ⟨17825174613069330372223001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47533798968184880992594669 17825174613069330372223001)
          ·
            refine ⟨13368880959801997779167251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17825174613069330372223001 13368880959801997779167251)
            ·
              refine ⟨20053321439702996668750877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368880959801997779167251 20053321439702996668750877)
              ·
                refine ⟨7519995539888623750781579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20053321439702996668750877 7519995539888623750781579)
                ·
                  refine ⟨11279993309832935626172369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519995539888623750781579 11279993309832935626172369)
                  ·
                    refine ⟨8459994982374701719629277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11279993309832935626172369 8459994982374701719629277)
                    ·
                      refine ⟨3172498118390513144860979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8459994982374701719629277 3172498118390513144860979)
                      ·
                        rfl

theorem cell23_6178418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6178418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178418 prefixEnd_6178418 := by exact prefixLift 6178418
  have htrace : WordTrace (prefixWord ++ tailWord_6178418) baseStart_6178418 baseEnd_6178418 := by
    simpa [prefixWord, tailWord_6178418, baseEnd_6178418] using wordTrace_append hprefix tailTrace_6178418
  have hstable : (prefixWord ++ tailWord_6178418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178418).length < 2 ^ (prefixWord ++ tailWord_6178418).sum := by decide
  have hdescent : baseEnd_6178418 < baseStart_6178418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178441 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 5, 3, 2]
def baseStart_6178441 : Nat := 118140960795 + 6178441 * 2 ^ 59
def prefixEnd_6178441 : Nat := 4983230072969 + 3 ^ 40 * 6178441 * 2
def baseEnd_6178441 : Nat := 3172509928445566554873373

theorem tailTrace_6178441 : CollatzResearch.WordTrace tailWord_6178441 prefixEnd_6178441 3172509928445566554873373 := by
  unfold tailWord_6178441
  simp only [CollatzResearch.WordTrace]
  refine ⟨225346256209570925559647177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150230837473047283706431451 225346256209570925559647177)
  ·
    refine ⟨169009692157178194169735383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225346256209570925559647177 169009692157178194169735383)
    ·
      refine ⟨253514538235767291254603075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169009692157178194169735383 253514538235767291254603075)
      ·
        refine ⟨380271807353650936881904613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253514538235767291254603075 380271807353650936881904613)
        ·
          refine ⟨71300963878809550665357115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380271807353650936881904613 71300963878809550665357115)
          ·
            refine ⟨106951445818214325998035673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71300963878809550665357115 106951445818214325998035673)
            ·
              refine ⟨80213584363660744498526755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106951445818214325998035673 80213584363660744498526755)
              ·
                refine ⟨120320376545491116747790133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80213584363660744498526755 120320376545491116747790133)
                ·
                  refine ⟨11280035301139792195105325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120320376545491116747790133 11280035301139792195105325)
                  ·
                    refine ⟨4230013237927422073164497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11280035301139792195105325 4230013237927422073164497)
                    ·
                      refine ⟨3172509928445566554873373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230013237927422073164497 3172509928445566554873373)
                      ·
                        rfl

theorem cell23_6178441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3, 2].length) (baseStart_6178441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178441 prefixEnd_6178441 := by exact prefixLift 6178441
  have htrace : WordTrace (prefixWord ++ tailWord_6178441) baseStart_6178441 baseEnd_6178441 := by
    simpa [prefixWord, tailWord_6178441, baseEnd_6178441] using wordTrace_append hprefix tailTrace_6178441
  have hstable : (prefixWord ++ tailWord_6178441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178441).length < 2 ^ (prefixWord ++ tailWord_6178441).sum := by decide
  have hdescent : baseEnd_6178441 < baseStart_6178441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178466 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6178466 : Nat := 118140960795 + 6178466 * 2 ^ 59
def prefixEnd_6178466 : Nat := 4983230072969 + 3 ^ 40 * 6178466 * 2
def baseEnd_6178466 : Nat := 3172522765461928957060759

theorem tailTrace_6178466 : CollatzResearch.WordTrace tailWord_6178466 prefixEnd_6178466 3172522765461928957060759 := by
  unfold tailWord_6178466
  simp only [CollatzResearch.WordTrace]
  refine ⟨56336792008620088707326813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150231445356320236552871501 56336792008620088707326813)
  ·
    refine ⟨21126297003232533265247555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56336792008620088707326813 21126297003232533265247555)
    ·
      refine ⟨31689445504848799897871333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21126297003232533265247555 31689445504848799897871333)
      ·
        refine ⟨5941771032159149980850875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31689445504848799897871333 5941771032159149980850875)
        ·
          refine ⟨8912656548238724971276313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941771032159149980850875 8912656548238724971276313)
          ·
            refine ⟨6684492411179043728457235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8912656548238724971276313 6684492411179043728457235)
            ·
              refine ⟨10026738616768565592685853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684492411179043728457235 10026738616768565592685853)
              ·
                refine ⟨3760026981288212097257195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10026738616768565592685853 3760026981288212097257195)
                ·
                  refine ⟨5640040471932318145885793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760026981288212097257195 5640040471932318145885793)
                  ·
                    refine ⟨4230030353949238609414345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5640040471932318145885793 4230030353949238609414345)
                    ·
                      refine ⟨3172522765461928957060759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230030353949238609414345 3172522765461928957060759)
                      ·
                        rfl

theorem cell23_6178466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6178466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178466 prefixEnd_6178466 := by exact prefixLift 6178466
  have htrace : WordTrace (prefixWord ++ tailWord_6178466) baseStart_6178466 baseEnd_6178466 := by
    simpa [prefixWord, tailWord_6178466, baseEnd_6178466] using wordTrace_append hprefix tailTrace_6178466
  have hstable : (prefixWord ++ tailWord_6178466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178466).length < 2 ^ (prefixWord ++ tailWord_6178466).sum := by decide
  have hdescent : baseEnd_6178466 < baseStart_6178466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178509 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6178509 : Nat := 118140960795 + 6178509 * 2 ^ 59
def prefixEnd_6178509 : Nat := 4983230072969 + 3 ^ 40 * 6178509 * 2
def baseEnd_6178509 : Nat := 3172544845130072288823061

theorem tailTrace_6178509 : CollatzResearch.WordTrace tailWord_6178509 prefixEnd_6178509 3172544845130072288823061 := by
  unfold tailWord_6178509
  simp only [CollatzResearch.WordTrace]
  refine ⟨225348736373324573173122581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150232490915549715448748387 225348736373324573173122581)
  ·
    refine ⟨10563222017499589367490121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225348736373324573173122581 10563222017499589367490121)
    ·
      refine ⟨7922416513124692025617591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10563222017499589367490121 7922416513124692025617591)
      ·
        refine ⟨11883624769687038038426387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922416513124692025617591 11883624769687038038426387)
        ·
          refine ⟨17825437154530557057639581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883624769687038038426387 17825437154530557057639581)
          ·
            refine ⟨6684538932948958896614843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17825437154530557057639581 6684538932948958896614843)
            ·
              refine ⟨10026808399423438344922265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684538932948958896614843 10026808399423438344922265)
              ·
                refine ⟨7520106299567578758691699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026808399423438344922265 7520106299567578758691699)
                ·
                  refine ⟨11280159449351368138037549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520106299567578758691699 11280159449351368138037549)
                  ·
                    refine ⟨4230059793506763051764081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11280159449351368138037549 4230059793506763051764081)
                    ·
                      refine ⟨3172544845130072288823061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230059793506763051764081 3172544845130072288823061)
                      ·
                        rfl

theorem cell23_6178509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6178509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178509 prefixEnd_6178509 := by exact prefixLift 6178509
  have htrace : WordTrace (prefixWord ++ tailWord_6178509) baseStart_6178509 baseEnd_6178509 := by
    simpa [prefixWord, tailWord_6178509, baseEnd_6178509] using wordTrace_append hprefix tailTrace_6178509
  have hstable : (prefixWord ++ tailWord_6178509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178509).length < 2 ^ (prefixWord ++ tailWord_6178509).sum := by decide
  have hdescent : baseEnd_6178509 < baseStart_6178509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178545 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 5]
def baseStart_6178545 : Nat := 118140960795 + 6178545 * 2 ^ 59
def prefixEnd_6178545 : Nat := 4983230072969 + 3 ^ 40 * 6178545 * 2
def baseEnd_6178545 : Nat := 352507036714848238663655

theorem tailTrace_6178545 : CollatzResearch.WordTrace tailWord_6178545 prefixEnd_6178545 352507036714848238663655 := by
  unfold tailWord_6178545
  simp only [CollatzResearch.WordTrace]
  refine ⟨225350049401194151321433089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150233366267462767547622059 225350049401194151321433089)
  ·
    refine ⟨169012537050895613491074817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225350049401194151321433089 169012537050895613491074817)
    ·
      refine ⟨126759402788171710118306113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169012537050895613491074817 126759402788171710118306113)
      ·
        refine ⟨95069552091128782588729585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126759402788171710118306113 95069552091128782588729585)
        ·
          refine ⟨71302164068346586941547189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95069552091128782588729585 71302164068346586941547189)
          ·
            refine ⟨6684577881407492525770049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71302164068346586941547189 6684577881407492525770049)
            ·
              refine ⟨5013433411055619394327537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6684577881407492525770049 5013433411055619394327537)
              ·
                refine ⟨3760075058291714545745653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013433411055619394327537 3760075058291714545745653)
                ·
                  refine ⟨352507036714848238663655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3760075058291714545745653 352507036714848238663655)
                  ·
                    rfl

theorem cell23_6178545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 5].length) (baseStart_6178545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178545 prefixEnd_6178545 := by exact prefixLift 6178545
  have htrace : WordTrace (prefixWord ++ tailWord_6178545) baseStart_6178545 baseEnd_6178545 := by
    simpa [prefixWord, tailWord_6178545, baseEnd_6178545] using wordTrace_append hprefix tailTrace_6178545
  have hstable : (prefixWord ++ tailWord_6178545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178545).length < 2 ^ (prefixWord ++ tailWord_6178545).sum := by decide
  have hdescent : baseEnd_6178545 < baseStart_6178545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178554 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_6178554 : Nat := 118140960795 + 6178554 * 2 ^ 59
def prefixEnd_6178554 : Nat := 4983230072969 + 3 ^ 40 * 6178554 * 2
def baseEnd_6178554 : Nat := 1057522650586508204253451

theorem tailTrace_6178554 : CollatzResearch.WordTrace tailWord_6178554 prefixEnd_6178554 1057522650586508204253451 := by
  unfold tailWord_6178554
  simp only [CollatzResearch.WordTrace]
  refine ⟨56337594414540386464627679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150233585105441030572340477 56337594414540386464627679)
  ·
    refine ⟨84506391621810579696941519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56337594414540386464627679 84506391621810579696941519)
    ·
      refine ⟨126759587432715869545412279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84506391621810579696941519 126759587432715869545412279)
      ·
        refine ⟨190139381149073804318118419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126759587432715869545412279 190139381149073804318118419)
        ·
          refine ⟨285209071723610706477177629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190139381149073804318118419 285209071723610706477177629)
          ·
            refine ⟨106953401896354014928941611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285209071723610706477177629 106953401896354014928941611)
            ·
              refine ⟨160430102844531022393412417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106953401896354014928941611 160430102844531022393412417)
              ·
                refine ⟨120322577133398266795059313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160430102844531022393412417 120322577133398266795059313)
                ·
                  refine ⟨90241932850048700096294485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120322577133398266795059313 90241932850048700096294485)
                  ·
                    refine ⟨1057522650586508204253451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90241932850048700096294485 1057522650586508204253451)
                    ·
                      rfl

theorem cell23_6178554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_6178554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178554 prefixEnd_6178554 := by exact prefixLift 6178554
  have htrace : WordTrace (prefixWord ++ tailWord_6178554) baseStart_6178554 baseEnd_6178554 := by
    simpa [prefixWord, tailWord_6178554, baseEnd_6178554] using wordTrace_append hprefix tailTrace_6178554
  have hstable : (prefixWord ++ tailWord_6178554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178554).length < 2 ^ (prefixWord ++ tailWord_6178554).sum := by decide
  have hdescent : baseEnd_6178554 < baseStart_6178554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178561 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6178561 : Nat := 118140960795 + 6178561 * 2 ^ 59
def prefixEnd_6178561 : Nat := 4983230072969 + 3 ^ 40 * 6178561 * 2
def baseEnd_6178561 : Nat := 3172571546124106085372821

theorem tailTrace_6178561 : CollatzResearch.WordTrace tailWord_6178561 prefixEnd_6178561 3172571546124106085372821 := by
  unfold tailWord_6178561
  simp only [CollatzResearch.WordTrace]
  refine ⟨225350632969136186054015537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150233755312757457369343691 225350632969136186054015537)
  ·
    refine ⟨169012974726852139540511653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225350632969136186054015537 169012974726852139540511653)
    ·
      refine ⟨31689932761284776163845935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169012974726852139540511653 31689932761284776163845935)
      ·
        refine ⟨47534899141927164245768903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31689932761284776163845935 47534899141927164245768903)
        ·
          refine ⟨71302348712890746368653355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47534899141927164245768903 71302348712890746368653355)
          ·
            refine ⟨106953523069336119552980033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71302348712890746368653355 106953523069336119552980033)
            ·
              refine ⟨80215142302002089664735025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106953523069336119552980033 80215142302002089664735025)
              ·
                refine ⟨60161356726501567248551269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80215142302002089664735025 60161356726501567248551269)
                ·
                  refine ⟨11280254386219043859103363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60161356726501567248551269 11280254386219043859103363)
                  ·
                    refine ⟨16920381579328565788655045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11280254386219043859103363 16920381579328565788655045)
                    ·
                      refine ⟨3172571546124106085372821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16920381579328565788655045 3172571546124106085372821)
                      ·
                        rfl

theorem cell23_6178561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6178561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178561 prefixEnd_6178561 := by exact prefixLift 6178561
  have htrace : WordTrace (prefixWord ++ tailWord_6178561) baseStart_6178561 baseEnd_6178561 := by
    simpa [prefixWord, tailWord_6178561, baseEnd_6178561] using wordTrace_append hprefix tailTrace_6178561
  have hstable : (prefixWord ++ tailWord_6178561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178561).length < 2 ^ (prefixWord ++ tailWord_6178561).sum := by decide
  have hdescent : baseEnd_6178561 < baseStart_6178561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178571 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 5, 4]
def baseStart_6178571 : Nat := 118140960795 + 6178571 * 2 ^ 59
def prefixEnd_6178571 : Nat := 4983230072969 + 3 ^ 40 * 6178571 * 2
def baseEnd_6178571 : Nat := 1057525560310217015415925

theorem tailTrace_6178571 : CollatzResearch.WordTrace tailWord_6178571 prefixEnd_6178571 1057525560310217015415925 := by
  unfold tailWord_6178571
  simp only [CollatzResearch.WordTrace]
  refine ⟨225350997699099957761879567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150233998466066638507919711 225350997699099957761879567)
  ·
    refine ⟨338026496548649936642819351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225350997699099957761879567 338026496548649936642819351)
    ·
      refine ⟨507039744822974904964229027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338026496548649936642819351 507039744822974904964229027)
      ·
        refine ⟨760559617234462357446343541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507039744822974904964229027 760559617234462357446343541)
        ·
          refine ⟨71302464115730846010594707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 760559617234462357446343541 71302464115730846010594707)
          ·
            refine ⟨106953696173596269015892061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71302464115730846010594707 106953696173596269015892061)
            ·
              refine ⟨40107636065098600880959523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106953696173596269015892061 40107636065098600880959523)
              ·
                refine ⟨60161454097647901321439285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40107636065098600880959523 60161454097647901321439285)
                ·
                  refine ⟨5640136321654490748884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60161454097647901321439285 5640136321654490748884933)
                  ·
                    refine ⟨1057525560310217015415925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640136321654490748884933 1057525560310217015415925)
                    ·
                      rfl

theorem cell23_6178571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 4].length) (baseStart_6178571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178571 prefixEnd_6178571 := by exact prefixLift 6178571
  have htrace : WordTrace (prefixWord ++ tailWord_6178571) baseStart_6178571 baseEnd_6178571 := by
    simpa [prefixWord, tailWord_6178571, baseEnd_6178571] using wordTrace_append hprefix tailTrace_6178571
  have hstable : (prefixWord ++ tailWord_6178571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178571).length < 2 ^ (prefixWord ++ tailWord_6178571).sum := by decide
  have hdescent : baseEnd_6178571 < baseStart_6178571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178631 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 3, 5]
def baseStart_6178631 : Nat := 118140960795 + 6178631 * 2 ^ 59
def prefixEnd_6178631 : Nat := 4983230072969 + 3 ^ 40 * 6178631 * 2
def baseEnd_6178631 : Nat := 1057535829923306937165833

theorem tailTrace_6178631 : CollatzResearch.WordTrace tailWord_6178631 prefixEnd_6178631 1057535829923306937165833 := by
  unfold tailWord_6178631
  simp only [CollatzResearch.WordTrace]
  refine ⟨225353186078882588009063747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150235457385921725339375831 225353186078882588009063747)
  ·
    refine ⟨338029779118323882013595621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225353186078882588009063747 338029779118323882013595621)
    ·
      refine ⟨63380583584685727877549179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338029779118323882013595621 63380583584685727877549179)
      ·
        refine ⟨95070875377028591816323769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63380583584685727877549179 95070875377028591816323769)
        ·
          refine ⟨71303156532771443862242827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95070875377028591816323769 71303156532771443862242827)
          ·
            refine ⟨106954734799157165793364241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71303156532771443862242827 106954734799157165793364241)
            ·
              refine ⟨80216051099367874345023181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106954734799157165793364241 80216051099367874345023181)
              ·
                refine ⟨30081019162262952879383693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80216051099367874345023181 30081019162262952879383693)
                ·
                  refine ⟨11280382185848607329768885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30081019162262952879383693 11280382185848607329768885)
                  ·
                    refine ⟨1057535829923306937165833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11280382185848607329768885 1057535829923306937165833)
                    ·
                      rfl

theorem cell23_6178631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_6178631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178631 prefixEnd_6178631 := by exact prefixLift 6178631
  have htrace : WordTrace (prefixWord ++ tailWord_6178631) baseStart_6178631 baseEnd_6178631 := by
    simpa [prefixWord, tailWord_6178631, baseEnd_6178631] using wordTrace_append hprefix tailTrace_6178631
  have hstable : (prefixWord ++ tailWord_6178631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178631).length < 2 ^ (prefixWord ++ tailWord_6178631).sum := by decide
  have hdescent : baseEnd_6178631 < baseStart_6178631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178655 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 2, 3, 2]
def baseStart_6178655 : Nat := 118140960795 + 6178655 * 2 ^ 59
def prefixEnd_6178655 : Nat := 4983230072969 + 3 ^ 40 * 6178655 * 2
def baseEnd_6178655 : Nat := 3172619813305628717597389

theorem tailTrace_6178655 : CollatzResearch.WordTrace tailWord_6178655 prefixEnd_6178655 3172619813305628717597389 := by
  unfold tailWord_6178655
  simp only [CollatzResearch.WordTrace]
  refine ⟨225354061430795640107937419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236040953863760071958279 225354061430795640107937419)
  ·
    refine ⟨338031092146193460161906129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225354061430795640107937419 338031092146193460161906129)
    ·
      refine ⟨253523319109645095121429597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338031092146193460161906129 253523319109645095121429597)
      ·
        refine ⟨95071244666116910670536099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253523319109645095121429597 95071244666116910670536099)
        ·
          refine ⟨142606866999175366005804149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95071244666116910670536099 142606866999175366005804149)
          ·
            refine ⟨13369393781172690563044139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142606866999175366005804149 13369393781172690563044139)
            ·
              refine ⟨20054090671759035844566209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13369393781172690563044139 20054090671759035844566209)
              ·
                refine ⟨15040568003819276883424657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20054090671759035844566209 15040568003819276883424657)
                ·
                  refine ⟨11280426002864457662568493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15040568003819276883424657 11280426002864457662568493)
                  ·
                    refine ⟨4230159751074171623463185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11280426002864457662568493 4230159751074171623463185)
                    ·
                      refine ⟨3172619813305628717597389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230159751074171623463185 3172619813305628717597389)
                      ·
                        rfl

theorem cell23_6178655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_6178655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178655 prefixEnd_6178655 := by exact prefixLift 6178655
  have htrace : WordTrace (prefixWord ++ tailWord_6178655) baseStart_6178655 baseEnd_6178655 := by
    simpa [prefixWord, tailWord_6178655, baseEnd_6178655] using wordTrace_append hprefix tailTrace_6178655
  have hstable : (prefixWord ++ tailWord_6178655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178655).length < 2 ^ (prefixWord ++ tailWord_6178655).sum := by decide
  have hdescent : baseEnd_6178655 < baseStart_6178655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178671 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_6178671 : Nat := 118140960795 + 6178671 * 2 ^ 59
def prefixEnd_6178671 : Nat := 4983230072969 + 3 ^ 40 * 6178671 * 2
def baseEnd_6178671 : Nat := 3172628028996100654997315

theorem tailTrace_6178671 : CollatzResearch.WordTrace tailWord_6178671 prefixEnd_6178671 3172628028996100654997315 := by
  unfold tailWord_6178671
  simp only [CollatzResearch.WordTrace]
  refine ⟨225354644998737674840519867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236429999158449893679911 225354644998737674840519867)
  ·
    refine ⟨338031967498106512260779801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225354644998737674840519867 338031967498106512260779801)
    ·
      refine ⟨253523975623579884195584851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338031967498106512260779801 253523975623579884195584851)
      ·
        refine ⟨380285963435369826293377277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253523975623579884195584851 380285963435369826293377277)
        ·
          refine ⟨142607236288263684860016479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380285963435369826293377277 142607236288263684860016479)
          ·
            refine ⟨213910854432395527290024719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142607236288263684860016479 213910854432395527290024719)
            ·
              refine ⟨320866281648593290935037079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213910854432395527290024719 320866281648593290935037079)
              ·
                refine ⟨481299422472889936402555619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320866281648593290935037079 481299422472889936402555619)
                ·
                  refine ⟨721949133709334904603833429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481299422472889936402555619 721949133709334904603833429)
                  ·
                    refine ⟨8460341410656268413326173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 721949133709334904603833429 8460341410656268413326173)
                    ·
                      refine ⟨3172628028996100654997315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460341410656268413326173 3172628028996100654997315)
                      ·
                        rfl

theorem cell23_6178671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_6178671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178671 prefixEnd_6178671 := by exact prefixLift 6178671
  have htrace : WordTrace (prefixWord ++ tailWord_6178671) baseStart_6178671 baseEnd_6178671 := by
    simpa [prefixWord, tailWord_6178671, baseEnd_6178671] using wordTrace_append hprefix tailTrace_6178671
  have hstable : (prefixWord ++ tailWord_6178671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178671).length < 2 ^ (prefixWord ++ tailWord_6178671).sum := by decide
  have hdescent : baseEnd_6178671 < baseStart_6178671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178681 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6178681 : Nat := 118140960795 + 6178681 * 2 ^ 59
def prefixEnd_6178681 : Nat := 4983230072969 + 3 ^ 40 * 6178681 * 2
def baseEnd_6178681 : Nat := 3172633163802645615872269

theorem tailTrace_6178681 : CollatzResearch.WordTrace tailWord_6178681 prefixEnd_6178681 3172633163802645615872269 := by
  unfold tailWord_6178681
  simp only [CollatzResearch.WordTrace]
  refine ⟨225355009728701446548383897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236673152467631032255931 225355009728701446548383897)
  ·
    refine ⟨169016257296526084911287923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225355009728701446548383897 169016257296526084911287923)
    ·
      refine ⟨253524385944789127366931885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169016257296526084911287923 253524385944789127366931885)
      ·
        refine ⟨95071644729295922762599457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253524385944789127366931885 95071644729295922762599457)
        ·
          refine ⟨71303733546971942071949593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95071644729295922762599457 71303733546971942071949593)
          ·
            refine ⟨53477800160228956553962195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71303733546971942071949593 53477800160228956553962195)
            ·
              refine ⟨80216700240343434830943293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53477800160228956553962195 80216700240343434830943293)
              ·
                refine ⟨30081262590128788061603735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80216700240343434830943293 30081262590128788061603735)
                ·
                  refine ⟨45121893885193182092405603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30081262590128788061603735 45121893885193182092405603)
                  ·
                    refine ⟨67682840827789773138608405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45121893885193182092405603 67682840827789773138608405)
                    ·
                      refine ⟨3172633163802645615872269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67682840827789773138608405 3172633163802645615872269)
                      ·
                        rfl

theorem cell23_6178681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6178681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178681 prefixEnd_6178681 := by exact prefixLift 6178681
  have htrace : WordTrace (prefixWord ++ tailWord_6178681) baseStart_6178681 baseEnd_6178681 := by
    simpa [prefixWord, tailWord_6178681, baseEnd_6178681] using wordTrace_append hprefix tailTrace_6178681
  have hstable : (prefixWord ++ tailWord_6178681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178681).length < 2 ^ (prefixWord ++ tailWord_6178681).sum := by decide
  have hdescent : baseEnd_6178681 < baseStart_6178681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178685 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_6178685 : Nat := 118140960795 + 6178685 * 2 ^ 59
def prefixEnd_6178685 : Nat := 4983230072969 + 3 ^ 40 * 6178685 * 2
def baseEnd_6178685 : Nat := 3172635217725263600222251

theorem tailTrace_6178685 : CollatzResearch.WordTrace tailWord_6178685 prefixEnd_6178685 3172635217725263600222251 := by
  unfold tailWord_6178685
  simp only [CollatzResearch.WordTrace]
  refine ⟨225355155620686955231529509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236770413791303487686339 225355155620686955231529509)
  ·
    refine ⟨42254091678878804105911783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225355155620686955231529509 42254091678878804105911783)
    ·
      refine ⟨63381137518318206158867675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42254091678878804105911783 63381137518318206158867675)
      ·
        refine ⟨95071706277477309238301513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63381137518318206158867675 95071706277477309238301513)
        ·
          refine ⟨71303779708107981928726135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95071706277477309238301513 71303779708107981928726135)
          ·
            refine ⟨106955669562161972893089203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71303779708107981928726135 106955669562161972893089203)
            ·
              refine ⟨160433504343242959339633805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106955669562161972893089203 160433504343242959339633805)
              ·
                refine ⟨60162564128716109752362677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160433504343242959339633805 60162564128716109752362677)
                ·
                  refine ⟨5640240387067135289284001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60162564128716109752362677 5640240387067135289284001)
                  ·
                    refine ⟨4230180290300351466963001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5640240387067135289284001 4230180290300351466963001)
                    ·
                      refine ⟨3172635217725263600222251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230180290300351466963001 3172635217725263600222251)
                      ·
                        rfl

theorem cell23_6178685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_6178685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178685 prefixEnd_6178685 := by exact prefixLift 6178685
  have htrace : WordTrace (prefixWord ++ tailWord_6178685) baseStart_6178685 baseEnd_6178685 := by
    simpa [prefixWord, tailWord_6178685, baseEnd_6178685] using wordTrace_append hprefix tailTrace_6178685
  have hstable : (prefixWord ++ tailWord_6178685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178685).length < 2 ^ (prefixWord ++ tailWord_6178685).sum := by decide
  have hdescent : baseEnd_6178685 < baseStart_6178685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178688 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_6178688 : Nat := 118140960795 + 6178688 * 2 ^ 59
def prefixEnd_6178688 : Nat := 4983230072969 + 3 ^ 40 * 6178688 * 2
def baseEnd_6178688 : Nat := 3172636758167227088484737

theorem tailTrace_6178688 : CollatzResearch.WordTrace tailWord_6178688 prefixEnd_6178688 3172636758167227088484737 := by
  unfold tailWord_6178688
  simp only [CollatzResearch.WordTrace]
  refine ⟨112677632519838043371944359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150236843359784057829259145 112677632519838043371944359)
  ·
    refine ⟨169016448779757065057916539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112677632519838043371944359 169016448779757065057916539)
    ·
      refine ⟨253524673169635597586874809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169016448779757065057916539 253524673169635597586874809)
      ·
        refine ⟨190143504877226698190156107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253524673169635597586874809 190143504877226698190156107)
        ·
          refine ⟨285215257315840047285234161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190143504877226698190156107 285215257315840047285234161)
          ·
            refine ⟨213911442986880035463925621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285215257315840047285234161 213911442986880035463925621)
            ·
              refine ⟨20054197780020003324743027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213911442986880035463925621 20054197780020003324743027)
              ·
                refine ⟨30081296670030004987114541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20054197780020003324743027 30081296670030004987114541)
                ·
                  refine ⟨11280486251261251870167953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30081296670030004987114541 11280486251261251870167953)
                  ·
                    refine ⟨8460364688445938902625965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11280486251261251870167953 8460364688445938902625965)
                    ·
                      refine ⟨3172636758167227088484737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460364688445938902625965 3172636758167227088484737)
                      ·
                        rfl

theorem cell23_6178688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_6178688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178688 prefixEnd_6178688 := by exact prefixLift 6178688
  have htrace : WordTrace (prefixWord ++ tailWord_6178688) baseStart_6178688 baseEnd_6178688 := by
    simpa [prefixWord, tailWord_6178688, baseEnd_6178688] using wordTrace_append hprefix tailTrace_6178688
  have hstable : (prefixWord ++ tailWord_6178688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178688).length < 2 ^ (prefixWord ++ tailWord_6178688).sum := by decide
  have hdescent : baseEnd_6178688 < baseStart_6178688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178689 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6178689 : Nat := 118140960795 + 6178689 * 2 ^ 59
def prefixEnd_6178689 : Nat := 4983230072969 + 3 ^ 40 * 6178689 * 2
def baseEnd_6178689 : Nat := 3172637271647881584572233

theorem tailTrace_6178689 : CollatzResearch.WordTrace tailWord_6178689 prefixEnd_6178689 3172637271647881584572233 := by
  unfold tailWord_6178689
  simp only [CollatzResearch.WordTrace]
  refine ⟨225355301512672463914675121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236867675114975943116747 225355301512672463914675121)
  ·
    refine ⟨169016476134504347936006341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225355301512672463914675121 169016476134504347936006341)
    ·
      refine ⟨31690589275219565238001189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169016476134504347936006341 31690589275219565238001189)
      ·
        refine ⟨5941985489103668482125223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31690589275219565238001189 5941985489103668482125223)
        ·
          refine ⟨8912978233655502723187835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941985489103668482125223 8912978233655502723187835)
          ·
            refine ⟨13369467350483254084781753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912978233655502723187835 13369467350483254084781753)
            ·
              refine ⟨10027100512862440563586315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369467350483254084781753 10027100512862440563586315)
              ·
                refine ⟨15040650769293660845379473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027100512862440563586315 15040650769293660845379473)
                ·
                  refine ⟨11280488076970245634034605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15040650769293660845379473 11280488076970245634034605)
                  ·
                    refine ⟨4230183028863842112762977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11280488076970245634034605 4230183028863842112762977)
                    ·
                      refine ⟨3172637271647881584572233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230183028863842112762977 3172637271647881584572233)
                      ·
                        rfl

theorem cell23_6178689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6178689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178689 prefixEnd_6178689 := by exact prefixLift 6178689
  have htrace : WordTrace (prefixWord ++ tailWord_6178689) baseStart_6178689 baseEnd_6178689 := by
    simpa [prefixWord, tailWord_6178689, baseEnd_6178689] using wordTrace_append hprefix tailTrace_6178689
  have hstable : (prefixWord ++ tailWord_6178689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178689).length < 2 ^ (prefixWord ++ tailWord_6178689).sum := by decide
  have hdescent : baseEnd_6178689 < baseStart_6178689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178691 : List Nat := [1, 1, 1, 3, 4, 2, 2, 9]
def baseStart_6178691 : Nat := 118140960795 + 6178691 * 2 ^ 59
def prefixEnd_6178691 : Nat := 4983230072969 + 3 ^ 40 * 6178691 * 2
def baseEnd_6178691 : Nat := 117505122170710762101749

theorem tailTrace_6178691 : CollatzResearch.WordTrace tailWord_6178691 prefixEnd_6178691 117505122170710762101749 := by
  unfold tailWord_6178691
  simp only [CollatzResearch.WordTrace]
  refine ⟨225355374458665218256247927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150236916305776812170831951 225355374458665218256247927)
  ·
    refine ⟨338033061687997827384371891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225355374458665218256247927 338033061687997827384371891)
    ·
      refine ⟨507049592531996741076557837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338033061687997827384371891 507049592531996741076557837)
      ·
        refine ⟨190143597199498777903709189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507049592531996741076557837 190143597199498777903709189)
        ·
          refine ⟨35651924474906020856945473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190143597199498777903709189 35651924474906020856945473)
          ·
            refine ⟨26738943356179515642709105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35651924474906020856945473 26738943356179515642709105)
            ·
              refine ⟨20054207517134636732031829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26738943356179515642709105 20054207517134636732031829)
              ·
                refine ⟨117505122170710762101749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20054207517134636732031829 117505122170710762101749)
                ·
                  rfl

theorem cell23_6178691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 9].length) (baseStart_6178691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178691 prefixEnd_6178691 := by exact prefixLift 6178691
  have htrace : WordTrace (prefixWord ++ tailWord_6178691) baseStart_6178691 baseEnd_6178691 := by
    simpa [prefixWord, tailWord_6178691, baseEnd_6178691] using wordTrace_append hprefix tailTrace_6178691
  have hstable : (prefixWord ++ tailWord_6178691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178691).length < 2 ^ (prefixWord ++ tailWord_6178691).sum := by decide
  have hdescent : baseEnd_6178691 < baseStart_6178691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178735 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_6178735 : Nat := 118140960795 + 6178735 * 2 ^ 59
def prefixEnd_6178735 : Nat := 4983230072969 + 3 ^ 40 * 6178735 * 2
def baseEnd_6178735 : Nat := 3172660891757988404597021

theorem tailTrace_6178735 : CollatzResearch.WordTrace tailWord_6178735 prefixEnd_6178735 3172660891757988404597021 := by
  unfold tailWord_6178735
  simp only [CollatzResearch.WordTrace]
  refine ⟨225356979270505813770849659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150237986180337209180566439 225356979270505813770849659)
  ·
    refine ⟨338035468905758720656274489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225356979270505813770849659 338035468905758720656274489)
    ·
      refine ⟨253526601679319040492205867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338035468905758720656274489 253526601679319040492205867)
      ·
        refine ⟨380289902518978560738308801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253526601679319040492205867 380289902518978560738308801)
        ·
          refine ⟨285217426889233920553731601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380289902518978560738308801 285217426889233920553731601)
          ·
            refine ⟨213913070166925440415298701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285217426889233920553731601 213913070166925440415298701)
            ·
              refine ⟨80217401312597040155737013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213913070166925440415298701 80217401312597040155737013)
              ·
                refine ⟨7520381373055972514600345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80217401312597040155737013 7520381373055972514600345)
                ·
                  refine ⟨5640286029791979385950259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7520381373055972514600345 5640286029791979385950259)
                  ·
                    refine ⟨8460429044687969078925389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640286029791979385950259 8460429044687969078925389)
                    ·
                      refine ⟨3172660891757988404597021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460429044687969078925389 3172660891757988404597021)
                      ·
                        rfl

theorem cell23_6178735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_6178735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178735 prefixEnd_6178735 := by exact prefixLift 6178735
  have htrace : WordTrace (prefixWord ++ tailWord_6178735) baseStart_6178735 baseEnd_6178735 := by
    simpa [prefixWord, tailWord_6178735, baseEnd_6178735] using wordTrace_append hprefix tailTrace_6178735
  have hstable : (prefixWord ++ tailWord_6178735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178735).length < 2 ^ (prefixWord ++ tailWord_6178735).sum := by decide
  have hdescent : baseEnd_6178735 < baseStart_6178735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178745 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6178745 : Nat := 118140960795 + 6178745 * 2 ^ 59
def prefixEnd_6178745 : Nat := 4983230072969 + 3 ^ 40 * 6178745 * 2
def baseEnd_6178745 : Nat := 3172666026564533365471975

theorem tailTrace_6178745 : CollatzResearch.WordTrace tailWord_6178745 prefixEnd_6178745 3172666026564533365471975 := by
  unfold tailWord_6178745
  simp only [CollatzResearch.WordTrace]
  refine ⟨225357344000469585478713689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150238229333646390319142459 225357344000469585478713689)
  ·
    refine ⟨169018008000352189109035267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225357344000469585478713689 169018008000352189109035267)
    ·
      refine ⟨253527012000528283663552901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169018008000352189109035267 253527012000528283663552901)
      ·
        refine ⟨47536314750099053186916169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253527012000528283663552901 47536314750099053186916169)
        ·
          refine ⟨35652236062574289890187127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47536314750099053186916169 35652236062574289890187127)
          ·
            refine ⟨53478354093861434835280691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35652236062574289890187127 53478354093861434835280691)
            ·
              refine ⟨80217531140792152252921037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53478354093861434835280691 80217531140792152252921037)
              ·
                refine ⟨30081574177797057094845389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80217531140792152252921037 30081574177797057094845389)
                ·
                  refine ⟨11280590316673896410567021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30081574177797057094845389 11280590316673896410567021)
                  ·
                    refine ⟨4230221368752711153962633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11280590316673896410567021 4230221368752711153962633)
                    ·
                      refine ⟨3172666026564533365471975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230221368752711153962633 3172666026564533365471975)
                      ·
                        rfl

theorem cell23_6178745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6178745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178745 prefixEnd_6178745 := by exact prefixLift 6178745
  have htrace : WordTrace (prefixWord ++ tailWord_6178745) baseStart_6178745 baseEnd_6178745 := by
    simpa [prefixWord, tailWord_6178745, baseEnd_6178745] using wordTrace_append hprefix tailTrace_6178745
  have hstable : (prefixWord ++ tailWord_6178745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178745).length < 2 ^ (prefixWord ++ tailWord_6178745).sum := by decide
  have hdescent : baseEnd_6178745 < baseStart_6178745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178751 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 8]
def baseStart_6178751 : Nat := 118140960795 + 6178751 * 2 ^ 59
def prefixEnd_6178751 : Nat := 4983230072969 + 3 ^ 40 * 6178751 * 2
def baseEnd_6178751 : Nat := 1057556369149486780665649

theorem tailTrace_6178751 : CollatzResearch.WordTrace tailWord_6178751 prefixEnd_6178751 1057556369149486780665649 := by
  unfold tailWord_6178751
  simp only [CollatzResearch.WordTrace]
  refine ⟨225357562838447848503432107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150238375225631899002288071 225357562838447848503432107)
  ·
    refine ⟨338036344257671772755148161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225357562838447848503432107 338036344257671772755148161)
    ·
      refine ⟨253527258193253829566361121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338036344257671772755148161 253527258193253829566361121)
      ·
        refine ⟨190145443644940372174770841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253527258193253829566361121 190145443644940372174770841)
        ·
          refine ⟨142609082733705279131078131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190145443644940372174770841 142609082733705279131078131)
          ·
            refine ⟨213913624100557918696617197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142609082733705279131078131 213913624100557918696617197)
            ·
              refine ⟨80217609037709219511231449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213913624100557918696617197 80217609037709219511231449)
              ·
                refine ⟨60163206778281914633423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80217609037709219511231449 60163206778281914633423587)
                ·
                  refine ⟨90244810167422871950135381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60163206778281914633423587 90244810167422871950135381)
                  ·
                    refine ⟨1057556369149486780665649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90244810167422871950135381 1057556369149486780665649)
                    ·
                      rfl

theorem cell23_6178751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_6178751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178751 prefixEnd_6178751 := by exact prefixLift 6178751
  have htrace : WordTrace (prefixWord ++ tailWord_6178751) baseStart_6178751 baseEnd_6178751 := by
    simpa [prefixWord, tailWord_6178751, baseEnd_6178751] using wordTrace_append hprefix tailTrace_6178751
  have hstable : (prefixWord ++ tailWord_6178751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178751).length < 2 ^ (prefixWord ++ tailWord_6178751).sum := by decide
  have hdescent : baseEnd_6178751 < baseStart_6178751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178786 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6178786 : Nat := 118140960795 + 6178786 * 2 ^ 59
def prefixEnd_6178786 : Nat := 4983230072969 + 3 ^ 40 * 6178786 * 2
def baseEnd_6178786 : Nat := 3172687079271367705059287

theorem tailTrace_6178786 : CollatzResearch.WordTrace tailWord_6178786 prefixEnd_6178786 3172687079271367705059287 := by
  unfold tailWord_6178786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56339709848330262370239053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150239226262214032987304141 56339709848330262370239053)
  ·
    refine ⟨21127391193123848388839645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56339709848330262370239053 21127391193123848388839645)
    ·
      refine ⟨7922771697421443145814867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21127391193123848388839645 7922771697421443145814867)
      ·
        refine ⟨11884157546132164718722301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922771697421443145814867 11884157546132164718722301)
        ·
          refine ⟨4456559079799561769520863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11884157546132164718722301 4456559079799561769520863)
          ·
            refine ⟨6684838619699342654281295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456559079799561769520863 6684838619699342654281295)
            ·
              refine ⟨10027257929549013981421943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684838619699342654281295 10027257929549013981421943)
              ·
                refine ⟨15040886894323520972132915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027257929549013981421943 15040886894323520972132915)
                ·
                  refine ⟨22561330341485281458199373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15040886894323520972132915 22561330341485281458199373)
                  ·
                    refine ⟨8460498878056980546824765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22561330341485281458199373 8460498878056980546824765)
                    ·
                      refine ⟨3172687079271367705059287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460498878056980546824765 3172687079271367705059287)
                      ·
                        rfl

theorem cell23_6178786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6178786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178786 prefixEnd_6178786 := by exact prefixLift 6178786
  have htrace : WordTrace (prefixWord ++ tailWord_6178786) baseStart_6178786 baseEnd_6178786 := by
    simpa [prefixWord, tailWord_6178786, baseEnd_6178786] using wordTrace_append hprefix tailTrace_6178786
  have hstable : (prefixWord ++ tailWord_6178786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178786).length < 2 ^ (prefixWord ++ tailWord_6178786).sum := by decide
  have hdescent : baseEnd_6178786 < baseStart_6178786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178788 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_6178788 : Nat := 118140960795 + 6178788 * 2 ^ 59
def prefixEnd_6178788 : Nat := 4983230072969 + 3 ^ 40 * 6178788 * 2
def baseEnd_6178788 : Nat := 3172688106232676697234277

theorem tailTrace_6178788 : CollatzResearch.WordTrace tailWord_6178788 prefixEnd_6178788 3172688106232676697234277 := by
  unfold tailWord_6178788
  simp only [CollatzResearch.WordTrace]
  refine ⟨112679456169656901911264509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150239274892875869215019345 112679456169656901911264509)
  ·
    refine ⟨42254796063621338216724191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112679456169656901911264509 42254796063621338216724191)
    ·
      refine ⟨63382194095432007325086287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42254796063621338216724191 63382194095432007325086287)
      ·
        refine ⟨95073291143148010987629431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63382194095432007325086287 95073291143148010987629431)
        ·
          refine ⟨142609936714722016481444147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95073291143148010987629431 142609936714722016481444147)
          ·
            refine ⟨213914905072083024722166221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142609936714722016481444147 213914905072083024722166221)
            ·
              refine ⟨80218089402031134270812333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213914905072083024722166221 80218089402031134270812333)
              ·
                refine ⟨30081783525761675351554625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80218089402031134270812333 30081783525761675351554625)
                ·
                  refine ⟨22561337644321256513665969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30081783525761675351554625 22561337644321256513665969)
                  ·
                    refine ⟨16921003233240942385249477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22561337644321256513665969 16921003233240942385249477)
                    ·
                      refine ⟨3172688106232676697234277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16921003233240942385249477 3172688106232676697234277)
                      ·
                        rfl

theorem cell23_6178788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_6178788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178788 prefixEnd_6178788 := by exact prefixLift 6178788
  have htrace : WordTrace (prefixWord ++ tailWord_6178788) baseStart_6178788 baseEnd_6178788 := by
    simpa [prefixWord, tailWord_6178788, baseEnd_6178788] using wordTrace_append hprefix tailTrace_6178788
  have hstable : (prefixWord ++ tailWord_6178788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178788).length < 2 ^ (prefixWord ++ tailWord_6178788).sum := by decide
  have hdescent : baseEnd_6178788 < baseStart_6178788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178808 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_6178808 : Nat := 118140960795 + 6178808 * 2 ^ 59
def prefixEnd_6178808 : Nat := 4983230072969 + 3 ^ 40 * 6178808 * 2
def baseEnd_6178808 : Nat := 3172698375845766618984185

theorem tailTrace_6178808 : CollatzResearch.WordTrace tailWord_6178808 prefixEnd_6178808 3172698375845766618984185 := by
  unfold tailWord_6178808
  simp only [CollatzResearch.WordTrace]
  refine ⟨112679820899620673619128539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150239761199494231492171385 112679820899620673619128539)
  ·
    refine ⟨169019731349431010428692809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112679820899620673619128539 169019731349431010428692809)
    ·
      refine ⟨126764798512073257821519607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169019731349431010428692809 126764798512073257821519607)
      ·
        refine ⟨190147197768109886732279411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126764798512073257821519607 190147197768109886732279411)
        ·
          refine ⟨285220796652164830098419117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190147197768109886732279411 285220796652164830098419117)
          ·
            refine ⟨106957798744561811286907169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285220796652164830098419117 106957798744561811286907169)
            ·
              refine ⟨80218349058421358465180377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106957798744561811286907169 80218349058421358465180377)
              ·
                refine ⟨60163761793816018848885283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80218349058421358465180377 60163761793816018848885283)
                ·
                  refine ⟨90245642690724028273327925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60163761793816018848885283 90245642690724028273327925)
                  ·
                    refine ⟨8460529002255377650624493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90245642690724028273327925 8460529002255377650624493)
                    ·
                      refine ⟨3172698375845766618984185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460529002255377650624493 3172698375845766618984185)
                      ·
                        rfl

theorem cell23_6178808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_6178808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178808 prefixEnd_6178808 := by exact prefixLift 6178808
  have htrace : WordTrace (prefixWord ++ tailWord_6178808) baseStart_6178808 baseEnd_6178808 := by
    simpa [prefixWord, tailWord_6178808, baseEnd_6178808] using wordTrace_append hprefix tailTrace_6178808
  have hstable : (prefixWord ++ tailWord_6178808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178808).length < 2 ^ (prefixWord ++ tailWord_6178808).sum := by decide
  have hdescent : baseEnd_6178808 < baseStart_6178808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178862 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_6178862 : Nat := 118140960795 + 6178862 * 2 ^ 59
def prefixEnd_6178862 : Nat := 4983230072969 + 3 ^ 40 * 6178862 * 2
def baseEnd_6178862 : Nat := 1057575367933703135902979

theorem tailTrace_6178862 : CollatzResearch.WordTrace tailWord_6178862 prefixEnd_6178862 1057575367933703135902979 := by
  unfold tailWord_6178862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170201417630714307590355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150241074227363809640481893 28170201417630714307590355)
  ·
    refine ⟨42255302126446071461385533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28170201417630714307590355 42255302126446071461385533)
    ·
      refine ⟨15845738297417276798019575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42255302126446071461385533 15845738297417276798019575)
      ·
        refine ⟨23768607446125915197029363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15845738297417276798019575 23768607446125915197029363)
        ·
          refine ⟨35652911169188872795544045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23768607446125915197029363 35652911169188872795544045)
          ·
            refine ⟨13369841688445827298329017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35652911169188872795544045 13369841688445827298329017)
            ·
              refine ⟨10027381266334370473746763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369841688445827298329017 10027381266334370473746763)
              ·
                refine ⟨15041071899501555710620145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027381266334370473746763 15041071899501555710620145)
                ·
                  refine ⟨11280803924626166782965109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15041071899501555710620145 11280803924626166782965109)
                  ·
                    refine ⟨1057575367933703135902979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11280803924626166782965109 1057575367933703135902979)
                    ·
                      rfl

theorem cell23_6178862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_6178862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178862 prefixEnd_6178862 := by exact prefixLift 6178862
  have htrace : WordTrace (prefixWord ++ tailWord_6178862) baseStart_6178862 baseEnd_6178862 := by
    simpa [prefixWord, tailWord_6178862, baseEnd_6178862] using wordTrace_append hprefix tailTrace_6178862
  have hstable : (prefixWord ++ tailWord_6178862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178862).length < 2 ^ (prefixWord ++ tailWord_6178862).sum := by decide
  have hdescent : baseEnd_6178862 < baseStart_6178862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178865 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6178865 : Nat := 118140960795 + 6178865 * 2 ^ 59
def prefixEnd_6178865 : Nat := 4983230072969 + 3 ^ 40 * 6178865 * 2
def baseEnd_6178865 : Nat := 3172727644243072895971423

theorem tailTrace_6178865 : CollatzResearch.WordTrace tailWord_6178865 prefixEnd_6178865 3172727644243072895971423 := by
  unfold tailWord_6178865
  simp only [CollatzResearch.WordTrace]
  refine ⟨225361720760034845973082049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150241147173356563982054699 225361720760034845973082049)
  ·
    refine ⟨169021290570026134479811537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225361720760034845973082049 169021290570026134479811537)
    ·
      refine ⟨126765967927519600859858653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169021290570026134479811537 126765967927519600859858653)
      ·
        refine ⟨47537237972819850322446995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126765967927519600859858653 47537237972819850322446995)
        ·
          refine ⟨71305856959229775483670493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47537237972819850322446995 71305856959229775483670493)
          ·
            refine ⟨26739696359711165806376435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71305856959229775483670493 26739696359711165806376435)
            ·
              refine ⟨40109544539566748709564653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26739696359711165806376435 40109544539566748709564653)
              ·
                refine ⟨15041079202337530766086745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40109544539566748709564653 15041079202337530766086745)
                ·
                  refine ⟨11280809401753148074565059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15041079202337530766086745 11280809401753148074565059)
                  ·
                    refine ⟨16921214102629722111847589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11280809401753148074565059 16921214102629722111847589)
                    ·
                      refine ⟨3172727644243072895971423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16921214102629722111847589 3172727644243072895971423)
                      ·
                        rfl

theorem cell23_6178865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6178865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178865 prefixEnd_6178865 := by exact prefixLift 6178865
  have htrace : WordTrace (prefixWord ++ tailWord_6178865) baseStart_6178865 baseEnd_6178865 := by
    simpa [prefixWord, tailWord_6178865, baseEnd_6178865] using wordTrace_append hprefix tailTrace_6178865
  have hstable : (prefixWord ++ tailWord_6178865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178865).length < 2 ^ (prefixWord ++ tailWord_6178865).sum := by decide
  have hdescent : baseEnd_6178865 < baseStart_6178865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178909 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6178909 : Nat := 118140960795 + 6178909 * 2 ^ 59
def prefixEnd_6178909 : Nat := 4983230072969 + 3 ^ 40 * 6178909 * 2
def baseEnd_6178909 : Nat := 1057583412463956907940407

theorem tailTrace_6178909 : CollatzResearch.WordTrace tailWord_6178909 prefixEnd_6178909 1057583412463956907940407 := by
  unfold tailWord_6178909
  simp only [CollatzResearch.WordTrace]
  refine ⟨225363325571875441487683781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150242217047916960991789187 225363325571875441487683781)
  ·
    refine ⟨42255623544726645278940709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225363325571875441487683781 42255623544726645278940709)
    ·
      refine ⟨7922929414636245989801383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42255623544726645278940709 7922929414636245989801383)
      ·
        refine ⟨11884394121954368984702075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922929414636245989801383 11884394121954368984702075)
        ·
          refine ⟨17826591182931553477053113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884394121954368984702075 17826591182931553477053113)
          ·
            refine ⟨13369943387198665107789835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17826591182931553477053113 13369943387198665107789835)
            ·
              refine ⟨20054915080797997661684753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13369943387198665107789835 20054915080797997661684753)
              ·
                refine ⟨15041186310598498246263565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20054915080797997661684753 15041186310598498246263565)
                ·
                  refine ⟨5640444866474436842348837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15041186310598498246263565 5640444866474436842348837)
                  ·
                    refine ⟨1057583412463956907940407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640444866474436842348837 1057583412463956907940407)
                    ·
                      rfl

theorem cell23_6178909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6178909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178909 prefixEnd_6178909 := by exact prefixLift 6178909
  have htrace : WordTrace (prefixWord ++ tailWord_6178909) baseStart_6178909 baseEnd_6178909 := by
    simpa [prefixWord, tailWord_6178909, baseEnd_6178909] using wordTrace_append hprefix tailTrace_6178909
  have hstable : (prefixWord ++ tailWord_6178909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178909).length < 2 ^ (prefixWord ++ tailWord_6178909).sum := by decide
  have hdescent : baseEnd_6178909 < baseStart_6178909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178949 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_6178949 : Nat := 118140960795 + 6178949 * 2 ^ 59
def prefixEnd_6178949 : Nat := 4983230072969 + 3 ^ 40 * 6178949 * 2
def baseEnd_6178949 : Nat := 3172770776618050567321037

theorem tailTrace_6178949 : CollatzResearch.WordTrace tailWord_6178949 prefixEnd_6178949 3172770776618050567321037 := by
  unfold tailWord_6178949
  simp only [CollatzResearch.WordTrace]
  refine ⟨225364784491730528319139901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150243189661153685546093267 225364784491730528319139901)
  ·
    refine ⟨84511794184398948119677463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225364784491730528319139901 84511794184398948119677463)
    ·
      refine ⟨126767691276598422179516195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84511794184398948119677463 126767691276598422179516195)
      ·
        refine ⟨190151536914897633269274293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126767691276598422179516195 190151536914897633269274293)
        ·
          refine ⟨17826706585771653118994465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190151536914897633269274293 17826706585771653118994465)
          ·
            refine ⟨13370029939328739839245849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17826706585771653118994465 13370029939328739839245849)
            ·
              refine ⟨10027522454496554879434387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13370029939328739839245849 10027522454496554879434387)
              ·
                refine ⟨15041283681744832319151581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027522454496554879434387 15041283681744832319151581)
                ·
                  refine ⟨5640481380654312119681843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15041283681744832319151581 5640481380654312119681843)
                  ·
                    refine ⟨8460722070981468179522765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640481380654312119681843 8460722070981468179522765)
                    ·
                      refine ⟨3172770776618050567321037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460722070981468179522765 3172770776618050567321037)
                      ·
                        rfl

theorem cell23_6178949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_6178949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178949 prefixEnd_6178949 := by exact prefixLift 6178949
  have htrace : WordTrace (prefixWord ++ tailWord_6178949) baseStart_6178949 baseEnd_6178949 := by
    simpa [prefixWord, tailWord_6178949, baseEnd_6178949] using wordTrace_append hprefix tailTrace_6178949
  have hstable : (prefixWord ++ tailWord_6178949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178949).length < 2 ^ (prefixWord ++ tailWord_6178949).sum := by decide
  have hdescent : baseEnd_6178949 < baseStart_6178949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178972 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6178972 : Nat := 118140960795 + 6178972 * 2 ^ 59
def prefixEnd_6178972 : Nat := 4983230072969 + 3 ^ 40 * 6178972 * 2
def baseEnd_6178972 : Nat := 3172782586673103977333431

theorem tailTrace_6178972 : CollatzResearch.WordTrace tailWord_6178972 prefixEnd_6178972 3172782586673103977333431 := by
  unfold tailWord_6178972
  simp only [CollatzResearch.WordTrace]
  refine ⟨112682811685323601623613585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150243748913764802164818113 112682811685323601623613585)
  ·
    refine ⟨84512108763992701217710189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112682811685323601623613585 84512108763992701217710189)
    ·
      refine ⟨31692040786497262956641321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84512108763992701217710189 31692040786497262956641321)
      ·
        refine ⟨23769030589872947217480991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31692040786497262956641321 23769030589872947217480991)
        ·
          refine ⟨35653545884809420826221487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23769030589872947217480991 35653545884809420826221487)
          ·
            refine ⟨53480318827214131239332231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35653545884809420826221487 53480318827214131239332231)
            ·
              refine ⟨80220478240821196858998347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53480318827214131239332231 80220478240821196858998347)
              ·
                refine ⟨120330717361231795288497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80220478240821196858998347 120330717361231795288497521)
                ·
                  refine ⟨90248038020923846466373141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120330717361231795288497521 90248038020923846466373141)
                  ·
                    refine ⟨4230376782230805303111241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90248038020923846466373141 4230376782230805303111241)
                    ·
                      refine ⟨3172782586673103977333431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230376782230805303111241 3172782586673103977333431)
                      ·
                        rfl

theorem cell23_6178972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6178972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178972 prefixEnd_6178972 := by exact prefixLift 6178972
  have htrace : WordTrace (prefixWord ++ tailWord_6178972) baseStart_6178972 baseEnd_6178972 := by
    simpa [prefixWord, tailWord_6178972, baseEnd_6178972] using wordTrace_append hprefix tailTrace_6178972
  have hstable : (prefixWord ++ tailWord_6178972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178972).length < 2 ^ (prefixWord ++ tailWord_6178972).sum := by decide
  have hdescent : baseEnd_6178972 < baseStart_6178972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6178989 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6178989 : Nat := 118140960795 + 6178989 * 2 ^ 59
def prefixEnd_6178989 : Nat := 4983230072969 + 3 ^ 40 * 6178989 * 2
def baseEnd_6178989 : Nat := 3172791315844230410820853

theorem tailTrace_6178989 : CollatzResearch.WordTrace tailWord_6178989 prefixEnd_6178989 3172791315844230410820853 := by
  unfold tailWord_6178989
  simp only [CollatzResearch.WordTrace]
  refine ⟨225366243411585615150596021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150244162274390410100397347 225366243411585615150596021)
  ·
    refine ⟨21128085319836151420368377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225366243411585615150596021 21128085319836151420368377)
    ·
      refine ⟨15846063989877113565276283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21128085319836151420368377 15846063989877113565276283)
      ·
        refine ⟨23769095984815670347914425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846063989877113565276283 23769095984815670347914425)
        ·
          refine ⟨17826821988611752760935819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23769095984815670347914425 17826821988611752760935819)
          ·
            refine ⟨26740232982917629141403729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17826821988611752760935819 26740232982917629141403729)
            ·
              refine ⟨20055174737188221856052797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26740232982917629141403729 20055174737188221856052797)
              ·
                refine ⟨7520690526445583196019799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20055174737188221856052797 7520690526445583196019799)
                ·
                  refine ⟨11281035789668374794029699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520690526445583196019799 11281035789668374794029699)
                  ·
                    refine ⟨16921553684502562191044549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11281035789668374794029699 16921553684502562191044549)
                    ·
                      refine ⟨3172791315844230410820853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16921553684502562191044549 3172791315844230410820853)
                      ·
                        rfl

theorem cell23_6178989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6178989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6178989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6178989 prefixEnd_6178989 := by exact prefixLift 6178989
  have htrace : WordTrace (prefixWord ++ tailWord_6178989) baseStart_6178989 baseEnd_6178989 := by
    simpa [prefixWord, tailWord_6178989, baseEnd_6178989] using wordTrace_append hprefix tailTrace_6178989
  have hstable : (prefixWord ++ tailWord_6178989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6178989).length < 2 ^ (prefixWord ++ tailWord_6178989).sum := by decide
  have hdescent : baseEnd_6178989 < baseStart_6178989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6178989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179012 : List Nat := [2, 3, 3, 1, 2, 2, 2, 8]
def baseStart_6179012 : Nat := 118140960795 + 6179012 * 2 ^ 59
def prefixEnd_6179012 : Nat := 4983230072969 + 3 ^ 40 * 6179012 * 2
def baseEnd_6179012 : Nat := 117511226885158660030861

theorem tailTrace_6179012 : CollatzResearch.WordTrace tailWord_6179012 prefixEnd_6179012 117511226885158660030861 := by
  unfold tailWord_6179012
  simp only [CollatzResearch.WordTrace]
  refine ⟨112683541145251145039341645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150244721527001526719122193 112683541145251145039341645)
  ·
    refine ⟨42256327929469179389753117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112683541145251145039341645 42256327929469179389753117)
    ·
      refine ⟨15846122973550942271157419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42256327929469179389753117 15846122973550942271157419)
      ·
        refine ⟨23769184460326413406736129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846122973550942271157419 23769184460326413406736129)
        ·
          refine ⟨17826888345244810055052097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23769184460326413406736129 17826888345244810055052097)
          ·
            refine ⟨13370166258933607541289073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17826888345244810055052097 13370166258933607541289073)
            ·
              refine ⟨10027624694200205655966805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13370166258933607541289073 10027624694200205655966805)
              ·
                refine ⟨117511226885158660030861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10027624694200205655966805 117511226885158660030861)
                ·
                  rfl

theorem cell23_6179012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 8].length) (baseStart_6179012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179012 prefixEnd_6179012 := by exact prefixLift 6179012
  have htrace : WordTrace (prefixWord ++ tailWord_6179012) baseStart_6179012 baseEnd_6179012 := by
    simpa [prefixWord, tailWord_6179012, baseEnd_6179012] using wordTrace_append hprefix tailTrace_6179012
  have hstable : (prefixWord ++ tailWord_6179012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179012).length < 2 ^ (prefixWord ++ tailWord_6179012).sum := by decide
  have hdescent : baseEnd_6179012 < baseStart_6179012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179026 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6179026 : Nat := 118140960795 + 6179026 * 2 ^ 59
def prefixEnd_6179026 : Nat := 4983230072969 + 3 ^ 40 * 6179026 * 2
def baseEnd_6179026 : Nat := 3172810314628446766058183

theorem tailTrace_6179026 : CollatzResearch.WordTrace tailWord_6179026 prefixEnd_6179026 3172810314628446766058183 := by
  unfold tailWord_6179026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56341898228112892617423233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150245061941634380313128621 56341898228112892617423233)
  ·
    refine ⟨42256423671084669463067425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56341898228112892617423233 42256423671084669463067425)
    ·
      refine ⟨31692317753313502097300569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42256423671084669463067425 31692317753313502097300569)
      ·
        refine ⟨23769238314985126572975427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31692317753313502097300569 23769238314985126572975427)
        ·
          refine ⟨35653857472477689859463141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23769238314985126572975427 35653857472477689859463141)
          ·
            refine ⟨6685098276089566848649339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35653857472477689859463141 6685098276089566848649339)
            ·
              refine ⟨10027647414134350272974009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6685098276089566848649339 10027647414134350272974009)
              ·
                refine ⟨7520735560600762704730507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10027647414134350272974009 7520735560600762704730507)
                ·
                  refine ⟨11281103340901144057095761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520735560600762704730507 11281103340901144057095761)
                  ·
                    refine ⟨8460827505675858042821821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11281103340901144057095761 8460827505675858042821821)
                    ·
                      refine ⟨3172810314628446766058183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460827505675858042821821 3172810314628446766058183)
                      ·
                        rfl

theorem cell23_6179026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6179026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179026 prefixEnd_6179026 := by exact prefixLift 6179026
  have htrace : WordTrace (prefixWord ++ tailWord_6179026) baseStart_6179026 baseEnd_6179026 := by
    simpa [prefixWord, tailWord_6179026, baseEnd_6179026] using wordTrace_append hprefix tailTrace_6179026
  have hstable : (prefixWord ++ tailWord_6179026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179026).length < 2 ^ (prefixWord ++ tailWord_6179026).sum := by decide
  have hdescent : baseEnd_6179026 < baseStart_6179026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179036 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6179036 : Nat := 118140960795 + 6179036 * 2 ^ 59
def prefixEnd_6179036 : Nat := 4983230072969 + 3 ^ 40 * 6179036 * 2
def baseEnd_6179036 : Nat := 3172815449434991726933137

theorem tailTrace_6179036 : CollatzResearch.WordTrace tailWord_6179036 prefixEnd_6179036 3172815449434991726933137 := by
  unfold tailWord_6179036
  simp only [CollatzResearch.WordTrace]
  refine ⟨112683978821207671088778481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150245305094943561451704641 112683978821207671088778481)
  ·
    refine ⟨84512984115905753316583861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112683978821207671088778481 84512984115905753316583861)
    ·
      refine ⟨7923092260866164373429737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84512984115905753316583861 7923092260866164373429737)
      ·
        refine ⟨5942319195649623280072303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7923092260866164373429737 5942319195649623280072303)
        ·
          refine ⟨8913478793474434920108455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942319195649623280072303 8913478793474434920108455)
          ·
            refine ⟨13370218190211652380162683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913478793474434920108455 13370218190211652380162683)
            ·
              refine ⟨20055327285317478570244025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13370218190211652380162683 20055327285317478570244025)
              ·
                refine ⟨15041495463988108927683019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20055327285317478570244025 15041495463988108927683019)
                ·
                  refine ⟨22562243195982163391524529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15041495463988108927683019 22562243195982163391524529)
                  ·
                    refine ⟨16921682396986622543643397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22562243195982163391524529 16921682396986622543643397)
                    ·
                      refine ⟨3172815449434991726933137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16921682396986622543643397 3172815449434991726933137)
                      ·
                        rfl

theorem cell23_6179036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6179036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179036 prefixEnd_6179036 := by exact prefixLift 6179036
  have htrace : WordTrace (prefixWord ++ tailWord_6179036) baseStart_6179036 baseEnd_6179036 := by
    simpa [prefixWord, tailWord_6179036, baseEnd_6179036] using wordTrace_append hprefix tailTrace_6179036
  have hstable : (prefixWord ++ tailWord_6179036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179036).length < 2 ^ (prefixWord ++ tailWord_6179036).sum := by decide
  have hdescent : baseEnd_6179036 < baseStart_6179036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179043 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6179043 : Nat := 118140960795 + 6179043 * 2 ^ 59
def prefixEnd_6179043 : Nat := 4983230072969 + 3 ^ 40 * 6179043 * 2
def baseEnd_6179043 : Nat := 3172819043799573199545605

theorem tailTrace_6179043 : CollatzResearch.WordTrace tailWord_6179043 prefixEnd_6179043 3172819043799573199545605 := by
  unfold tailWord_6179043
  simp only [CollatzResearch.WordTrace]
  refine ⟨225368212953389982373061783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150245475302259988248707855 225368212953389982373061783)
  ·
    refine ⟨338052319430084973559592675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225368212953389982373061783 338052319430084973559592675)
    ·
      refine ⟨507078479145127460339389013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338052319430084973559592675 507078479145127460339389013)
      ·
        refine ⟨5942325927481962425852215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 507078479145127460339389013 5942325927481962425852215)
        ·
          refine ⟨8913488891222943638778323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942325927481962425852215 8913488891222943638778323)
          ·
            refine ⟨13370233336834415458167485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913488891222943638778323 13370233336834415458167485)
            ·
              refine ⟨5013837501312905796812807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370233336834415458167485 5013837501312905796812807)
              ·
                refine ⟨7520756251969358695219211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013837501312905796812807 7520756251969358695219211)
                ·
                  refine ⟨11281134377954038042828817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7520756251969358695219211 11281134377954038042828817)
                  ·
                    refine ⟨8460850783465528532121613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11281134377954038042828817 8460850783465528532121613)
                    ·
                      refine ⟨3172819043799573199545605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460850783465528532121613 3172819043799573199545605)
                      ·
                        rfl

theorem cell23_6179043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6179043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179043 prefixEnd_6179043 := by exact prefixLift 6179043
  have htrace : WordTrace (prefixWord ++ tailWord_6179043) baseStart_6179043 baseEnd_6179043 := by
    simpa [prefixWord, tailWord_6179043, baseEnd_6179043] using wordTrace_append hprefix tailTrace_6179043
  have hstable : (prefixWord ++ tailWord_6179043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179043).length < 2 ^ (prefixWord ++ tailWord_6179043).sum := by decide
  have hdescent : baseEnd_6179043 < baseStart_6179043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179062 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6179062 : Nat := 118140960795 + 6179062 * 2 ^ 59
def prefixEnd_6179062 : Nat := 4983230072969 + 3 ^ 40 * 6179062 * 2
def baseEnd_6179062 : Nat := 3172828799932008625208017

theorem tailTrace_6179062 : CollatzResearch.WordTrace tailWord_6179062 prefixEnd_6179062 3172828799932008625208017 := by
  unfold tailWord_6179062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085556621270071788625215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150245937293547432412002293 14085556621270071788625215)
  ·
    refine ⟨21128334931905107682937823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14085556621270071788625215 21128334931905107682937823)
    ·
      refine ⟨31692502397857661524406735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21128334931905107682937823 31692502397857661524406735)
      ·
        refine ⟨47538753596786492286610103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31692502397857661524406735 47538753596786492286610103)
        ·
          refine ⟨71308130395179738429915155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47538753596786492286610103 71308130395179738429915155)
          ·
            refine ⟨106962195592769607644872733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71308130395179738429915155 106962195592769607644872733)
            ·
              refine ⟨40110823347288602866827275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106962195592769607644872733 40110823347288602866827275)
              ·
                refine ⟨60166235020932904300240913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40110823347288602866827275 60166235020932904300240913)
                ·
                  refine ⟨45124676265699678225180685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60166235020932904300240913 45124676265699678225180685)
                  ·
                    refine ⟨16921753599637379334442757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45124676265699678225180685 16921753599637379334442757)
                    ·
                      refine ⟨3172828799932008625208017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16921753599637379334442757 3172828799932008625208017)
                      ·
                        rfl

theorem cell23_6179062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6179062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179062 prefixEnd_6179062 := by exact prefixLift 6179062
  have htrace : WordTrace (prefixWord ++ tailWord_6179062) baseStart_6179062 baseEnd_6179062 := by
    simpa [prefixWord, tailWord_6179062, baseEnd_6179062] using wordTrace_append hprefix tailTrace_6179062
  have hstable : (prefixWord ++ tailWord_6179062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179062).length < 2 ^ (prefixWord ++ tailWord_6179062).sum := by decide
  have hdescent : baseEnd_6179062 < baseStart_6179062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6179065 : Nat := 118140960795 + 6179065 * 2 ^ 59
def prefixEnd_6179065 : Nat := 4983230072969 + 3 ^ 40 * 6179065 * 2
def baseEnd_6179065 : Nat := 3172830340373972113470503

theorem tailTrace_6179065 : CollatzResearch.WordTrace tailWord_6179065 prefixEnd_6179065 3172830340373972113470503 := by
  unfold tailWord_6179065
  simp only [CollatzResearch.WordTrace]
  refine ⟨225369015359310280130362649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150246010239540186753575099 225369015359310280130362649)
  ·
    refine ⟨169026761519482710097771987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225369015359310280130362649 169026761519482710097771987)
    ·
      refine ⟨253540142279224065146657981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169026761519482710097771987 253540142279224065146657981)
      ·
        refine ⟨95077553354709024429996743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253540142279224065146657981 95077553354709024429996743)
        ·
          refine ⟨142616330032063536644995115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95077553354709024429996743 142616330032063536644995115)
          ·
            refine ⟨213924495048095304967492673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142616330032063536644995115 213924495048095304967492673)
            ·
              refine ⟨160443371286071478725619505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213924495048095304967492673 160443371286071478725619505)
              ·
                refine ⟨120332528464553609044214629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160443371286071478725619505 120332528464553609044214629)
                ·
                  refine ⟨22562349087103801695790243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120332528464553609044214629 22562349087103801695790243)
                  ·
                    refine ⟨33843523630655702543685365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22562349087103801695790243 33843523630655702543685365)
                    ·
                      refine ⟨3172830340373972113470503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33843523630655702543685365 3172830340373972113470503)
                      ·
                        rfl

theorem cell23_6179065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6179065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179065 prefixEnd_6179065 := by exact prefixLift 6179065
  have htrace : WordTrace (prefixWord ++ tailWord_6179065) baseStart_6179065 baseEnd_6179065 := by
    simpa [prefixWord, tailWord_6179065, baseEnd_6179065] using wordTrace_append hprefix tailTrace_6179065
  have hstable : (prefixWord ++ tailWord_6179065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179065).length < 2 ^ (prefixWord ++ tailWord_6179065).sum := by decide
  have hdescent : baseEnd_6179065 < baseStart_6179065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179129 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6179129 : Nat := 118140960795 + 6179129 * 2 ^ 59
def prefixEnd_6179129 : Nat := 4983230072969 + 3 ^ 40 * 6179129 * 2
def baseEnd_6179129 : Nat := 3172863203135859863070209

theorem tailTrace_6179129 : CollatzResearch.WordTrace tailWord_6179129 prefixEnd_6179129 3172863203135859863070209 := by
  unfold tailWord_6179129
  simp only [CollatzResearch.WordTrace]
  refine ⟨225371349631078419060692441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150247566420718946040461627 225371349631078419060692441)
  ·
    refine ⟨169028512223308814295519331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225371349631078419060692441 169028512223308814295519331)
    ·
      refine ⟨253542768334963221443278997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169028512223308814295519331 253542768334963221443278997)
      ·
        refine ⟨11884817265701401005153703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253542768334963221443278997 11884817265701401005153703)
        ·
          refine ⟨17827225898552101507730555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884817265701401005153703 17827225898552101507730555)
          ·
            refine ⟨26740838847828152261595833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17827225898552101507730555 26740838847828152261595833)
            ·
              refine ⟨20055629135871114196196875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26740838847828152261595833 20055629135871114196196875)
              ·
                refine ⟨30083443703806671294295313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20055629135871114196196875 30083443703806671294295313)
                ·
                  refine ⟨22562582777855003470721485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30083443703806671294295313 22562582777855003470721485)
                  ·
                    refine ⟨8460968541695626301520557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22562582777855003470721485 8460968541695626301520557)
                    ·
                      refine ⟨3172863203135859863070209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8460968541695626301520557 3172863203135859863070209)
                      ·
                        rfl

theorem cell23_6179129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6179129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179129 prefixEnd_6179129 := by exact prefixLift 6179129
  have htrace : WordTrace (prefixWord ++ tailWord_6179129) baseStart_6179129 baseEnd_6179129 := by
    simpa [prefixWord, tailWord_6179129, baseEnd_6179129] using wordTrace_append hprefix tailTrace_6179129
  have hstable : (prefixWord ++ tailWord_6179129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179129).length < 2 ^ (prefixWord ++ tailWord_6179129).sum := by decide
  have hdescent : baseEnd_6179129 < baseStart_6179129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179145 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_6179145 : Nat := 118140960795 + 6179145 * 2 ^ 59
def prefixEnd_6179145 : Nat := 4983230072969 + 3 ^ 40 * 6179145 * 2
def baseEnd_6179145 : Nat := 1057623806275443933490045

theorem tailTrace_6179145 : CollatzResearch.WordTrace tailWord_6179145 prefixEnd_6179145 1057623806275443933490045 := by
  unfold tailWord_6179145
  simp only [CollatzResearch.WordTrace]
  refine ⟨225371933199020453793274889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150247955466013635862183259 225371933199020453793274889)
  ·
    refine ⟨169028949899265340344956167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225371933199020453793274889 169028949899265340344956167)
    ·
      refine ⟨253543424848898010517434251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169028949899265340344956167 253543424848898010517434251)
      ·
        refine ⟨380315137273347015776151377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253543424848898010517434251 380315137273347015776151377)
        ·
          refine ⟨285236352955010261832113533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380315137273347015776151377 285236352955010261832113533)
          ·
            refine ⟨106963632358128848187042575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285236352955010261832113533 106963632358128848187042575)
            ·
              refine ⟨160445448537193272280563863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106963632358128848187042575 160445448537193272280563863)
              ·
                refine ⟨240668172805789908420845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160445448537193272280563863 240668172805789908420845795)
                ·
                  refine ⟨361002259208684862631268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240668172805789908420845795 361002259208684862631268693)
                  ·
                    refine ⟨1057623806275443933490045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 361002259208684862631268693 1057623806275443933490045)
                    ·
                      rfl

theorem cell23_6179145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_6179145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179145 prefixEnd_6179145 := by exact prefixLift 6179145
  have htrace : WordTrace (prefixWord ++ tailWord_6179145) baseStart_6179145 baseEnd_6179145 := by
    simpa [prefixWord, tailWord_6179145, baseEnd_6179145] using wordTrace_append hprefix tailTrace_6179145
  have hstable : (prefixWord ++ tailWord_6179145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179145).length < 2 ^ (prefixWord ++ tailWord_6179145).sum := by decide
  have hdescent : baseEnd_6179145 < baseStart_6179145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179152 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_6179152 : Nat := 118140960795 + 6179152 * 2 ^ 59
def prefixEnd_6179152 : Nat := 4983230072969 + 3 ^ 40 * 6179152 * 2
def baseEnd_6179152 : Nat := 3172875013190913273082603

theorem tailTrace_6179152 : CollatzResearch.WordTrace tailWord_6179152 prefixEnd_6179152 3172875013190913273082603 := by
  unfold tailWord_6179152
  simp only [CollatzResearch.WordTrace]
  refine ⟨112686094254997546994389855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150248125673330062659186473 112686094254997546994389855)
  ·
    refine ⟨169029141382496320491584783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112686094254997546994389855 169029141382496320491584783)
    ·
      refine ⟨253543712073744480737377175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169029141382496320491584783 253543712073744480737377175)
      ·
        refine ⟨380315568110616721106065763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253543712073744480737377175 380315568110616721106065763)
        ·
          refine ⟨570473352165925081659098645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380315568110616721106065763 570473352165925081659098645)
          ·
            refine ⟨26740938382777738202770249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 570473352165925081659098645 26740938382777738202770249)
            ·
              refine ⟨20055703787083303652077687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26740938382777738202770249 20055703787083303652077687)
              ·
                refine ⟨30083555680624955478116531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20055703787083303652077687 30083555680624955478116531)
                ·
                  refine ⟨45125333520937433217174797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30083555680624955478116531 45125333520937433217174797)
                  ·
                    refine ⟨16922000070351537456440549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45125333520937433217174797 16922000070351537456440549)
                    ·
                      refine ⟨3172875013190913273082603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16922000070351537456440549 3172875013190913273082603)
                      ·
                        rfl

theorem cell23_6179152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_6179152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179152 prefixEnd_6179152 := by exact prefixLift 6179152
  have htrace : WordTrace (prefixWord ++ tailWord_6179152) baseStart_6179152 baseEnd_6179152 := by
    simpa [prefixWord, tailWord_6179152, baseEnd_6179152] using wordTrace_append hprefix tailTrace_6179152
  have hstable : (prefixWord ++ tailWord_6179152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179152).length < 2 ^ (prefixWord ++ tailWord_6179152).sum := by decide
  have hdescent : baseEnd_6179152 < baseStart_6179152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179230 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6179230 : Nat := 118140960795 + 6179230 * 2 ^ 59
def prefixEnd_6179230 : Nat := 4983230072969 + 3 ^ 40 * 6179230 * 2
def baseEnd_6179230 : Nat := 1057638354893987989302415

theorem tailTrace_6179230 : CollatzResearch.WordTrace tailWord_6179230 prefixEnd_6179230 1057638354893987989302415 := by
  unfold tailWord_6179230
  simp only [CollatzResearch.WordTrace]
  refine ⟨28171879175464064163764893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150250022269141675540079429 28171879175464064163764893)
  ·
    refine ⟨10564454690799024061411835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28171879175464064163764893 10564454690799024061411835)
    ·
      refine ⟨15846682036198536092117753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564454690799024061411835 15846682036198536092117753)
      ·
        refine ⟨11885011527148902069088315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15846682036198536092117753 11885011527148902069088315)
        ·
          refine ⟨17827517290723353103632473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11885011527148902069088315 17827517290723353103632473)
          ·
            refine ⟨13370637968042514827724355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17827517290723353103632473 13370637968042514827724355)
            ·
              refine ⟨20055956952063772241586533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13370637968042514827724355 20055956952063772241586533)
              ·
                refine ⟨3760491928511957295297475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20055956952063772241586533 3760491928511957295297475)
                ·
                  refine ⟨5640737892767935942946213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760491928511957295297475 5640737892767935942946213)
                  ·
                    refine ⟨1057638354893987989302415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640737892767935942946213 1057638354893987989302415)
                    ·
                      rfl

theorem cell23_6179230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6179230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179230 prefixEnd_6179230 := by exact prefixLift 6179230
  have htrace : WordTrace (prefixWord ++ tailWord_6179230) baseStart_6179230 baseEnd_6179230 := by
    simpa [prefixWord, tailWord_6179230, baseEnd_6179230] using wordTrace_append hprefix tailTrace_6179230
  have hstable : (prefixWord ++ tailWord_6179230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179230).length < 2 ^ (prefixWord ++ tailWord_6179230).sum := by decide
  have hdescent : baseEnd_6179230 < baseStart_6179230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179239 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 3, 5]
def baseStart_6179239 : Nat := 118140960795 + 6179239 * 2 ^ 59
def prefixEnd_6179239 : Nat := 4983230072969 + 3 ^ 40 * 6179239 * 2
def baseEnd_6179239 : Nat := 1057639895335951477564901

theorem tailTrace_6179239 : CollatzResearch.WordTrace tailWord_6179239 prefixEnd_6179239 1057639895335951477564901 := by
  unfold tailWord_6179239
  simp only [CollatzResearch.WordTrace]
  refine ⟨225375361660679907847196771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150250241107119938564797847 225375361660679907847196771)
  ·
    refine ⟨338063042491019861770795157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225375361660679907847196771 338063042491019861770795157)
    ·
      refine ⟨15846705116766556020506023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 338063042491019861770795157 15846705116766556020506023)
      ·
        refine ⟨23770057675149834030759035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846705116766556020506023 23770057675149834030759035)
        ·
          refine ⟨35655086512724751046138553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23770057675149834030759035 35655086512724751046138553)
          ·
            refine ⟨26741314884543563284603915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35655086512724751046138553 26741314884543563284603915)
            ·
              refine ⟨40111972326815344926905873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26741314884543563284603915 40111972326815344926905873)
              ·
                refine ⟨30083979245111508695179405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40111972326815344926905873 30083979245111508695179405)
                ·
                  refine ⟨11281492216916815760692277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30083979245111508695179405 11281492216916815760692277)
                  ·
                    refine ⟨1057639895335951477564901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11281492216916815760692277 1057639895335951477564901)
                    ·
                      rfl

theorem cell23_6179239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_6179239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179239 prefixEnd_6179239 := by exact prefixLift 6179239
  have htrace : WordTrace (prefixWord ++ tailWord_6179239) baseStart_6179239 baseEnd_6179239 := by
    simpa [prefixWord, tailWord_6179239, baseEnd_6179239] using wordTrace_append hprefix tailTrace_6179239
  have hstable : (prefixWord ++ tailWord_6179239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179239).length < 2 ^ (prefixWord ++ tailWord_6179239).sum := by decide
  have hdescent : baseEnd_6179239 < baseStart_6179239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179253 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_6179253 : Nat := 118140960795 + 6179253 * 2 ^ 59
def prefixEnd_6179253 : Nat := 4983230072969 + 3 ^ 40 * 6179253 * 2
def baseEnd_6179253 : Nat := 3172926874737017377919639

theorem tailTrace_6179253 : CollatzResearch.WordTrace tailWord_6179253 prefixEnd_6179253 3172926874737017377919639 := by
  unfold tailWord_6179253
  simp only [CollatzResearch.WordTrace]
  refine ⟨225375872282629188238206413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150250581521752792158804275 225375872282629188238206413)
  ·
    refine ⟨84515952105985945589327405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225375872282629188238206413 84515952105985945589327405)
    ·
      refine ⟨31693482039744729595997777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84515952105985945589327405 31693482039744729595997777)
      ·
        refine ⟨23770111529808547196998333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31693482039744729595997777 23770111529808547196998333)
        ·
          refine ⟨8913791823678205198874375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23770111529808547196998333 8913791823678205198874375)
          ·
            refine ⟨13370687735517307798311563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913791823678205198874375 13370687735517307798311563)
            ·
              refine ⟨20056031603275961697467345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13370687735517307798311563 20056031603275961697467345)
              ·
                refine ⟨15042023702456971273100509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20056031603275961697467345 15042023702456971273100509)
                ·
                  refine ⟨5640758888421364227412691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15042023702456971273100509 5640758888421364227412691)
                  ·
                    refine ⟨8461138332632046341119037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640758888421364227412691 8461138332632046341119037)
                    ·
                      refine ⟨3172926874737017377919639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8461138332632046341119037 3172926874737017377919639)
                      ·
                        rfl

theorem cell23_6179253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_6179253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179253 prefixEnd_6179253 := by exact prefixLift 6179253
  have htrace : WordTrace (prefixWord ++ tailWord_6179253) baseStart_6179253 baseEnd_6179253 := by
    simpa [prefixWord, tailWord_6179253, baseEnd_6179253] using wordTrace_append hprefix tailTrace_6179253
  have hstable : (prefixWord ++ tailWord_6179253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179253).length < 2 ^ (prefixWord ++ tailWord_6179253).sum := by decide
  have hdescent : baseEnd_6179253 < baseStart_6179253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179303 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 2, 4]
def baseStart_6179303 : Nat := 118140960795 + 6179303 * 2 ^ 59
def prefixEnd_6179303 : Nat := 4983230072969 + 3 ^ 40 * 6179303 * 2
def baseEnd_6179303 : Nat := 1057650849589914060764803

theorem tailTrace_6179303 : CollatzResearch.WordTrace tailWord_6179303 prefixEnd_6179303 1057650849589914060764803 := by
  unfold tailWord_6179303
  simp only [CollatzResearch.WordTrace]
  refine ⟨225377695932448046777526563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150251797288298697851684375 225377695932448046777526563)
  ·
    refine ⟨338066543898672070166289845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225377695932448046777526563 338066543898672070166289845)
    ·
      refine ⟨31693738490500506578089673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338066543898672070166289845 31693738490500506578089673)
      ·
        refine ⟨23770303867875379933567255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31693738490500506578089673 23770303867875379933567255)
        ·
          refine ⟨35655455801813069900350883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23770303867875379933567255 35655455801813069900350883)
          ·
            refine ⟨53483183702719604850526325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35655455801813069900350883 53483183702719604850526325)
            ·
              refine ⟨5014048472129962954736843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53483183702719604850526325 5014048472129962954736843)
              ·
                refine ⟨7521072708194944432105265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014048472129962954736843 7521072708194944432105265)
                ·
                  refine ⟨5640804531146208324078949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521072708194944432105265 5640804531146208324078949)
                  ·
                    refine ⟨1057650849589914060764803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640804531146208324078949 1057650849589914060764803)
                    ·
                      rfl

theorem cell23_6179303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_6179303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179303 prefixEnd_6179303 := by exact prefixLift 6179303
  have htrace : WordTrace (prefixWord ++ tailWord_6179303) baseStart_6179303 baseEnd_6179303 := by
    simpa [prefixWord, tailWord_6179303, baseEnd_6179303] using wordTrace_append hprefix tailTrace_6179303
  have hstable : (prefixWord ++ tailWord_6179303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179303).length < 2 ^ (prefixWord ++ tailWord_6179303).sum := by decide
  have hdescent : baseEnd_6179303 < baseStart_6179303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179306 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_6179306 : Nat := 118140960795 + 6179306 * 2 ^ 59
def prefixEnd_6179306 : Nat := 4983230072969 + 3 ^ 40 * 6179306 * 2
def baseEnd_6179306 : Nat := 3172954089211705670556895

theorem tailTrace_6179306 : CollatzResearch.WordTrace tailWord_6179306 prefixEnd_6179306 3172954089211705670556895 := by
  unfold tailWord_6179306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56344451337859294572471443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150251870234291452193257181 56344451337859294572471443)
  ·
    refine ⟨84516677006788941858707165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56344451337859294572471443 84516677006788941858707165)
    ·
      refine ⟨31693753877545853197015187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84516677006788941858707165 31693753877545853197015187)
      ·
        refine ⟨47540630816318779795522781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31693753877545853197015187 47540630816318779795522781)
        ·
          refine ⟨17827736556119542423321043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47540630816318779795522781 17827736556119542423321043)
          ·
            refine ⟨26741604834179313634981565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17827736556119542423321043 26741604834179313634981565)
            ·
              refine ⟨10028101812817242613118087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26741604834179313634981565 10028101812817242613118087)
              ·
                refine ⟨15042152719225863919677131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10028101812817242613118087 15042152719225863919677131)
                ·
                  refine ⟨22563229078838795879515697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15042152719225863919677131 22563229078838795879515697)
                  ·
                    refine ⟨16922421809129096909636773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22563229078838795879515697 16922421809129096909636773)
                    ·
                      refine ⟨3172954089211705670556895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16922421809129096909636773 3172954089211705670556895)
                      ·
                        rfl

theorem cell23_6179306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_6179306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179306 prefixEnd_6179306 := by exact prefixLift 6179306
  have htrace : WordTrace (prefixWord ++ tailWord_6179306) baseStart_6179306 baseEnd_6179306 := by
    simpa [prefixWord, tailWord_6179306, baseEnd_6179306] using wordTrace_append hprefix tailTrace_6179306
  have hstable : (prefixWord ++ tailWord_6179306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179306).length < 2 ^ (prefixWord ++ tailWord_6179306).sum := by decide
  have hdescent : baseEnd_6179306 < baseStart_6179306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179336 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_6179336 : Nat := 118140960795 + 6179336 * 2 ^ 59
def prefixEnd_6179336 : Nat := 4983230072969 + 3 ^ 40 * 6179336 * 2
def baseEnd_6179336 : Nat := 3172969493631340553181757

theorem tailTrace_6179336 : CollatzResearch.WordTrace tailWord_6179336 prefixEnd_6179336 3172969493631340553181757 := by
  unfold tailWord_6179336
  simp only [CollatzResearch.WordTrace]
  refine ⟨112689449770664246706738931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150252599694218995608985241 112689449770664246706738931)
  ·
    refine ⟨169034174655996370060108397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112689449770664246706738931 169034174655996370060108397)
    ·
      refine ⟨63387815495998638772540649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169034174655996370060108397 63387815495998638772540649)
      ·
        refine ⟨47540861621998979079405487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63387815495998638772540649 47540861621998979079405487)
        ·
          refine ⟨71311292432998468619108231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47540861621998979079405487 71311292432998468619108231)
          ·
            refine ⟨106966938649497702928662347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71311292432998468619108231 106966938649497702928662347)
            ·
              refine ⟨160450407974246554392993521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106966938649497702928662347 160450407974246554392993521)
              ·
                refine ⟨120337805980684915794745141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160450407974246554392993521 120337805980684915794745141)
                ·
                  refine ⟨11281669310689210855757357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120337805980684915794745141 11281669310689210855757357)
                  ·
                    refine ⟨4230625991508454070909009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11281669310689210855757357 4230625991508454070909009)
                    ·
                      refine ⟨3172969493631340553181757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230625991508454070909009 3172969493631340553181757)
                      ·
                        rfl

theorem cell23_6179336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_6179336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179336 prefixEnd_6179336 := by exact prefixLift 6179336
  have htrace : WordTrace (prefixWord ++ tailWord_6179336) baseStart_6179336 baseEnd_6179336 := by
    simpa [prefixWord, tailWord_6179336, baseEnd_6179336] using wordTrace_append hprefix tailTrace_6179336
  have hstable : (prefixWord ++ tailWord_6179336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179336).length < 2 ^ (prefixWord ++ tailWord_6179336).sum := by decide
  have hdescent : baseEnd_6179336 < baseStart_6179336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179349 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_6179349 : Nat := 118140960795 + 6179349 * 2 ^ 59
def prefixEnd_6179349 : Nat := 4983230072969 + 3 ^ 40 * 6179349 * 2
def baseEnd_6179349 : Nat := 3172976168879849002319197

theorem tailTrace_6179349 : CollatzResearch.WordTrace tailWord_6179349 prefixEnd_6179349 3172976168879849002319197 := by
  unfold tailWord_6179349
  simp only [CollatzResearch.WordTrace]
  refine ⟨225379373690281396633701101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150252915793520931089134067 225379373690281396633701101)
  ·
    refine ⟨84517265133855523737637913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225379373690281396633701101 84517265133855523737637913)
    ·
      refine ⟨63387948850391642803228435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84517265133855523737637913 63387948850391642803228435)
      ·
        refine ⟨95081923275587464204842653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63387948850391642803228435 95081923275587464204842653)
        ·
          refine ⟨35655721228345299076815995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95081923275587464204842653 35655721228345299076815995)
          ·
            refine ⟨53483581842517948615223993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35655721228345299076815995 53483581842517948615223993)
            ·
              refine ⟨40112686381888461461417995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53483581842517948615223993 40112686381888461461417995)
              ·
                refine ⟨60169029572832692192126993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40112686381888461461417995 60169029572832692192126993)
                ·
                  refine ⟨45126772179624519144095245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60169029572832692192126993 45126772179624519144095245)
                  ·
                    refine ⟨16922539567359194679035717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45126772179624519144095245 16922539567359194679035717)
                    ·
                      refine ⟨3172976168879849002319197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16922539567359194679035717 3172976168879849002319197)
                      ·
                        rfl

theorem cell23_6179349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_6179349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179349 prefixEnd_6179349 := by exact prefixLift 6179349
  have htrace : WordTrace (prefixWord ++ tailWord_6179349) baseStart_6179349 baseEnd_6179349 := by
    simpa [prefixWord, tailWord_6179349, baseEnd_6179349] using wordTrace_append hprefix tailTrace_6179349
  have hstable : (prefixWord ++ tailWord_6179349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179349).length < 2 ^ (prefixWord ++ tailWord_6179349).sum := by decide
  have hdescent : baseEnd_6179349 < baseStart_6179349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179360 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6179360 : Nat := 118140960795 + 6179360 * 2 ^ 59
def prefixEnd_6179360 : Nat := 4983230072969 + 3 ^ 40 * 6179360 * 2
def baseEnd_6179360 : Nat := 3172981817167048459281647

theorem tailTrace_6179360 : CollatzResearch.WordTrace tailWord_6179360 prefixEnd_6179360 3172981817167048459281647 := by
  unfold tailWord_6179360
  simp only [CollatzResearch.WordTrace]
  refine ⟨112689887446620772756175767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150253183262161030341567689 112689887446620772756175767)
  ·
    refine ⟨169034831169931159134263651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112689887446620772756175767 169034831169931159134263651)
    ·
      refine ⟨253552246754896738701395477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169034831169931159134263651 253552246754896738701395477)
      ·
        refine ⟨11885261566635784626627913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253552246754896738701395477 11885261566635784626627913)
        ·
          refine ⟨8913946174976838469970935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11885261566635784626627913 8913946174976838469970935)
          ·
            refine ⟨13370919262465257704956403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913946174976838469970935 13370919262465257704956403)
            ·
              refine ⟨20056378893697886557434605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13370919262465257704956403 20056378893697886557434605)
              ·
                refine ⟨7521142085136707459037977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20056378893697886557434605 7521142085136707459037977)
                ·
                  refine ⟨5640856563852530594278483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521142085136707459037977 5640856563852530594278483)
                  ·
                    refine ⟨8461284845778795891417725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640856563852530594278483 8461284845778795891417725)
                    ·
                      refine ⟨3172981817167048459281647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8461284845778795891417725 3172981817167048459281647)
                      ·
                        rfl

theorem cell23_6179360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6179360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179360 prefixEnd_6179360 := by exact prefixLift 6179360
  have htrace : WordTrace (prefixWord ++ tailWord_6179360) baseStart_6179360 baseEnd_6179360 := by
    simpa [prefixWord, tailWord_6179360, baseEnd_6179360] using wordTrace_append hprefix tailTrace_6179360
  have hstable : (prefixWord ++ tailWord_6179360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179360).length < 2 ^ (prefixWord ++ tailWord_6179360).sum := by decide
  have hdescent : baseEnd_6179360 < baseStart_6179360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179370 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6179370 : Nat := 118140960795 + 6179370 * 2 ^ 59
def prefixEnd_6179370 : Nat := 4983230072969 + 3 ^ 40 * 6179370 * 2
def baseEnd_6179370 : Nat := 3172986951973593420156601

theorem tailTrace_6179370 : CollatzResearch.WordTrace tailWord_6179370 prefixEnd_6179370 3172986951973593420156601 := by
  unfold tailWord_6179370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56345034905801329305053891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150253426415470211480143709 56345034905801329305053891)
  ·
    refine ⟨84517552358701993957580837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56345034905801329305053891 84517552358701993957580837)
    ·
      refine ⟨15847041067256623867046407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84517552358701993957580837 15847041067256623867046407)
      ·
        refine ⟨23770561600884935800569611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15847041067256623867046407 23770561600884935800569611)
        ·
          refine ⟨35655842401327403700854417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23770561600884935800569611 35655842401327403700854417)
          ·
            refine ⟨26741881800995552775640813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35655842401327403700854417 26741881800995552775640813)
            ·
              refine ⟨10028205675373332290865305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26741881800995552775640813 10028205675373332290865305)
              ·
                refine ⟨7521154256529999218148979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10028205675373332290865305 7521154256529999218148979)
                ·
                  refine ⟨11281731384794998827223469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521154256529999218148979 11281731384794998827223469)
                  ·
                    refine ⟨4230649269298124560208801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11281731384794998827223469 4230649269298124560208801)
                    ·
                      refine ⟨3172986951973593420156601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230649269298124560208801 3172986951973593420156601)
                      ·
                        rfl

theorem cell23_6179370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6179370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179370 prefixEnd_6179370 := by exact prefixLift 6179370
  have htrace : WordTrace (prefixWord ++ tailWord_6179370) baseStart_6179370 baseEnd_6179370 := by
    simpa [prefixWord, tailWord_6179370, baseEnd_6179370] using wordTrace_append hprefix tailTrace_6179370
  have hstable : (prefixWord ++ tailWord_6179370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179370).length < 2 ^ (prefixWord ++ tailWord_6179370).sum := by decide
  have hdescent : baseEnd_6179370 < baseStart_6179370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179436 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_6179436 : Nat := 118140960795 + 6179436 * 2 ^ 59
def prefixEnd_6179436 : Nat := 4983230072969 + 3 ^ 40 * 6179436 * 2
def baseEnd_6179436 : Nat := 1057673613898930053977099

theorem tailTrace_6179436 : CollatzResearch.WordTrace tailWord_6179436 prefixEnd_6179436 1057673613898930053977099 := by
  unfold tailWord_6179436
  simp only [CollatzResearch.WordTrace]
  refine ⟨112691273420483105246059081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150255031227310806994745441 112691273420483105246059081)
  ·
    refine ⟨84518455065362328934544311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112691273420483105246059081 84518455065362328934544311)
    ·
      refine ⟨126777682598043493401816467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84518455065362328934544311 126777682598043493401816467)
      ·
        refine ⟨190166523897065240102724701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126777682598043493401816467 190166523897065240102724701)
        ·
          refine ⟨71312446461399465038521763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190166523897065240102724701 71312446461399465038521763)
          ·
            refine ⟨106968669692099197557782645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71312446461399465038521763 106968669692099197557782645)
            ·
              refine ⟨10028312783634299771042123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106968669692099197557782645 10028312783634299771042123)
              ·
                refine ⟨15042469175451449656563185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10028312783634299771042123 15042469175451449656563185)
                ·
                  refine ⟨11281851881588587242422389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15042469175451449656563185 11281851881588587242422389)
                  ·
                    refine ⟨1057673613898930053977099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11281851881588587242422389 1057673613898930053977099)
                    ·
                      rfl

theorem cell23_6179436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_6179436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179436 prefixEnd_6179436 := by exact prefixLift 6179436
  have htrace : WordTrace (prefixWord ++ tailWord_6179436) baseStart_6179436 baseEnd_6179436 := by
    simpa [prefixWord, tailWord_6179436, baseEnd_6179436] using wordTrace_append hprefix tailTrace_6179436
  have hstable : (prefixWord ++ tailWord_6179436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179436).length < 2 ^ (prefixWord ++ tailWord_6179436).sum := by decide
  have hdescent : baseEnd_6179436 < baseStart_6179436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179459 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_6179459 : Nat := 118140960795 + 6179459 * 2 ^ 59
def prefixEnd_6179459 : Nat := 4983230072969 + 3 ^ 40 * 6179459 * 2
def baseEnd_6179459 : Nat := 3173032651751843571943691

theorem tailTrace_6179459 : CollatzResearch.WordTrace tailWord_6179459 prefixEnd_6179459 3173032651751843571943691 := by
  unfold tailWord_6179459
  simp only [CollatzResearch.WordTrace]
  refine ⟨225383385719882885420205431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150255590479921923613470287 225383385719882885420205431)
  ·
    refine ⟨338075078579824328130308147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225383385719882885420205431 338075078579824328130308147)
    ·
      refine ⟨507112617869736492195462221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338075078579824328130308147 507112617869736492195462221)
      ·
        refine ⟨190167231701151184573298333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507112617869736492195462221 190167231701151184573298333)
        ·
          refine ⟨71312711887931694214986875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190167231701151184573298333 71312711887931694214986875)
          ·
            refine ⟨106969067831897541322480313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71312711887931694214986875 106969067831897541322480313)
            ·
              refine ⟨80226800873923155991860235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106969067831897541322480313 80226800873923155991860235)
              ·
                refine ⟨120340201310884733987790353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80226800873923155991860235 120340201310884733987790353)
                ·
                  refine ⟨90255150983163550490842765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120340201310884733987790353 90255150983163550490842765)
                  ·
                    refine ⟨33845681618686331434066037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90255150983163550490842765 33845681618686331434066037)
                    ·
                      refine ⟨3173032651751843571943691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33845681618686331434066037 3173032651751843571943691)
                      ·
                        rfl

theorem cell23_6179459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_6179459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179459 prefixEnd_6179459 := by exact prefixLift 6179459
  have htrace : WordTrace (prefixWord ++ tailWord_6179459) baseStart_6179459 baseEnd_6179459 := by
    simpa [prefixWord, tailWord_6179459, baseEnd_6179459] using wordTrace_append hprefix tailTrace_6179459
  have hstable : (prefixWord ++ tailWord_6179459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179459).length < 2 ^ (prefixWord ++ tailWord_6179459).sum := by decide
  have hdescent : baseEnd_6179459 < baseStart_6179459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179517 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_6179517 : Nat := 118140960795 + 6179517 * 2 ^ 59
def prefixEnd_6179517 : Nat := 4983230072969 + 3 ^ 40 * 6179517 * 2
def baseEnd_6179517 : Nat := 1057687477876601448339475

theorem tailTrace_6179517 : CollatzResearch.WordTrace tailWord_6179517 prefixEnd_6179517 1057687477876601448339475 := by
  unfold tailWord_6179517
  simp only [CollatzResearch.WordTrace]
  refine ⟨225385501153672761325816805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150257000769115174217211203 225385501153672761325816805)
  ·
    refine ⟨42259781466313642748590651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225385501153672761325816805 42259781466313642748590651)
    ·
      refine ⟨63389672199470464122885977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42259781466313642748590651 63389672199470464122885977)
      ·
        refine ⟨47542254149602848092164483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63389672199470464122885977 47542254149602848092164483)
        ·
          refine ⟨71313381224404272138246725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47542254149602848092164483 71313381224404272138246725)
          ·
            refine ⟨13371258979575801025921261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71313381224404272138246725 13371258979575801025921261)
            ·
              refine ⟨5014222117340925384720473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13371258979575801025921261 5014222117340925384720473)
              ·
                refine ⟨3760666588005694038540355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014222117340925384720473 3760666588005694038540355)
                ·
                  refine ⟨5640999882008541057810533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760666588005694038540355 5640999882008541057810533)
                  ·
                    refine ⟨1057687477876601448339475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640999882008541057810533 1057687477876601448339475)
                    ·
                      rfl

theorem cell23_6179517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_6179517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179517 prefixEnd_6179517 := by exact prefixLift 6179517
  have htrace : WordTrace (prefixWord ++ tailWord_6179517) baseStart_6179517 baseEnd_6179517 := by
    simpa [prefixWord, tailWord_6179517, baseEnd_6179517] using wordTrace_append hprefix tailTrace_6179517
  have hstable : (prefixWord ++ tailWord_6179517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179517).length < 2 ^ (prefixWord ++ tailWord_6179517).sum := by decide
  have hdescent : baseEnd_6179517 < baseStart_6179517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179529 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_6179529 : Nat := 118140960795 + 6179529 * 2 ^ 59
def prefixEnd_6179529 : Nat := 4983230072969 + 3 ^ 40 * 6179529 * 2
def baseEnd_6179529 : Nat := 3173068595397658298068369

theorem tailTrace_6179529 : CollatzResearch.WordTrace tailWord_6179529 prefixEnd_6179529 3173068595397658298068369 := by
  unfold tailWord_6179529
  simp only [CollatzResearch.WordTrace]
  refine ⟨225385938829629287375253641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150257292553086191583502427 225385938829629287375253641)
  ·
    refine ⟨169039454122221965531440231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225385938829629287375253641 169039454122221965531440231)
    ·
      refine ⟨253559181183332948297160347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169039454122221965531440231 253559181183332948297160347)
      ·
        refine ⟨380338771774999422445740521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253559181183332948297160347 380338771774999422445740521)
        ·
          refine ⟨285254078831249566834305391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380338771774999422445740521 285254078831249566834305391)
          ·
            refine ⟨427881118246874350251458087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285254078831249566834305391 427881118246874350251458087)
            ·
              refine ⟨641821677370311525377187131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427881118246874350251458087 641821677370311525377187131)
              ·
                refine ⟨962732516055467288065780697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641821677370311525377187131 962732516055467288065780697)
                ·
                  refine ⟨722049387041600466049335523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962732516055467288065780697 722049387041600466049335523)
                  ·
                    refine ⟨1083074080562400699074003285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 722049387041600466049335523 1083074080562400699074003285)
                    ·
                      refine ⟨3173068595397658298068369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1083074080562400699074003285 3173068595397658298068369)
                      ·
                        rfl

theorem cell23_6179529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_6179529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179529 prefixEnd_6179529 := by exact prefixLift 6179529
  have htrace : WordTrace (prefixWord ++ tailWord_6179529) baseStart_6179529 baseEnd_6179529 := by
    simpa [prefixWord, tailWord_6179529, baseEnd_6179529] using wordTrace_append hprefix tailTrace_6179529
  have hstable : (prefixWord ++ tailWord_6179529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179529).length < 2 ^ (prefixWord ++ tailWord_6179529).sum := by decide
  have hdescent : baseEnd_6179529 < baseStart_6179529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179530 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_6179530 : Nat := 118140960795 + 6179530 * 2 ^ 59
def prefixEnd_6179530 : Nat := 4983230072969 + 3 ^ 40 * 6179530 * 2
def baseEnd_6179530 : Nat := 352563234319812532683985

theorem tailTrace_6179530 : CollatzResearch.WordTrace tailWord_6179530 prefixEnd_6179530 352563234319812532683985 := by
  unfold tailWord_6179530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56346493825656416136510011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150257316868417109697360029 56346493825656416136510011)
  ·
    refine ⟨84519740738484624204765017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56346493825656416136510011 84519740738484624204765017)
    ·
      refine ⟨63389805553863468153573763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84519740738484624204765017 63389805553863468153573763)
      ·
        refine ⟨95084708330795202230360645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63389805553863468153573763 95084708330795202230360645)
        ·
          refine ⟨17828382812024100418192621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95084708330795202230360645 17828382812024100418192621)
          ·
            refine ⟨6685643554509037656822233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17828382812024100418192621 6685643554509037656822233)
            ·
              refine ⟨5014232665881778242616675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685643554509037656822233 5014232665881778242616675)
              ·
                refine ⟨7521348998822667363925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014232665881778242616675 7521348998822667363925013)
                ·
                  refine ⟨352563234319812532683985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7521348998822667363925013 352563234319812532683985)
                  ·
                    rfl

theorem cell23_6179530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_6179530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179530 prefixEnd_6179530 := by exact prefixLift 6179530
  have htrace : WordTrace (prefixWord ++ tailWord_6179530) baseStart_6179530 baseEnd_6179530 := by
    simpa [prefixWord, tailWord_6179530, baseEnd_6179530] using wordTrace_append hprefix tailTrace_6179530
  have hstable : (prefixWord ++ tailWord_6179530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179530).length < 2 ^ (prefixWord ++ tailWord_6179530).sum := by decide
  have hdescent : baseEnd_6179530 < baseStart_6179530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 12]
def baseStart_6179539 : Nat := 118140960795 + 6179539 * 2 ^ 59
def prefixEnd_6179539 : Nat := 4983230072969 + 3 ^ 40 * 6179539 * 2
def baseEnd_6179539 : Nat := 1057691243401401086314441

theorem tailTrace_6179539 : CollatzResearch.WordTrace tailWord_6179539 prefixEnd_6179539 1057691243401401086314441 := by
  unfold tailWord_6179539
  simp only [CollatzResearch.WordTrace]
  refine ⟨225386303559593059083117671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150257535706395372722078447 225386303559593059083117671)
  ·
    refine ⟨338079455339389588624676507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225386303559593059083117671 338079455339389588624676507)
    ·
      refine ⟨507119183009084382937014761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338079455339389588624676507 507119183009084382937014761)
      ·
        refine ⟨380339387256813287202761071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507119183009084382937014761 380339387256813287202761071)
        ·
          refine ⟨570509080885219930804141607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380339387256813287202761071 570509080885219930804141607)
          ·
            refine ⟨855763621327829896206212411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570509080885219930804141607 855763621327829896206212411)
            ·
              refine ⟨1283645431991744844309318617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855763621327829896206212411 1283645431991744844309318617)
              ·
                refine ⟨962734073993808633231988963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283645431991744844309318617 962734073993808633231988963)
                ·
                  refine ⟨1444101110990712949847983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962734073993808633231988963 1444101110990712949847983445)
                  ·
                    refine ⟨1057691243401401086314441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1444101110990712949847983445 1057691243401401086314441)
                    ·
                      rfl

theorem cell23_6179539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_6179539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179539 prefixEnd_6179539 := by exact prefixLift 6179539
  have htrace : WordTrace (prefixWord ++ tailWord_6179539) baseStart_6179539 baseEnd_6179539 := by
    simpa [prefixWord, tailWord_6179539, baseEnd_6179539] using wordTrace_append hprefix tailTrace_6179539
  have hstable : (prefixWord ++ tailWord_6179539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179539).length < 2 ^ (prefixWord ++ tailWord_6179539).sum := by decide
  have hdescent : baseEnd_6179539 < baseStart_6179539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179543 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 1, 5]
def baseStart_6179543 : Nat := 118140960795 + 6179543 * 2 ^ 59
def prefixEnd_6179543 : Nat := 4983230072969 + 3 ^ 40 * 6179543 * 2
def baseEnd_6179543 : Nat := 1057691928042273747764435

theorem tailTrace_6179543 : CollatzResearch.WordTrace tailWord_6179543 prefixEnd_6179543 1057691928042273747764435 := by
  unfold tailWord_6179543
  simp only [CollatzResearch.WordTrace]
  refine ⟨225386449451578567766263283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150257632967719045177508855 225386449451578567766263283)
  ·
    refine ⟨338079674177367851649394925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225386449451578567766263283 338079674177367851649394925)
    ·
      refine ⟨126779877816512944368523097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338079674177367851649394925 126779877816512944368523097)
      ·
        refine ⟨95084908362384708276392323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126779877816512944368523097 95084908362384708276392323)
        ·
          refine ⟨142627362543577062414588485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95084908362384708276392323 142627362543577062414588485)
          ·
            refine ⟨26742630476920699202735341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142627362543577062414588485 26742630476920699202735341)
            ·
              refine ⟨10028486428845262201025753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26742630476920699202735341 10028486428845262201025753)
              ·
                refine ⟨7521364821633946650769315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10028486428845262201025753 7521364821633946650769315)
                ·
                  refine ⟨11282047232450919976153973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521364821633946650769315 11282047232450919976153973)
                  ·
                    refine ⟨1057691928042273747764435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11282047232450919976153973 1057691928042273747764435)
                    ·
                      rfl

theorem cell23_6179543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_6179543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179543 prefixEnd_6179543 := by exact prefixLift 6179543
  have htrace : WordTrace (prefixWord ++ tailWord_6179543) baseStart_6179543 baseEnd_6179543 := by
    simpa [prefixWord, tailWord_6179543, baseEnd_6179543] using wordTrace_append hprefix tailTrace_6179543
  have hstable : (prefixWord ++ tailWord_6179543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179543).length < 2 ^ (prefixWord ++ tailWord_6179543).sum := by decide
  have hdescent : baseEnd_6179543 < baseStart_6179543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179556 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_6179556 : Nat := 118140960795 + 6179556 * 2 ^ 59
def prefixEnd_6179556 : Nat := 4983230072969 + 3 ^ 40 * 6179556 * 2
def baseEnd_6179556 : Nat := 1057694153125109897476915

theorem tailTrace_6179556 : CollatzResearch.WordTrace tailWord_6179556 prefixEnd_6179556 1057694153125109897476915 := by
  unfold tailWord_6179556
  simp only [CollatzResearch.WordTrace]
  refine ⟨112693461800265735493243261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150257949067020980657657681 112693461800265735493243261)
  ·
    refine ⟨42260048175099650809966223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112693461800265735493243261 42260048175099650809966223)
    ·
      refine ⟨63390072262649476214949335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42260048175099650809966223 63390072262649476214949335)
      ·
        refine ⟨95085108393974214322424003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63390072262649476214949335 95085108393974214322424003)
        ·
          refine ⟨142627662590961321483636005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95085108393974214322424003 142627662590961321483636005)
          ·
            refine ⟨26742686735805247778181751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142627662590961321483636005 26742686735805247778181751)
            ·
              refine ⟨40114030103707871667272627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26742686735805247778181751 40114030103707871667272627)
              ·
                refine ⟨60171045155561807500908941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40114030103707871667272627 60171045155561807500908941)
                ·
                  refine ⟨22564141933335677812840853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60171045155561807500908941 22564141933335677812840853)
                  ·
                    refine ⟨1057694153125109897476915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22564141933335677812840853 1057694153125109897476915)
                    ·
                      rfl

theorem cell23_6179556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_6179556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179556 prefixEnd_6179556 := by exact prefixLift 6179556
  have htrace : WordTrace (prefixWord ++ tailWord_6179556) baseStart_6179556 baseEnd_6179556 := by
    simpa [prefixWord, tailWord_6179556, baseEnd_6179556] using wordTrace_append hprefix tailTrace_6179556
  have hstable : (prefixWord ++ tailWord_6179556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179556).length < 2 ^ (prefixWord ++ tailWord_6179556).sum := by decide
  have hdescent : baseEnd_6179556 < baseStart_6179556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179576 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_6179576 : Nat := 118140960795 + 6179576 * 2 ^ 59
def prefixEnd_6179576 : Nat := 4983230072969 + 3 ^ 40 * 6179576 * 2
def baseEnd_6179576 : Nat := 3173092728988419614180653

theorem tailTrace_6179576 : CollatzResearch.WordTrace tailWord_6179576 prefixEnd_6179576 3173092728988419614180653 := by
  unfold tailWord_6179576
  simp only [CollatzResearch.WordTrace]
  refine ⟨112693826530229507201107291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150258435373639342934809721 112693826530229507201107291)
  ·
    refine ⟨169040739795344260801660937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112693826530229507201107291 169040739795344260801660937)
    ·
      refine ⟨126780554846508195601245703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169040739795344260801660937 126780554846508195601245703)
      ·
        refine ⟨190170832269762293401868555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126780554846508195601245703 190170832269762293401868555)
        ·
          refine ⟨285256248404643440102802833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190170832269762293401868555 285256248404643440102802833)
          ·
            refine ⟨213942186303482580077102125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285256248404643440102802833 213942186303482580077102125)
            ·
              refine ⟨80228319863805967528913297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213942186303482580077102125 80228319863805967528913297)
              ·
                refine ⟨60171239897854475646684973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80228319863805967528913297 60171239897854475646684973)
                ·
                  refine ⟨22564214961695428367506865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60171239897854475646684973 22564214961695428367506865)
                  ·
                    refine ⟨16923161221271571275630149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22564214961695428367506865 16923161221271571275630149)
                    ·
                      refine ⟨3173092728988419614180653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16923161221271571275630149 3173092728988419614180653)
                      ·
                        rfl

theorem cell23_6179576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_6179576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179576 prefixEnd_6179576 := by exact prefixLift 6179576
  have htrace : WordTrace (prefixWord ++ tailWord_6179576) baseStart_6179576 baseEnd_6179576 := by
    simpa [prefixWord, tailWord_6179576, baseEnd_6179576] using wordTrace_append hprefix tailTrace_6179576
  have hstable : (prefixWord ++ tailWord_6179576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179576).length < 2 ^ (prefixWord ++ tailWord_6179576).sum := by decide
  have hdescent : baseEnd_6179576 < baseStart_6179576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179654 : List Nat := [6, 1, 1, 2, 2, 2, 2, 7]
def baseStart_6179654 : Nat := 118140960795 + 6179654 * 2 ^ 59
def prefixEnd_6179654 : Nat := 4983230072969 + 3 ^ 40 * 6179654 * 2
def baseEnd_6179654 : Nat := 117523436314054455889085

theorem tailTrace_6179654 : CollatzResearch.WordTrace tailWord_6179654 prefixEnd_6179654 117523436314054455889085 := by
  unfold tailWord_6179654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043453061068013553861063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150260331969450955815702677 7043453061068013553861063)
  ·
    refine ⟨10565179591602020330791595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7043453061068013553861063 10565179591602020330791595)
    ·
      refine ⟨15847769387403030496187393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10565179591602020330791595 15847769387403030496187393)
      ·
        refine ⟨11885827040552272872140545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15847769387403030496187393 11885827040552272872140545)
        ·
          refine ⟨8914370280414204654105409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11885827040552272872140545 8914370280414204654105409)
          ·
            refine ⟨6685777710310653490579057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914370280414204654105409 6685777710310653490579057)
            ·
              refine ⟨5014333282732990117934293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685777710310653490579057 5014333282732990117934293)
              ·
                refine ⟨117523436314054455889085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5014333282732990117934293 117523436314054455889085)
                ·
                  rfl

theorem cell23_6179654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_6179654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179654 prefixEnd_6179654 := by exact prefixLift 6179654
  have htrace : WordTrace (prefixWord ++ tailWord_6179654) baseStart_6179654 baseEnd_6179654 := by
    simpa [prefixWord, tailWord_6179654, baseEnd_6179654] using wordTrace_append hprefix tailTrace_6179654
  have hstable : (prefixWord ++ tailWord_6179654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179654).length < 2 ^ (prefixWord ++ tailWord_6179654).sum := by decide
  have hdescent : baseEnd_6179654 < baseStart_6179654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179657 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 1, 3, 2]
def baseStart_6179657 : Nat := 118140960795 + 6179657 * 2 ^ 59
def prefixEnd_6179657 : Nat := 4983230072969 + 3 ^ 40 * 6179657 * 2
def baseEnd_6179657 : Nat := 3173134320921433797267781

theorem tailTrace_6179657 : CollatzResearch.WordTrace tailWord_6179657 prefixEnd_6179657 3173134320921433797267781 := by
  unfold tailWord_6179657
  simp only [CollatzResearch.WordTrace]
  refine ⟨225390607373165565235913225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150260404915443710157275483 225390607373165565235913225)
  ·
    refine ⟨169042955529874173926934919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225390607373165565235913225 169042955529874173926934919)
    ·
      refine ⟨253564433294811260890402379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169042955529874173926934919 253564433294811260890402379)
      ·
        refine ⟨380346649942216891335603569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253564433294811260890402379 380346649942216891335603569)
        ·
          refine ⟨285259987456662668501702677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380346649942216891335603569 285259987456662668501702677)
          ·
            refine ⟨13371561912031062586017313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285259987456662668501702677 13371561912031062586017313)
            ·
              refine ⟨10028671434023296939512985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13371561912031062586017313 10028671434023296939512985)
              ·
                refine ⟨7521503575517472704634739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10028671434023296939512985 7521503575517472704634739)
                ·
                  refine ⟨11282255363276209056952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521503575517472704634739 11282255363276209056952109)
                  ·
                    refine ⟨4230845761228578396357041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11282255363276209056952109 4230845761228578396357041)
                    ·
                      refine ⟨3173134320921433797267781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230845761228578396357041 3173134320921433797267781)
                      ·
                        rfl

theorem cell23_6179657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 3, 2].length) (baseStart_6179657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179657 prefixEnd_6179657 := by exact prefixLift 6179657
  have htrace : WordTrace (prefixWord ++ tailWord_6179657) baseStart_6179657 baseEnd_6179657 := by
    simpa [prefixWord, tailWord_6179657, baseEnd_6179657] using wordTrace_append hprefix tailTrace_6179657
  have hstable : (prefixWord ++ tailWord_6179657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179657).length < 2 ^ (prefixWord ++ tailWord_6179657).sum := by decide
  have hdescent : baseEnd_6179657 < baseStart_6179657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179673 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_6179673 : Nat := 118140960795 + 6179673 * 2 ^ 59
def prefixEnd_6179673 : Nat := 4983230072969 + 3 ^ 40 * 6179673 * 2
def baseEnd_6179673 : Nat := 3173142536611905734667707

theorem tailTrace_6179673 : CollatzResearch.WordTrace tailWord_6179673 prefixEnd_6179673 3173142536611905734667707 := by
  unfold tailWord_6179673
  simp only [CollatzResearch.WordTrace]
  refine ⟨225391190941107599968495673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150260793960738399978997115 225391190941107599968495673)
  ·
    refine ⟨169043393205830699976371755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225391190941107599968495673 169043393205830699976371755)
    ·
      refine ⟨253565089808746049964557633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169043393205830699976371755 253565089808746049964557633)
      ·
        refine ⟨190173817356559537473418225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253565089808746049964557633 190173817356559537473418225)
        ·
          refine ⟨142630363017419653105063669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190173817356559537473418225 142630363017419653105063669)
          ·
            refine ⟨13371596532883092478599719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142630363017419653105063669 13371596532883092478599719)
            ·
              refine ⟨20057394799324638717899579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13371596532883092478599719 20057394799324638717899579)
              ·
                refine ⟨30086092198986958076849369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20057394799324638717899579 30086092198986958076849369)
                ·
                  refine ⟨22564569149240218557637027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30086092198986958076849369 22564569149240218557637027)
                  ·
                    refine ⟨33846853723860327836455541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22564569149240218557637027 33846853723860327836455541)
                    ·
                      refine ⟨3173142536611905734667707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33846853723860327836455541 3173142536611905734667707)
                      ·
                        rfl

theorem cell23_6179673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_6179673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179673 prefixEnd_6179673 := by exact prefixLift 6179673
  have htrace : WordTrace (prefixWord ++ tailWord_6179673) baseStart_6179673 baseEnd_6179673 := by
    simpa [prefixWord, tailWord_6179673, baseEnd_6179673] using wordTrace_append hprefix tailTrace_6179673
  have hstable : (prefixWord ++ tailWord_6179673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179673).length < 2 ^ (prefixWord ++ tailWord_6179673).sum := by decide
  have hdescent : baseEnd_6179673 < baseStart_6179673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179687 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_6179687 : Nat := 118140960795 + 6179687 * 2 ^ 59
def prefixEnd_6179687 : Nat := 4983230072969 + 3 ^ 40 * 6179687 * 2
def baseEnd_6179687 : Nat := 3173149725341068679892643

theorem tailTrace_6179687 : CollatzResearch.WordTrace tailWord_6179687 prefixEnd_6179687 3173149725341068679892643 := by
  unfold tailWord_6179687
  simp only [CollatzResearch.WordTrace]
  refine ⟨225391701563056880359505315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150261134375371253573003543 225391701563056880359505315)
  ·
    refine ⟨338087552344585320539257973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225391701563056880359505315 338087552344585320539257973)
    ·
      refine ⟨31695708032304873800555435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338087552344585320539257973 31695708032304873800555435)
      ·
        refine ⟨47543562048457310700833153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31695708032304873800555435 47543562048457310700833153)
        ·
          refine ⟨35657671536342983025624865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47543562048457310700833153 35657671536342983025624865)
          ·
            refine ⟨26743253652257237269218649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35657671536342983025624865 26743253652257237269218649)
            ·
              refine ⟨20057440239192927951913987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26743253652257237269218649 20057440239192927951913987)
              ·
                refine ⟨30086160358789391927870981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20057440239192927951913987 30086160358789391927870981)
                ·
                  refine ⟨5641155067273010986475809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30086160358789391927870981 5641155067273010986475809)
                  ·
                    refine ⟨4230866300454758239856857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5641155067273010986475809 4230866300454758239856857)
                    ·
                      refine ⟨3173149725341068679892643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230866300454758239856857 3173149725341068679892643)
                      ·
                        rfl

theorem cell23_6179687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_6179687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179687 prefixEnd_6179687 := by exact prefixLift 6179687
  have htrace : WordTrace (prefixWord ++ tailWord_6179687) baseStart_6179687 baseEnd_6179687 := by
    simpa [prefixWord, tailWord_6179687, baseEnd_6179687] using wordTrace_append hprefix tailTrace_6179687
  have hstable : (prefixWord ++ tailWord_6179687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179687).length < 2 ^ (prefixWord ++ tailWord_6179687).sum := by decide
  have hdescent : baseEnd_6179687 < baseStart_6179687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179703 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_6179703 : Nat := 118140960795 + 6179703 * 2 ^ 59
def prefixEnd_6179703 : Nat := 4983230072969 + 3 ^ 40 * 6179703 * 2
def baseEnd_6179703 : Nat := 3173157941031540617292569

theorem tailTrace_6179703 : CollatzResearch.WordTrace tailWord_6179703 prefixEnd_6179703 3173157941031540617292569 := by
  unfold tailWord_6179703
  simp only [CollatzResearch.WordTrace]
  refine ⟨225392285130998915092087763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150261523420665943394725175 225392285130998915092087763)
  ·
    refine ⟨338088427696498372638131645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225392285130998915092087763 338088427696498372638131645)
    ·
      refine ⟨126783160386186889739299367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338088427696498372638131645 126783160386186889739299367)
      ·
        refine ⟨190174740579280334608949051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126783160386186889739299367 190174740579280334608949051)
        ·
          refine ⟨285262110868920501913423577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190174740579280334608949051 285262110868920501913423577)
          ·
            refine ⟨213946583151690376435067683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285262110868920501913423577 213946583151690376435067683)
            ·
              refine ⟨320919874727535564652601525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213946583151690376435067683 320919874727535564652601525)
              ·
                refine ⟨30086238255706459186181393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320919874727535564652601525 30086238255706459186181393)
                ·
                  refine ⟨22564678691779844389636045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30086238255706459186181393 22564678691779844389636045)
                  ·
                    refine ⟨8461754509417441646113517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22564678691779844389636045 8461754509417441646113517)
                    ·
                      refine ⟨3173157941031540617292569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8461754509417441646113517 3173157941031540617292569)
                      ·
                        rfl

theorem cell23_6179703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_6179703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179703 prefixEnd_6179703 := by exact prefixLift 6179703
  have htrace : WordTrace (prefixWord ++ tailWord_6179703) baseStart_6179703 baseEnd_6179703 := by
    simpa [prefixWord, tailWord_6179703, baseEnd_6179703] using wordTrace_append hprefix tailTrace_6179703
  have hstable : (prefixWord ++ tailWord_6179703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179703).length < 2 ^ (prefixWord ++ tailWord_6179703).sum := by decide
  have hdescent : baseEnd_6179703 < baseStart_6179703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179723 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 2, 5]
def baseStart_6179723 : Nat := 118140960795 + 6179723 * 2 ^ 59
def prefixEnd_6179723 : Nat := 4983230072969 + 3 ^ 40 * 6179723 * 2
def baseEnd_6179723 : Nat := 1057722736881543513014159

theorem tailTrace_6179723 : CollatzResearch.WordTrace tailWord_6179723 prefixEnd_6179723 1057722736881543513014159 := by
  unfold tailWord_6179723
  simp only [CollatzResearch.WordTrace]
  refine ⟨225393014590926458507815823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150262009727284305671877215 225393014590926458507815823)
  ·
    refine ⟨338089521886389687761723735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225393014590926458507815823 338089521886389687761723735)
    ·
      refine ⟨507134282829584531642585603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338089521886389687761723735 507134282829584531642585603)
      ·
        refine ⟨760701424244376797463878405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507134282829584531642585603 760701424244376797463878405)
        ·
          refine ⟨142631517045820649524477201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 760701424244376797463878405 142631517045820649524477201)
          ·
            refine ⟨106973637784365487143357901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142631517045820649524477201 106973637784365487143357901)
            ·
              refine ⟨40115114169137057678759213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106973637784365487143357901 40115114169137057678759213)
              ·
                refine ⟨15043167813426396629534705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40115114169137057678759213 15043167813426396629534705)
                ·
                  refine ⟨11282375860069797472151029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043167813426396629534705 11282375860069797472151029)
                  ·
                    refine ⟨1057722736881543513014159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11282375860069797472151029 1057722736881543513014159)
                    ·
                      rfl

theorem cell23_6179723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 5].length) (baseStart_6179723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179723 prefixEnd_6179723 := by exact prefixLift 6179723
  have htrace : WordTrace (prefixWord ++ tailWord_6179723) baseStart_6179723 baseEnd_6179723 := by
    simpa [prefixWord, tailWord_6179723, baseEnd_6179723] using wordTrace_append hprefix tailTrace_6179723
  have hstable : (prefixWord ++ tailWord_6179723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179723).length < 2 ^ (prefixWord ++ tailWord_6179723).sum := by decide
  have hdescent : baseEnd_6179723 < baseStart_6179723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179733 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_6179733 : Nat := 118140960795 + 6179733 * 2 ^ 59
def prefixEnd_6179733 : Nat := 4983230072969 + 3 ^ 40 * 6179733 * 2
def baseEnd_6179733 : Nat := 3173173345451175499917431

theorem tailTrace_6179733 : CollatzResearch.WordTrace tailWord_6179733 prefixEnd_6179733 3173173345451175499917431 := by
  unfold tailWord_6179733
  simp only [CollatzResearch.WordTrace]
  refine ⟨225393379320890230215679853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150262252880593486810453235 225393379320890230215679853)
  ·
    refine ⟨84522517245333836330879945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225393379320890230215679853 84522517245333836330879945)
    ·
      refine ⟨63391887934000377248159959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84522517245333836330879945 63391887934000377248159959)
      ·
        refine ⟨95087831901000565872239939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63391887934000377248159959 95087831901000565872239939)
        ·
          refine ⟨142631747851500848808359909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95087831901000565872239939 142631747851500848808359909)
          ·
            refine ⟨26743452722156409151567483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142631747851500848808359909 26743452722156409151567483)
            ·
              refine ⟨40115179083234613727351225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26743452722156409151567483 40115179083234613727351225)
              ·
                refine ⟨30086384312425960295513419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40115179083234613727351225 30086384312425960295513419)
                ·
                  refine ⟨45129576468638940443270129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30086384312425960295513419 45129576468638940443270129)
                  ·
                    refine ⟨33847182351479205332452597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45129576468638940443270129 33847182351479205332452597)
                    ·
                      refine ⟨3173173345451175499917431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33847182351479205332452597 3173173345451175499917431)
                      ·
                        rfl

theorem cell23_6179733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_6179733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179733 prefixEnd_6179733 := by exact prefixLift 6179733
  have htrace : WordTrace (prefixWord ++ tailWord_6179733) baseStart_6179733 baseEnd_6179733 := by
    simpa [prefixWord, tailWord_6179733, baseEnd_6179733] using wordTrace_append hprefix tailTrace_6179733
  have hstable : (prefixWord ++ tailWord_6179733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179733).length < 2 ^ (prefixWord ++ tailWord_6179733).sum := by decide
  have hdescent : baseEnd_6179733 < baseStart_6179733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179770 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_6179770 : Nat := 118140960795 + 6179770 * 2 ^ 59
def prefixEnd_6179770 : Nat := 4983230072969 + 3 ^ 40 * 6179770 * 2
def baseEnd_6179770 : Nat := 1057730781411797285051587

theorem tailTrace_6179770 : CollatzResearch.WordTrace tailWord_6179770 prefixEnd_6179770 1057730781411797285051587 := by
  unfold tailWord_6179770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56348682205439046383694191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150263152547837457023184509 56348682205439046383694191)
  ·
    refine ⟨84523023308158569575541287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56348682205439046383694191 84523023308158569575541287)
    ·
      refine ⟨126784534962237854363311931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84523023308158569575541287 126784534962237854363311931)
      ·
        refine ⟨190176802443356781544967897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126784534962237854363311931 190176802443356781544967897)
        ·
          refine ⟨142632601832517586158725923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190176802443356781544967897 142632601832517586158725923)
          ·
            refine ⟨213948902748776379238088885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142632601832517586158725923 213948902748776379238088885)
            ·
              refine ⟨20057709632697785553570833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213948902748776379238088885 20057709632697785553570833)
              ·
                refine ⟨15043282224523339165178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20057709632697785553570833 15043282224523339165178125)
                ·
                  refine ⟨5641230834196252186941797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15043282224523339165178125 5641230834196252186941797)
                  ·
                    refine ⟨1057730781411797285051587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641230834196252186941797 1057730781411797285051587)
                    ·
                      rfl

theorem cell23_6179770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_6179770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179770 prefixEnd_6179770 := by exact prefixLift 6179770
  have htrace : WordTrace (prefixWord ++ tailWord_6179770) baseStart_6179770 baseEnd_6179770 := by
    simpa [prefixWord, tailWord_6179770, baseEnd_6179770] using wordTrace_append hprefix tailTrace_6179770
  have hstable : (prefixWord ++ tailWord_6179770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179770).length < 2 ^ (prefixWord ++ tailWord_6179770).sum := by decide
  have hdescent : baseEnd_6179770 < baseStart_6179770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179787 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 1, 4]
def baseStart_6179787 : Nat := 118140960795 + 6179787 * 2 ^ 59
def prefixEnd_6179787 : Nat := 4983230072969 + 3 ^ 40 * 6179787 * 2
def baseEnd_6179787 : Nat := 1057733691135506096214061

theorem tailTrace_6179787 : CollatzResearch.WordTrace tailWord_6179787 prefixEnd_6179787 1057733691135506096214061 := by
  unfold tailWord_6179787
  simp only [CollatzResearch.WordTrace]
  refine ⟨225395348862694597438145615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150263565908463064958763743 225395348862694597438145615)
  ·
    refine ⟨338093023294041896157218423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225395348862694597438145615 338093023294041896157218423)
    ·
      refine ⟨507139534941062844235827635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338093023294041896157218423 507139534941062844235827635)
      ·
        refine ⟨760709302411594266353741453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507139534941062844235827635 760709302411594266353741453)
        ·
          refine ⟨285265988404347849882653045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760709302411594266353741453 285265988404347849882653045)
          ·
            refine ⟨26743686412907610926498723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285265988404347849882653045 26743686412907610926498723)
            ·
              refine ⟨40115529619361416389748085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26743686412907610926498723 40115529619361416389748085)
              ·
                refine ⟨3760830901815132786538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40115529619361416389748085 3760830901815132786538883)
                ·
                  refine ⟨5641246352722699179808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760830901815132786538883 5641246352722699179808325)
                  ·
                    refine ⟨1057733691135506096214061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641246352722699179808325 1057733691135506096214061)
                    ·
                      rfl

theorem cell23_6179787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 4].length) (baseStart_6179787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179787 prefixEnd_6179787 := by exact prefixLift 6179787
  have htrace : WordTrace (prefixWord ++ tailWord_6179787) baseStart_6179787 baseEnd_6179787 := by
    simpa [prefixWord, tailWord_6179787, baseEnd_6179787] using wordTrace_append hprefix tailTrace_6179787
  have hstable : (prefixWord ++ tailWord_6179787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179787).length < 2 ^ (prefixWord ++ tailWord_6179787).sum := by decide
  have hdescent : baseEnd_6179787 < baseStart_6179787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179800 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 6]
def baseStart_6179800 : Nat := 118140960795 + 6179800 * 2 ^ 59
def prefixEnd_6179800 : Nat := 4983230072969 + 3 ^ 40 * 6179800 * 2
def baseEnd_6179800 : Nat := 352578638739447415308847

theorem tailTrace_6179800 : CollatzResearch.WordTrace tailWord_6179800 prefixEnd_6179800 352578638739447415308847 := by
  unfold tailWord_6179800
  simp only [CollatzResearch.WordTrace]
  refine ⟨112697911505823750329184427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150263882007765000438912569 112697911505823750329184427)
  ·
    refine ⟨169046867258735625493776641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112697911505823750329184427 169046867258735625493776641)
    ·
      refine ⟨126785150444051719120332481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169046867258735625493776641 126785150444051719120332481)
      ·
        refine ⟨95088862833038789340249361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126785150444051719120332481 95088862833038789340249361)
        ·
          refine ⟨71316647124779092005187021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95088862833038789340249361 71316647124779092005187021)
          ·
            refine ⟨26743742671792159501945133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71316647124779092005187021 26743742671792159501945133)
            ·
              refine ⟨10028903501922059813229425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26743742671792159501945133 10028903501922059813229425)
              ·
                refine ⟨7521677626441544859922069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10028903501922059813229425 7521677626441544859922069)
                ·
                  refine ⟨352578638739447415308847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7521677626441544859922069 352578638739447415308847)
                  ·
                    rfl

theorem cell23_6179800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_6179800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179800 prefixEnd_6179800 := by exact prefixLift 6179800
  have htrace : WordTrace (prefixWord ++ tailWord_6179800) baseStart_6179800 baseEnd_6179800 := by
    simpa [prefixWord, tailWord_6179800, baseEnd_6179800] using wordTrace_append hprefix tailTrace_6179800
  have hstable : (prefixWord ++ tailWord_6179800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179800).length < 2 ^ (prefixWord ++ tailWord_6179800).sum := by decide
  have hdescent : baseEnd_6179800 < baseStart_6179800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179837 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_6179837 : Nat := 118140960795 + 6179837 * 2 ^ 59
def prefixEnd_6179837 : Nat := 4983230072969 + 3 ^ 40 * 6179837 * 2
def baseEnd_6179837 : Nat := 3173226747439243093016953

theorem tailTrace_6179837 : CollatzResearch.WordTrace tailWord_6179837 prefixEnd_6179837 3173226747439243093016953 := by
  unfold tailWord_6179837
  simp only [CollatzResearch.WordTrace]
  refine ⟨225397172512513455977465765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150264781675008970651643843 225397172512513455977465765)
  ·
    refine ⟨42261969846096272995774831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225397172512513455977465765 42261969846096272995774831)
    ·
      refine ⟨63392954769144409493662247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42261969846096272995774831 63392954769144409493662247)
      ·
        refine ⟨95089432153716614240493371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63392954769144409493662247 95089432153716614240493371)
        ·
          refine ⟨142634148230574921360740057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95089432153716614240493371 142634148230574921360740057)
          ·
            refine ⟨106975611172931191020555043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142634148230574921360740057 106975611172931191020555043)
            ·
              refine ⟨160463416759396786530832565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106975611172931191020555043 160463416759396786530832565)
              ·
                refine ⟨15043445321193448737265553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160463416759396786530832565 15043445321193448737265553)
                ·
                  refine ⟨11282583990895086552949165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043445321193448737265553 11282583990895086552949165)
                  ·
                    refine ⟨4230968996585657457355937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11282583990895086552949165 4230968996585657457355937)
                    ·
                      refine ⟨3173226747439243093016953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230968996585657457355937 3173226747439243093016953)
                      ·
                        rfl

theorem cell23_6179837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_6179837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179837 prefixEnd_6179837 := by exact prefixLift 6179837
  have htrace : WordTrace (prefixWord ++ tailWord_6179837) baseStart_6179837 baseEnd_6179837 := by
    simpa [prefixWord, tailWord_6179837, baseEnd_6179837] using wordTrace_append hprefix tailTrace_6179837
  have hstable : (prefixWord ++ tailWord_6179837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179837).length < 2 ^ (prefixWord ++ tailWord_6179837).sum := by decide
  have hdescent : baseEnd_6179837 < baseStart_6179837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179838 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_6179838 : Nat := 118140960795 + 6179838 * 2 ^ 59
def prefixEnd_6179838 : Nat := 4983230072969 + 3 ^ 40 * 6179838 * 2
def baseEnd_6179838 : Nat := 1057742420306632529701483

theorem tailTrace_6179838 : CollatzResearch.WordTrace tailWord_6179838 prefixEnd_6179838 1057742420306632529701483 := by
  unfold tailWord_6179838
  simp only [CollatzResearch.WordTrace]
  refine ⟨28174651123188729143531521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150264805990339888765501445 28174651123188729143531521)
  ·
    refine ⟨21130988342391546857648641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28174651123188729143531521 21130988342391546857648641)
    ·
      refine ⟨15848241256793660143236481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21130988342391546857648641 15848241256793660143236481)
      ·
        refine ⟨11886180942595245107427361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15848241256793660143236481 11886180942595245107427361)
        ·
          refine ⟨8914635706946433830570521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886180942595245107427361 8914635706946433830570521)
          ·
            refine ⟨6685976780209825372927891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914635706946433830570521 6685976780209825372927891)
            ·
              refine ⟨10028965170314738059391837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6685976780209825372927891 10028965170314738059391837)
              ·
                refine ⟨3760861938868026772271939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10028965170314738059391837 3760861938868026772271939)
                ·
                  refine ⟨5641292908302040158407909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760861938868026772271939 5641292908302040158407909)
                  ·
                    refine ⟨1057742420306632529701483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641292908302040158407909 1057742420306632529701483)
                    ·
                      rfl

theorem cell23_6179838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_6179838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179838 prefixEnd_6179838 := by exact prefixLift 6179838
  have htrace : WordTrace (prefixWord ++ tailWord_6179838) baseStart_6179838 baseEnd_6179838 := by
    simpa [prefixWord, tailWord_6179838, baseEnd_6179838] using wordTrace_append hprefix tailTrace_6179838
  have hstable : (prefixWord ++ tailWord_6179838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179838).length < 2 ^ (prefixWord ++ tailWord_6179838).sum := by decide
  have hdescent : baseEnd_6179838 < baseStart_6179838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179854 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6179854 : Nat := 118140960795 + 6179854 * 2 ^ 59
def prefixEnd_6179854 : Nat := 4983230072969 + 3 ^ 40 * 6179854 * 2
def baseEnd_6179854 : Nat := 3173235476610369526504375

theorem tailTrace_6179854 : CollatzResearch.WordTrace tailWord_6179854 prefixEnd_6179854 3173235476610369526504375 := by
  unfold tailWord_6179854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28174724069181483485104327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150265195035634578587223077 28174724069181483485104327)
  ·
    refine ⟨42262086103772225227656491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28174724069181483485104327 42262086103772225227656491)
    ·
      refine ⟨63393129155658337841484737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42262086103772225227656491 63393129155658337841484737)
      ·
        refine ⟨47544846866743753381113553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63393129155658337841484737 47544846866743753381113553)
        ·
          refine ⟨35658635150057815035835165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47544846866743753381113553 35658635150057815035835165)
          ·
            refine ⟨13371988181271680638438187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35658635150057815035835165 13371988181271680638438187)
            ·
              refine ⟨20057982271907520957657281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13371988181271680638438187 20057982271907520957657281)
              ·
                refine ⟨15043486703930640718242961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20057982271907520957657281 15043486703930640718242961)
                ·
                  refine ⟨11282615027947980538682221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043486703930640718242961 11282615027947980538682221)
                  ·
                    refine ⟨4230980635480492702005833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11282615027947980538682221 4230980635480492702005833)
                    ·
                      refine ⟨3173235476610369526504375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4230980635480492702005833 3173235476610369526504375)
                      ·
                        rfl

theorem cell23_6179854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6179854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179854 prefixEnd_6179854 := by exact prefixLift 6179854
  have htrace : WordTrace (prefixWord ++ tailWord_6179854) baseStart_6179854 baseEnd_6179854 := by
    simpa [prefixWord, tailWord_6179854, baseEnd_6179854] using wordTrace_append hprefix tailTrace_6179854
  have hstable : (prefixWord ++ tailWord_6179854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179854).length < 2 ^ (prefixWord ++ tailWord_6179854).sum := by decide
  have hdescent : baseEnd_6179854 < baseStart_6179854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179877 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_6179877 : Nat := 118140960795 + 6179877 * 2 ^ 59
def prefixEnd_6179877 : Nat := 4983230072969 + 3 ^ 40 * 6179877 * 2
def baseEnd_6179877 : Nat := 1057749095555140978838923

theorem tailTrace_6179877 : CollatzResearch.WordTrace tailWord_6179877 prefixEnd_6179877 1057749095555140978838923 := by
  unfold tailWord_6179877
  simp only [CollatzResearch.WordTrace]
  refine ⟨225398631432368542808921885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150265754288245695205947923 225398631432368542808921885)
  ·
    refine ⟨84524486787138203553345707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225398631432368542808921885 84524486787138203553345707)
    ·
      refine ⟨126786730180707305330018561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84524486787138203553345707 126786730180707305330018561)
      ·
        refine ⟨95090047635530478997513921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126786730180707305330018561 95090047635530478997513921)
        ·
          refine ⟨71317535726647859248135441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95090047635530478997513921 71317535726647859248135441)
          ·
            refine ⟨53488151794985894436101581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71317535726647859248135441 53488151794985894436101581)
            ·
              refine ⟨20058056923119710413538093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53488151794985894436101581 20058056923119710413538093)
              ·
                refine ⟨7521771346169891405076785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20058056923119710413538093 7521771346169891405076785)
                ·
                  refine ⟨5641328509627418553807589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521771346169891405076785 5641328509627418553807589)
                  ·
                    refine ⟨1057749095555140978838923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641328509627418553807589 1057749095555140978838923)
                    ·
                      rfl

theorem cell23_6179877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_6179877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179877 prefixEnd_6179877 := by exact prefixLift 6179877
  have htrace : WordTrace (prefixWord ++ tailWord_6179877) baseStart_6179877 baseEnd_6179877 := by
    simpa [prefixWord, tailWord_6179877, baseEnd_6179877] using wordTrace_append hprefix tailTrace_6179877
  have hstable : (prefixWord ++ tailWord_6179877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179877).length < 2 ^ (prefixWord ++ tailWord_6179877).sum := by decide
  have hdescent : baseEnd_6179877 < baseStart_6179877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179897 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6179897 : Nat := 118140960795 + 6179897 * 2 ^ 59
def prefixEnd_6179897 : Nat := 4983230072969 + 3 ^ 40 * 6179897 * 2
def baseEnd_6179897 : Nat := 3173257556278512858266677

theorem tailTrace_6179897 : CollatzResearch.WordTrace tailWord_6179897 prefixEnd_6179897 3173257556278512858266677 := by
  unfold tailWord_6179897
  simp only [CollatzResearch.WordTrace]
  refine ⟨225399360892296086224649945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150266240594864057483099963 225399360892296086224649945)
  ·
    refine ⟨169049520669222064668487459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225399360892296086224649945 169049520669222064668487459)
    ·
      refine ⟨253574281003833097002731189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169049520669222064668487459 253574281003833097002731189)
      ·
        refine ⟨23772588844109352844006049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253574281003833097002731189 23772588844109352844006049)
        ·
          refine ⟨17829441633082014633004537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23772588844109352844006049 17829441633082014633004537)
          ·
            refine ⟨13372081224811510974753403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17829441633082014633004537 13372081224811510974753403)
            ·
              refine ⟨20058121837217266462130105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372081224811510974753403 20058121837217266462130105)
              ·
                refine ⟨15043591377912949846597579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20058121837217266462130105 15043591377912949846597579)
                ·
                  refine ⟨22565387066869424769896369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15043591377912949846597579 22565387066869424769896369)
                  ·
                    refine ⟨16924040300152068577422277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22565387066869424769896369 16924040300152068577422277)
                    ·
                      refine ⟨3173257556278512858266677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16924040300152068577422277 3173257556278512858266677)
                      ·
                        rfl

theorem cell23_6179897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6179897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179897 prefixEnd_6179897 := by exact prefixLift 6179897
  have htrace : WordTrace (prefixWord ++ tailWord_6179897) baseStart_6179897 baseEnd_6179897 := by
    simpa [prefixWord, tailWord_6179897, baseEnd_6179897] using wordTrace_append hprefix tailTrace_6179897
  have hstable : (prefixWord ++ tailWord_6179897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179897).length < 2 ^ (prefixWord ++ tailWord_6179897).sum := by decide
  have hdescent : baseEnd_6179897 < baseStart_6179897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179904 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3]
def baseStart_6179904 : Nat := 118140960795 + 6179904 * 2 ^ 59
def prefixEnd_6179904 : Nat := 4983230072969 + 3 ^ 40 * 6179904 * 2
def baseEnd_6179904 : Nat := 3173261150643094330879145

theorem tailTrace_6179904 : CollatzResearch.WordTrace tailWord_6179904 prefixEnd_6179904 3173261150643094330879145 := by
  unfold tailWord_6179904
  simp only [CollatzResearch.WordTrace]
  refine ⟨112699808101635363210077383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150266410802180484280103177 112699808101635363210077383)
  ·
    refine ⟨169049712152453044815116075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112699808101635363210077383 169049712152453044815116075)
    ·
      refine ⟨253574568228679567222674113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169049712152453044815116075 253574568228679567222674113)
      ·
        refine ⟨190180926171509675417005585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253574568228679567222674113 190180926171509675417005585)
        ·
          refine ⟨142635694628632256562754189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190180926171509675417005585 142635694628632256562754189)
          ·
            refine ⟨53488385485737096211032821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142635694628632256562754189 53488385485737096211032821)
            ·
              refine ⟨5014536139287852769784327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53488385485737096211032821 5014536139287852769784327)
              ·
                refine ⟨7521804208931779154676491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014536139287852769784327 7521804208931779154676491)
                ·
                  refine ⟨11282706313397668732014737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521804208931779154676491 11282706313397668732014737)
                  ·
                    refine ⟨8462029735048251549011053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11282706313397668732014737 8462029735048251549011053)
                    ·
                      refine ⟨3173261150643094330879145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462029735048251549011053 3173261150643094330879145)
                      ·
                        rfl

theorem cell23_6179904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_6179904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179904 prefixEnd_6179904 := by exact prefixLift 6179904
  have htrace : WordTrace (prefixWord ++ tailWord_6179904) baseStart_6179904 baseEnd_6179904 := by
    simpa [prefixWord, tailWord_6179904, baseEnd_6179904] using wordTrace_append hprefix tailTrace_6179904
  have hstable : (prefixWord ++ tailWord_6179904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179904).length < 2 ^ (prefixWord ++ tailWord_6179904).sum := by decide
  have hdescent : baseEnd_6179904 < baseStart_6179904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179940 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_6179940 : Nat := 118140960795 + 6179940 * 2 ^ 59
def prefixEnd_6179940 : Nat := 4983230072969 + 3 ^ 40 * 6179940 * 2
def baseEnd_6179940 : Nat := 3173279635946656190028979

theorem tailTrace_6179940 : CollatzResearch.WordTrace tailWord_6179940 prefixEnd_6179940 3173279635946656190028979 := by
  unfold tailWord_6179940
  simp only [CollatzResearch.WordTrace]
  refine ⟨112700464615570152284232637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150267286154093536378976849 112700464615570152284232637)
  ·
    refine ⟨42262674230838807106587239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112700464615570152284232637 42262674230838807106587239)
    ·
      refine ⟨63394011346258210659880859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42262674230838807106587239 63394011346258210659880859)
      ·
        refine ⟨95091017019387315989821289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63394011346258210659880859 95091017019387315989821289)
        ·
          refine ⟨71318262764540486992365967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95091017019387315989821289 71318262764540486992365967)
          ·
            refine ⟨106977394146810730488548951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71318262764540486992365967 106977394146810730488548951)
            ·
              refine ⟨160466091220216095732823427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106977394146810730488548951 160466091220216095732823427)
              ·
                refine ⟨240699136830324143599235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160466091220216095732823427 240699136830324143599235141)
                ·
                  refine ⟨45131088155685776924856589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240699136830324143599235141 45131088155685776924856589)
                  ·
                    refine ⟨16924158058382166346821221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45131088155685776924856589 16924158058382166346821221)
                    ·
                      refine ⟨3173279635946656190028979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16924158058382166346821221 3173279635946656190028979)
                      ·
                        rfl

theorem cell23_6179940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_6179940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179940 prefixEnd_6179940 := by exact prefixLift 6179940
  have htrace : WordTrace (prefixWord ++ tailWord_6179940) baseStart_6179940 baseEnd_6179940 := by
    simpa [prefixWord, tailWord_6179940, baseEnd_6179940] using wordTrace_append hprefix tailTrace_6179940
  have hstable : (prefixWord ++ tailWord_6179940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179940).length < 2 ^ (prefixWord ++ tailWord_6179940).sum := by decide
  have hdescent : baseEnd_6179940 < baseStart_6179940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179960 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_6179960 : Nat := 118140960795 + 6179960 * 2 ^ 59
def prefixEnd_6179960 : Nat := 4983230072969 + 3 ^ 40 * 6179960 * 2
def baseEnd_6179960 : Nat := 3173289905559746111778887

theorem tailTrace_6179960 : CollatzResearch.WordTrace tailWord_6179960 prefixEnd_6179960 3173289905559746111778887 := by
  unfold tailWord_6179960
  simp only [CollatzResearch.WordTrace]
  refine ⟨112700829345533923992096667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150267772460711898656128889 112700829345533923992096667)
  ·
    refine ⟨169051244018300885988145001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112700829345533923992096667 169051244018300885988145001)
    ·
      refine ⟨126788433013725664491108751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169051244018300885988145001 126788433013725664491108751)
      ·
        refine ⟨190182649520588496736663127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126788433013725664491108751 190182649520588496736663127)
        ·
          refine ⟨285273974280882745104994691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190182649520588496736663127 285273974280882745104994691)
          ·
            refine ⟨427910961421324117657492037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285273974280882745104994691 427910961421324117657492037)
            ·
              refine ⟨80233305266498272060779757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427910961421324117657492037 80233305266498272060779757)
              ·
                refine ⟨30087489474936852022792409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80233305266498272060779757 30087489474936852022792409)
                ·
                  refine ⟨22565617106202639017094307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30087489474936852022792409 22565617106202639017094307)
                  ·
                    refine ⟨33848425659303958525641461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22565617106202639017094307 33848425659303958525641461)
                    ·
                      refine ⟨3173289905559746111778887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33848425659303958525641461 3173289905559746111778887)
                      ·
                        rfl

theorem cell23_6179960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_6179960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179960 prefixEnd_6179960 := by exact prefixLift 6179960
  have htrace : WordTrace (prefixWord ++ tailWord_6179960) baseStart_6179960 baseEnd_6179960 := by
    simpa [prefixWord, tailWord_6179960, baseEnd_6179960] using wordTrace_append hprefix tailTrace_6179960
  have hstable : (prefixWord ++ tailWord_6179960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179960).length < 2 ^ (prefixWord ++ tailWord_6179960).sum := by decide
  have hdescent : baseEnd_6179960 < baseStart_6179960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179961 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 1, 3, 2]
def baseStart_6179961 : Nat := 118140960795 + 6179961 * 2 ^ 59
def prefixEnd_6179961 : Nat := 4983230072969 + 3 ^ 40 * 6179961 * 2
def baseEnd_6179961 : Nat := 3173290419040400607866383

theorem tailTrace_6179961 : CollatzResearch.WordTrace tailWord_6179961 prefixEnd_6179961 3173290419040400607866383 := by
  unfold tailWord_6179961
  simp only [CollatzResearch.WordTrace]
  refine ⟨225401695164064225154979737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150267796776042816769986491 225401695164064225154979737)
  ·
    refine ⟨169051271373048168866234803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225401695164064225154979737 169051271373048168866234803)
    ·
      refine ⟨253576907059572253299352205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169051271373048168866234803 253576907059572253299352205)
      ·
        refine ⟨95091340147339594987257077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253576907059572253299352205 95091340147339594987257077)
        ·
          refine ⟨8914813138813087030055351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95091340147339594987257077 8914813138813087030055351)
          ·
            refine ⟨13372219708219630545083027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914813138813087030055351 13372219708219630545083027)
            ·
              refine ⟨20058329562329445817624541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372219708219630545083027 20058329562329445817624541)
              ·
                refine ⟨7521873585873542181609203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20058329562329445817624541 7521873585873542181609203)
                ·
                  refine ⟨11282810378810313272413805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7521873585873542181609203 11282810378810313272413805)
                  ·
                    refine ⟨4231053892053867477155177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11282810378810313272413805 4231053892053867477155177)
                    ·
                      refine ⟨3173290419040400607866383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231053892053867477155177 3173290419040400607866383)
                      ·
                        rfl

theorem cell23_6179961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_6179961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179961 prefixEnd_6179961 := by exact prefixLift 6179961
  have htrace : WordTrace (prefixWord ++ tailWord_6179961) baseStart_6179961 baseEnd_6179961 := by
    simpa [prefixWord, tailWord_6179961, baseEnd_6179961] using wordTrace_append hprefix tailTrace_6179961
  have hstable : (prefixWord ++ tailWord_6179961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179961).length < 2 ^ (prefixWord ++ tailWord_6179961).sum := by decide
  have hdescent : baseEnd_6179961 < baseStart_6179961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6179991 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_6179991 : Nat := 118140960795 + 6179991 * 2 ^ 59
def prefixEnd_6179991 : Nat := 4983230072969 + 3 ^ 40 * 6179991 * 2
def baseEnd_6179991 : Nat := 3173305823460035490491245

theorem tailTrace_6179991 : CollatzResearch.WordTrace tailWord_6179991 prefixEnd_6179991 3173305823460035490491245 := by
  unfold tailWord_6179991
  simp only [CollatzResearch.WordTrace]
  refine ⟨225402789353955540278571827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150268526235970360185714551 225402789353955540278571827)
  ·
    refine ⟨338104184030933310417857741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225402789353955540278571827 338104184030933310417857741)
    ·
      refine ⟨126789069011599991406696653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338104184030933310417857741 126789069011599991406696653)
      ·
        refine ⟨47545900879349996777511245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126789069011599991406696653 47545900879349996777511245)
        ·
          refine ⟨17829712829756248791566717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47545900879349996777511245 17829712829756248791566717)
          ·
            refine ⟨6686142311158593296837519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17829712829756248791566717 6686142311158593296837519)
            ·
              refine ⟨10029213466737889945256279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686142311158593296837519 10029213466737889945256279)
              ·
                refine ⟨15043820200106834917884419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029213466737889945256279 15043820200106834917884419)
                ·
                  refine ⟨22565730300160252376826629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15043820200106834917884419 22565730300160252376826629)
                  ·
                    refine ⟨4231074431280047320654993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22565730300160252376826629 4231074431280047320654993)
                    ·
                      refine ⟨3173305823460035490491245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231074431280047320654993 3173305823460035490491245)
                      ·
                        rfl

theorem cell23_6179991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_6179991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6179991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6179991 prefixEnd_6179991 := by exact prefixLift 6179991
  have htrace : WordTrace (prefixWord ++ tailWord_6179991) baseStart_6179991 baseEnd_6179991 := by
    simpa [prefixWord, tailWord_6179991, baseEnd_6179991] using wordTrace_append hprefix tailTrace_6179991
  have hstable : (prefixWord ++ tailWord_6179991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6179991).length < 2 ^ (prefixWord ++ tailWord_6179991).sum := by decide
  have hdescent : baseEnd_6179991 < baseStart_6179991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6179991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180057 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 5, 4]
def baseStart_6180057 : Nat := 118140960795 + 6180057 * 2 ^ 59
def prefixEnd_6180057 : Nat := 4983230072969 + 3 ^ 40 * 6180057 * 2
def baseEnd_6180057 : Nat := 1057779904394410744088647

theorem tailTrace_6180057 : CollatzResearch.WordTrace tailWord_6180057 prefixEnd_6180057 1057779904394410744088647 := by
  unfold tailWord_6180057
  simp only [CollatzResearch.WordTrace]
  refine ⟨225405196571716433550474425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150270131047810955700316283 225405196571716433550474425)
  ·
    refine ⟨169053897428787325162855819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225405196571716433550474425 169053897428787325162855819)
    ·
      refine ⟨253580846143180987744283729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169053897428787325162855819 253580846143180987744283729)
      ·
        refine ⟨190185634607385740808212797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253580846143180987744283729 190185634607385740808212797)
        ·
          refine ⟨71319612977769652803079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190185634607385740808212797 71319612977769652803079799)
          ·
            refine ⟨106979419466654479204619699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71319612977769652803079799 106979419466654479204619699)
            ·
              refine ⟨160469129199981718806929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106979419466654479204619699 160469129199981718806929549)
              ·
                refine ⟨60175923449993144552598581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160469129199981718806929549 60175923449993144552598581)
                ·
                  refine ⟨5641492823436857301806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60175923449993144552598581 5641492823436857301806117)
                  ·
                    refine ⟨1057779904394410744088647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641492823436857301806117 1057779904394410744088647)
                    ·
                      rfl

theorem cell23_6180057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_6180057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180057 prefixEnd_6180057 := by exact prefixLift 6180057
  have htrace : WordTrace (prefixWord ++ tailWord_6180057) baseStart_6180057 baseEnd_6180057 := by
    simpa [prefixWord, tailWord_6180057, baseEnd_6180057] using wordTrace_append hprefix tailTrace_6180057
  have hstable : (prefixWord ++ tailWord_6180057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180057).length < 2 ^ (prefixWord ++ tailWord_6180057).sum := by decide
  have hdescent : baseEnd_6180057 < baseStart_6180057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180061 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_6180061 : Nat := 118140960795 + 6180061 * 2 ^ 59
def prefixEnd_6180061 : Nat := 4983230072969 + 3 ^ 40 * 6180061 * 2
def baseEnd_6180061 : Nat := 1057780589035283405538641

theorem tailTrace_6180061 : CollatzResearch.WordTrace tailWord_6180061 prefixEnd_6180061 1057780589035283405538641 := by
  unfold tailWord_6180061
  simp only [CollatzResearch.WordTrace]
  refine ⟨225405342463701942233620037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150270228309134628155746691 225405342463701942233620037)
  ·
    refine ⟨42263501711944114168803757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225405342463701942233620037 42263501711944114168803757)
    ·
      refine ⟨15848813141979042813301409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42263501711944114168803757 15848813141979042813301409)
      ·
        refine ⟨11886609856484282109976057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15848813141979042813301409 11886609856484282109976057)
        ·
          refine ⟨8914957392363211582482043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886609856484282109976057 8914957392363211582482043)
          ·
            refine ⟨13372436088544817373723065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914957392363211582482043 13372436088544817373723065)
            ·
              refine ⟨10029327066408613030292299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13372436088544817373723065 10029327066408613030292299)
              ·
                refine ⟨15043990599612919545438449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029327066408613030292299 15043990599612919545438449)
                ·
                  refine ⟨11282992949709689659078837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043990599612919545438449 11282992949709689659078837)
                  ·
                    refine ⟨1057780589035283405538641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11282992949709689659078837 1057780589035283405538641)
                    ·
                      rfl

theorem cell23_6180061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_6180061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180061 prefixEnd_6180061 := by exact prefixLift 6180061
  have htrace : WordTrace (prefixWord ++ tailWord_6180061) baseStart_6180061 baseEnd_6180061 := by
    simpa [prefixWord, tailWord_6180061, baseEnd_6180061] using wordTrace_append hprefix tailTrace_6180061
  have hstable : (prefixWord ++ tailWord_6180061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180061).length < 2 ^ (prefixWord ++ tailWord_6180061).sum := by decide
  have hdescent : baseEnd_6180061 < baseStart_6180061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180064 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_6180064 : Nat := 118140960795 + 6180064 * 2 ^ 59
def prefixEnd_6180064 : Nat := 4983230072969 + 3 ^ 40 * 6180064 * 2
def baseEnd_6180064 : Nat := 3173343307547813704878409

theorem tailTrace_6180064 : CollatzResearch.WordTrace tailWord_6180064 prefixEnd_6180064 3173343307547813704878409 := by
  unfold tailWord_6180064
  simp only [CollatzResearch.WordTrace]
  refine ⟨112702725941345536872989623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150270301255127382497319497 112702725941345536872989623)
  ·
    refine ⟨169054088912018305309484435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112702725941345536872989623 169054088912018305309484435)
    ·
      refine ⟨253581133368027457964226653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169054088912018305309484435 253581133368027457964226653)
      ·
        refine ⟨95092925013010296736584995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253581133368027457964226653 95092925013010296736584995)
        ·
          refine ⟨142639387519515445104877493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95092925013010296736584995 142639387519515445104877493)
          ·
            refine ⟨13372442579954572978582265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142639387519515445104877493 13372442579954572978582265)
            ·
              refine ⟨10029331934965929733936699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13372442579954572978582265 10029331934965929733936699)
              ·
                refine ⟨15043997902448894600905049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029331934965929733936699 15043997902448894600905049)
                ·
                  refine ⟨11282998426836670950678787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043997902448894600905049 11282998426836670950678787)
                  ·
                    refine ⟨16924497640255006426018181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11282998426836670950678787 16924497640255006426018181)
                    ·
                      refine ⟨3173343307547813704878409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16924497640255006426018181 3173343307547813704878409)
                      ·
                        rfl

theorem cell23_6180064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_6180064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180064 prefixEnd_6180064 := by exact prefixLift 6180064
  have htrace : WordTrace (prefixWord ++ tailWord_6180064) baseStart_6180064 baseEnd_6180064 := by
    simpa [prefixWord, tailWord_6180064, baseEnd_6180064] using wordTrace_append hprefix tailTrace_6180064
  have hstable : (prefixWord ++ tailWord_6180064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180064).length < 2 ^ (prefixWord ++ tailWord_6180064).sum := by decide
  have hdescent : baseEnd_6180064 < baseStart_6180064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180098 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6180098 : Nat := 118140960795 + 6180098 * 2 ^ 59
def prefixEnd_6180098 : Nat := 4983230072969 + 3 ^ 40 * 6180098 * 2
def baseEnd_6180098 : Nat := 3173360765890066571853253

theorem tailTrace_6180098 : CollatzResearch.WordTrace tailWord_6180098 prefixEnd_6180098 3173360765890066571853253 := by
  unfold tailWord_6180098
  simp only [CollatzResearch.WordTrace]
  refine ⟨56351672991141974388179237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150271127976378598368477965 56351672991141974388179237)
  ·
    refine ⟨10565938685839120197783607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56351672991141974388179237 10565938685839120197783607)
    ·
      refine ⟨15848908028758680296675411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10565938685839120197783607 15848908028758680296675411)
      ·
        refine ⟨23773362043138020445013117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15848908028758680296675411 23773362043138020445013117)
        ·
          refine ⟨8915010766176757666879919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23773362043138020445013117 8915010766176757666879919)
          ·
            refine ⟨13372516149265136500319879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915010766176757666879919 13372516149265136500319879)
            ·
              refine ⟨20058774223897704750479819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372516149265136500319879 20058774223897704750479819)
              ·
                refine ⟨30088161335846557125719729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20058774223897704750479819 30088161335846557125719729)
                ·
                  refine ⟨22566121001884917844289797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30088161335846557125719729 22566121001884917844289797)
                  ·
                    refine ⟨4231147687853422095804337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22566121001884917844289797 4231147687853422095804337)
                    ·
                      refine ⟨3173360765890066571853253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231147687853422095804337 3173360765890066571853253)
                      ·
                        rfl

theorem cell23_6180098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6180098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180098 prefixEnd_6180098 := by exact prefixLift 6180098
  have htrace : WordTrace (prefixWord ++ tailWord_6180098) baseStart_6180098 baseEnd_6180098 := by
    simpa [prefixWord, tailWord_6180098, baseEnd_6180098] using wordTrace_append hprefix tailTrace_6180098
  have hstable : (prefixWord ++ tailWord_6180098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180098).length < 2 ^ (prefixWord ++ tailWord_6180098).sum := by decide
  have hdescent : baseEnd_6180098 < baseStart_6180098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180148 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6180148 : Nat := 118140960795 + 6180148 * 2 ^ 59
def prefixEnd_6180148 : Nat := 4983230072969 + 3 ^ 40 * 6180148 * 2
def baseEnd_6180148 : Nat := 3173386439922791376228023

theorem tailTrace_6180148 : CollatzResearch.WordTrace tailWord_6180148 prefixEnd_6180148 3173386439922791376228023 := by
  unfold tailWord_6180148
  simp only [CollatzResearch.WordTrace]
  refine ⟨112704257807193378046018549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150272343742924504061358065 112704257807193378046018549)
  ·
    refine ⟨10566024169424379191814239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112704257807193378046018549 10566024169424379191814239)
    ·
      refine ⟨15849036254136568787721359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10566024169424379191814239 15849036254136568787721359)
      ·
        refine ⟨23773554381204853181582039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15849036254136568787721359 23773554381204853181582039)
        ·
          refine ⟨35660331571807279772373059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23773554381204853181582039 35660331571807279772373059)
          ·
            refine ⟨53490497357710919658559589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35660331571807279772373059 53490497357710919658559589)
            ·
              refine ⟨10029468254570797435979923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53490497357710919658559589 10029468254570797435979923)
              ·
                refine ⟨15044202381856196153969885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029468254570797435979923 15044202381856196153969885)
                ·
                  refine ⟨5641575893196073557738707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15044202381856196153969885 5641575893196073557738707)
                  ·
                    refine ⟨8462363839794110336608061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641575893196073557738707 8462363839794110336608061)
                    ·
                      refine ⟨3173386439922791376228023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462363839794110336608061 3173386439922791376228023)
                      ·
                        rfl

theorem cell23_6180148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6180148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180148 prefixEnd_6180148 := by exact prefixLift 6180148
  have htrace : WordTrace (prefixWord ++ tailWord_6180148) baseStart_6180148 baseEnd_6180148 := by
    simpa [prefixWord, tailWord_6180148, baseEnd_6180148] using wordTrace_append hprefix tailTrace_6180148
  have hstable : (prefixWord ++ tailWord_6180148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180148).length < 2 ^ (prefixWord ++ tailWord_6180148).sum := by decide
  have hdescent : baseEnd_6180148 < baseStart_6180148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180177 : List Nat := [1, 2, 2, 1, 4, 1, 3, 9]
def baseStart_6180177 : Nat := 118140960795 + 6180177 * 2 ^ 59
def prefixEnd_6180177 : Nat := 4983230072969 + 3 ^ 40 * 6180177 * 2
def baseEnd_6180177 : Nat := 117533382624510065287607

theorem tailTrace_6180177 : CollatzResearch.WordTrace tailWord_6180177 prefixEnd_6180177 117533382624510065287607 := by
  unfold tailWord_6180177
  simp only [CollatzResearch.WordTrace]
  refine ⟨225409573331281694044842785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150273048887521129363228523 225409573331281694044842785)
  ·
    refine ⟨169057179998461270533632089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225409573331281694044842785 169057179998461270533632089)
    ·
      refine ⟨126792884998845952900224067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169057179998461270533632089 126792884998845952900224067)
      ·
        refine ⟨190189327498268929350336101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126792884998845952900224067 190189327498268929350336101)
        ·
          refine ⟨35660498905925424253188019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190189327498268929350336101 35660498905925424253188019)
          ·
            refine ⟨53490748358888136379782029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35660498905925424253188019 53490748358888136379782029)
            ·
              refine ⟨20059030634583051142418261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53490748358888136379782029 20059030634583051142418261)
              ·
                refine ⟨117533382624510065287607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20059030634583051142418261 117533382624510065287607)
                ·
                  rfl

theorem cell23_6180177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 9].length) (baseStart_6180177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180177 prefixEnd_6180177 := by exact prefixLift 6180177
  have htrace : WordTrace (prefixWord ++ tailWord_6180177) baseStart_6180177 baseEnd_6180177 := by
    simpa [prefixWord, tailWord_6180177, baseEnd_6180177] using wordTrace_append hprefix tailTrace_6180177
  have hstable : (prefixWord ++ tailWord_6180177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180177).length < 2 ^ (prefixWord ++ tailWord_6180177).sum := by decide
  have hdescent : baseEnd_6180177 < baseStart_6180177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180205 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6180205 : Nat := 118140960795 + 6180205 * 2 ^ 59
def prefixEnd_6180205 : Nat := 4983230072969 + 3 ^ 40 * 6180205 * 2
def baseEnd_6180205 : Nat := 3173415708320097653215261

theorem tailTrace_6180205 : CollatzResearch.WordTrace tailWord_6180205 prefixEnd_6180205 3173415708320097653215261 := by
  unfold tailWord_6180205
  simp only [CollatzResearch.WordTrace]
  refine ⟨225410594575180254826862069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150273729716786836551241379 225410594575180254826862069)
  ·
    refine ⟨21132243241423148890018319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225410594575180254826862069 21132243241423148890018319)
    ·
      refine ⟨31698364862134723335027479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21132243241423148890018319 31698364862134723335027479)
      ·
        refine ⟨47547547293202085002541219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31698364862134723335027479 47547547293202085002541219)
        ·
          refine ⟨71321320939803127503811829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47547547293202085002541219 71321320939803127503811829)
          ·
            refine ⟨6686373838106543203482359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71321320939803127503811829 6686373838106543203482359)
            ·
              refine ⟨10029560757159814805223539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686373838106543203482359 10029560757159814805223539)
              ·
                refine ⟨15044341135739722207835309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029560757159814805223539 15044341135739722207835309)
                ·
                  refine ⟨5641627925902395827938241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15044341135739722207835309 5641627925902395827938241)
                  ·
                    refine ⟨4231220944426796870953681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5641627925902395827938241 4231220944426796870953681)
                    ·
                      refine ⟨3173415708320097653215261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231220944426796870953681 3173415708320097653215261)
                      ·
                        rfl

theorem cell23_6180205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6180205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180205 prefixEnd_6180205 := by exact prefixLift 6180205
  have htrace : WordTrace (prefixWord ++ tailWord_6180205) baseStart_6180205 baseEnd_6180205 := by
    simpa [prefixWord, tailWord_6180205, baseEnd_6180205] using wordTrace_append hprefix tailTrace_6180205
  have hstable : (prefixWord ++ tailWord_6180205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180205).length < 2 ^ (prefixWord ++ tailWord_6180205).sum := by decide
  have hdescent : baseEnd_6180205 < baseStart_6180205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180207 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 7]
def baseStart_6180207 : Nat := 118140960795 + 6180207 * 2 ^ 59
def prefixEnd_6180207 : Nat := 4983230072969 + 3 ^ 40 * 6180207 * 2
def baseEnd_6180207 : Nat := 1057805578427135548463417

theorem tailTrace_6180207 : CollatzResearch.WordTrace tailWord_6180207 prefixEnd_6180207 1057805578427135548463417 := by
  unfold tailWord_6180207
  simp only [CollatzResearch.WordTrace]
  refine ⟨225410667521173009168434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150273778347448672778956583 225410667521173009168434875)
  ·
    refine ⟨338116001281759513752652313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225410667521173009168434875 338116001281759513752652313)
    ·
      refine ⟨253587000961319635314489235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338116001281759513752652313 253587000961319635314489235)
      ·
        refine ⟨380380501441979452971733853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253587000961319635314489235 380380501441979452971733853)
        ·
          refine ⟨142642688040742294864400195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380380501441979452971733853 142642688040742294864400195)
          ·
            refine ⟨213964032061113442296600293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142642688040742294864400195 213964032061113442296600293)
            ·
              refine ⟨40118256011458770430612555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213964032061113442296600293 40118256011458770430612555)
              ·
                refine ⟨60177384017188155645918833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40118256011458770430612555 60177384017188155645918833)
                ·
                  refine ⟨45133038012891116734439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60177384017188155645918833 45133038012891116734439125)
                  ·
                    refine ⟨1057805578427135548463417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45133038012891116734439125 1057805578427135548463417)
                    ·
                      rfl

theorem cell23_6180207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_6180207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180207 prefixEnd_6180207 := by exact prefixLift 6180207
  have htrace : WordTrace (prefixWord ++ tailWord_6180207) baseStart_6180207 baseEnd_6180207 := by
    simpa [prefixWord, tailWord_6180207, baseEnd_6180207] using wordTrace_append hprefix tailTrace_6180207
  have hstable : (prefixWord ++ tailWord_6180207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180207).length < 2 ^ (prefixWord ++ tailWord_6180207).sum := by decide
  have hdescent : baseEnd_6180207 < baseStart_6180207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180222 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6180222 : Nat := 118140960795 + 6180222 * 2 ^ 59
def prefixEnd_6180222 : Nat := 4983230072969 + 3 ^ 40 * 6180222 * 2
def baseEnd_6180222 : Nat := 3173424437491224086702683

theorem tailTrace_6180222 : CollatzResearch.WordTrace tailWord_6180222 prefixEnd_6180222 3173424437491224086702683 := by
  unfold tailWord_6180222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28176401827014833341278865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150274143077412444486820613 28176401827014833341278865)
  ·
    refine ⟨21132301370261125005959149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28176401827014833341278865 21132301370261125005959149)
    ·
      refine ⟨7924613013847921877234681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21132301370261125005959149 7924613013847921877234681)
      ·
        refine ⟨5943459760385941407926011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7924613013847921877234681 5943459760385941407926011)
        ·
          refine ⟨8915189640578912111889017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943459760385941407926011 8915189640578912111889017)
          ·
            refine ⟨6686392230434184083916763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8915189640578912111889017 6686392230434184083916763)
            ·
              refine ⟨10029588345651276125875145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686392230434184083916763 10029588345651276125875145)
              ·
                refine ⟨7522191259238457094406359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10029588345651276125875145 7522191259238457094406359)
                ·
                  refine ⟨11283286888857685641609539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7522191259238457094406359 11283286888857685641609539)
                  ·
                    refine ⟨16924930333286528462414309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11283286888857685641609539 16924930333286528462414309)
                    ·
                      refine ⟨3173424437491224086702683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16924930333286528462414309 3173424437491224086702683)
                      ·
                        rfl

theorem cell23_6180222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6180222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180222 prefixEnd_6180222 := by exact prefixLift 6180222
  have htrace : WordTrace (prefixWord ++ tailWord_6180222) baseStart_6180222 baseEnd_6180222 := by
    simpa [prefixWord, tailWord_6180222, baseEnd_6180222] using wordTrace_append hprefix tailTrace_6180222
  have hstable : (prefixWord ++ tailWord_6180222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180222).length < 2 ^ (prefixWord ++ tailWord_6180222).sum := by decide
  have hdescent : baseEnd_6180222 < baseStart_6180222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180225 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6180225 : Nat := 118140960795 + 6180225 * 2 ^ 59
def prefixEnd_6180225 : Nat := 4983230072969 + 3 ^ 40 * 6180225 * 2
def baseEnd_6180225 : Nat := 3173425977933187574965169

theorem tailTrace_6180225 : CollatzResearch.WordTrace tailWord_6180225 prefixEnd_6180225 3173425977933187574965169 := by
  unfold tailWord_6180225
  simp only [CollatzResearch.WordTrace]
  refine ⟨225411324035107798242590129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150274216023405198828393419 225411324035107798242590129)
  ·
    refine ⟨169058493026330848681942597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225411324035107798242590129 169058493026330848681942597)
    ·
      refine ⟨31698467442437034127864237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169058493026330848681942597 31698467442437034127864237)
      ·
        refine ⟨11886925290913887797949089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31698467442437034127864237 11886925290913887797949089)
        ·
          refine ⟨8915193968185415848461817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886925290913887797949089 8915193968185415848461817)
          ·
            refine ⟨6686395476139061886346363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8915193968185415848461817 6686395476139061886346363)
            ·
              refine ⟨10029593214208592829519545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686395476139061886346363 10029593214208592829519545)
              ·
                refine ⟨7522194910656444622139659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10029593214208592829519545 7522194910656444622139659)
                ·
                  refine ⟨11283292365984666933209489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7522194910656444622139659 11283292365984666933209489)
                  ·
                    refine ⟨8462469274488500199907117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11283292365984666933209489 8462469274488500199907117)
                    ·
                      refine ⟨3173425977933187574965169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462469274488500199907117 3173425977933187574965169)
                      ·
                        rfl

theorem cell23_6180225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6180225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180225 prefixEnd_6180225 := by exact prefixLift 6180225
  have htrace : WordTrace (prefixWord ++ tailWord_6180225) baseStart_6180225 baseEnd_6180225 := by
    simpa [prefixWord, tailWord_6180225, baseEnd_6180225] using wordTrace_append hprefix tailTrace_6180225
  have hstable : (prefixWord ++ tailWord_6180225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180225).length < 2 ^ (prefixWord ++ tailWord_6180225).sum := by decide
  have hdescent : baseEnd_6180225 < baseStart_6180225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180238 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6180238 : Nat := 118140960795 + 6180238 * 2 ^ 59
def prefixEnd_6180238 : Nat := 4983230072969 + 3 ^ 40 * 6180238 * 2
def baseEnd_6180238 : Nat := 3173432653181696024102609

theorem tailTrace_6180238 : CollatzResearch.WordTrace tailWord_6180238 prefixEnd_6180238 3173432653181696024102609 := by
  unfold tailWord_6180238
  simp only [CollatzResearch.WordTrace]
  refine ⟨28176474773007587682851671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150274532122707134308542245 28176474773007587682851671)
  ·
    refine ⟨42264712159511381524277507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28176474773007587682851671 42264712159511381524277507)
    ·
      refine ⟨63397068239267072286416261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42264712159511381524277507 63397068239267072286416261)
      ·
        refine ⟨11886950294862576053703049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63397068239267072286416261 11886950294862576053703049)
        ·
          refine ⟨8915212721146932040277287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886950294862576053703049 8915212721146932040277287)
          ·
            refine ⟨13372819081720398060415931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915212721146932040277287 13372819081720398060415931)
            ·
              refine ⟨20059228622580597090623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372819081720398060415931 20059228622580597090623897)
              ·
                refine ⟨15044421466935447817967923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20059228622580597090623897 15044421466935447817967923)
                ·
                  refine ⟨22566632200403171726951885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15044421466935447817967923 22566632200403171726951885)
                  ·
                    refine ⟨8462487075151189397606957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22566632200403171726951885 8462487075151189397606957)
                    ·
                      refine ⟨3173432653181696024102609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462487075151189397606957 3173432653181696024102609)
                      ·
                        rfl

theorem cell23_6180238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6180238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180238 prefixEnd_6180238 := by exact prefixLift 6180238
  have htrace : WordTrace (prefixWord ++ tailWord_6180238) baseStart_6180238 baseEnd_6180238 := by
    simpa [prefixWord, tailWord_6180238, baseEnd_6180238] using wordTrace_append hprefix tailTrace_6180238
  have hstable : (prefixWord ++ tailWord_6180238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180238).length < 2 ^ (prefixWord ++ tailWord_6180238).sum := by decide
  have hdescent : baseEnd_6180238 < baseStart_6180238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180242 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6180242 : Nat := 118140960795 + 6180242 * 2 ^ 59
def prefixEnd_6180242 : Nat := 4983230072969 + 3 ^ 40 * 6180242 * 2
def baseEnd_6180242 : Nat := 3173434707104314008452591

theorem tailTrace_6180242 : CollatzResearch.WordTrace tailWord_6180242 prefixEnd_6180242 3173434707104314008452591 := by
  unfold tailWord_6180242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56352986019011552536489745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150274629384030806763972653 56352986019011552536489745)
  ·
    refine ⟨42264739514258664402367309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56352986019011552536489745 42264739514258664402367309)
    ·
      refine ⟨15849277317846999150887741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42264739514258664402367309 15849277317846999150887741)
      ·
        refine ⟨5943478994192624681582903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15849277317846999150887741 5943478994192624681582903)
        ·
          refine ⟨8915218491288937022374355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943478994192624681582903 8915218491288937022374355)
          ·
            refine ⟨13372827736933405533561533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915218491288937022374355 13372827736933405533561533)
            ·
              refine ⟨5014810401350027075085575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13372827736933405533561533 5014810401350027075085575)
              ·
                refine ⟨7522215602025040612628363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014810401350027075085575 7522215602025040612628363)
                ·
                  refine ⟨11283323403037560918942545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7522215602025040612628363 11283323403037560918942545)
                  ·
                    refine ⟨8462492552278170689206909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11283323403037560918942545 8462492552278170689206909)
                    ·
                      refine ⟨3173434707104314008452591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462492552278170689206909 3173434707104314008452591)
                      ·
                        rfl

theorem cell23_6180242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6180242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180242 prefixEnd_6180242 := by exact prefixLift 6180242
  have htrace : WordTrace (prefixWord ++ tailWord_6180242) baseStart_6180242 baseEnd_6180242 := by
    simpa [prefixWord, tailWord_6180242, baseEnd_6180242] using wordTrace_append hprefix tailTrace_6180242
  have hstable : (prefixWord ++ tailWord_6180242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180242).length < 2 ^ (prefixWord ++ tailWord_6180242).sum := by decide
  have hdescent : baseEnd_6180242 < baseStart_6180242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180324 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_6180324 : Nat := 118140960795 + 6180324 * 2 ^ 59
def prefixEnd_6180324 : Nat := 4983230072969 + 3 ^ 40 * 6180324 * 2
def baseEnd_6180324 : Nat := 3173476812517982687627213

theorem tailTrace_6180324 : CollatzResearch.WordTrace tailWord_6180324 prefixEnd_6180324 3173476812517982687627213 := by
  unfold tailWord_6180324
  simp only [CollatzResearch.WordTrace]
  refine ⟨112707467430874569075222013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150276623241166092100296017 112707467430874569075222013)
  ·
    refine ⟨42265300286577963403208255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112707467430874569075222013 42265300286577963403208255)
    ·
      refine ⟨63397950429866945104812383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42265300286577963403208255 63397950429866945104812383)
      ·
        refine ⟨95096925644800417657218575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63397950429866945104812383 95096925644800417657218575)
        ·
          refine ⟨142645388467200626485827863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95096925644800417657218575 142645388467200626485827863)
          ·
            refine ⟨213968082700800939728741795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142645388467200626485827863 213968082700800939728741795)
            ·
              refine ⟨320952124051201409593112693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213968082700800939728741795 320952124051201409593112693)
              ·
                refine ⟨30089261629800132149354315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320952124051201409593112693 30089261629800132149354315)
                ·
                  refine ⟨45133892444700198224031473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30089261629800132149354315 45133892444700198224031473)
                  ·
                    refine ⟨33850419333525148668023605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45133892444700198224031473 33850419333525148668023605)
                    ·
                      refine ⟨3173476812517982687627213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33850419333525148668023605 3173476812517982687627213)
                      ·
                        rfl

theorem cell23_6180324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_6180324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180324 prefixEnd_6180324 := by exact prefixLift 6180324
  have htrace : WordTrace (prefixWord ++ tailWord_6180324) baseStart_6180324 baseEnd_6180324 := by
    simpa [prefixWord, tailWord_6180324, baseEnd_6180324] using wordTrace_append hprefix tailTrace_6180324
  have hstable : (prefixWord ++ tailWord_6180324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180324).length < 2 ^ (prefixWord ++ tailWord_6180324).sum := by decide
  have hdescent : baseEnd_6180324 < baseStart_6180324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 4, 2]
def baseStart_6180351 : Nat := 118140960795 + 6180351 * 2 ^ 59
def prefixEnd_6180351 : Nat := 4983230072969 + 3 ^ 40 * 6180351 * 2
def baseEnd_6180351 : Nat := 3173490676495654081989589

theorem tailTrace_6180351 : CollatzResearch.WordTrace tailWord_6180351 prefixEnd_6180351 3173490676495654081989589 := by
  unfold tailWord_6180351
  simp only [CollatzResearch.WordTrace]
  refine ⟨225415919632651321761676907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150277279755100881174451271 225415919632651321761676907)
  ·
    refine ⟨338123879448976982642515361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225415919632651321761676907 338123879448976982642515361)
    ·
      refine ⟨253592909586732736981886521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338123879448976982642515361 253592909586732736981886521)
      ·
        refine ⟨190194682190049552736414891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253592909586732736981886521 190194682190049552736414891)
        ·
          refine ⟨285292023285074329104622337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190194682190049552736414891 285292023285074329104622337)
          ·
            refine ⟨213969017463805746828466753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285292023285074329104622337 213969017463805746828466753)
            ·
              refine ⟨160476763097854310121350065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213969017463805746828466753 160476763097854310121350065)
              ·
                refine ⟨120357572323390732591012549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160476763097854310121350065 120357572323390732591012549)
                ·
                  refine ⟨22567044810635762360814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120357572323390732591012549 22567044810635762360814853)
                  ·
                    refine ⟨4231320901994205442652785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22567044810635762360814853 4231320901994205442652785)
                    ·
                      refine ⟨3173490676495654081989589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231320901994205442652785 3173490676495654081989589)
                      ·
                        rfl

theorem cell23_6180351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_6180351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180351 prefixEnd_6180351 := by exact prefixLift 6180351
  have htrace : WordTrace (prefixWord ++ tailWord_6180351) baseStart_6180351 baseEnd_6180351 := by
    simpa [prefixWord, tailWord_6180351, baseEnd_6180351] using wordTrace_append hprefix tailTrace_6180351
  have hstable : (prefixWord ++ tailWord_6180351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180351).length < 2 ^ (prefixWord ++ tailWord_6180351).sum := by decide
  have hdescent : baseEnd_6180351 < baseStart_6180351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180371 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3]
def baseStart_6180371 : Nat := 118140960795 + 6180371 * 2 ^ 59
def prefixEnd_6180371 : Nat := 4983230072969 + 3 ^ 40 * 6180371 * 2
def baseEnd_6180371 : Nat := 3173500946108744003739497

theorem tailTrace_6180371 : CollatzResearch.WordTrace tailWord_6180371 prefixEnd_6180371 3173500946108744003739497 := by
  unfold tailWord_6180371
  simp only [CollatzResearch.WordTrace]
  refine ⟨225416649092578865177404967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150277766061719243451603311 225416649092578865177404967)
  ·
    refine ⟨338124973638868297766107451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225416649092578865177404967 338124973638868297766107451)
    ·
      refine ⟨507187460458302446649161177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338124973638868297766107451 507187460458302446649161177)
      ·
        refine ⟨380390595343726834986870883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507187460458302446649161177 380390595343726834986870883)
        ·
          refine ⟨570585893015590252480306325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380390595343726834986870883 570585893015590252480306325)
          ·
            refine ⟨26746213735105793085014359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 570585893015590252480306325 26746213735105793085014359)
            ·
              refine ⟨40119320602658689627521539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26746213735105793085014359 40119320602658689627521539)
              ·
                refine ⟨60178980903988034441282309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40119320602658689627521539 60178980903988034441282309)
                ·
                  refine ⟨11283558919497756457740433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60178980903988034441282309 11283558919497756457740433)
                  ·
                    refine ⟨8462669189623317343305325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11283558919497756457740433 8462669189623317343305325)
                    ·
                      refine ⟨3173500946108744003739497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462669189623317343305325 3173500946108744003739497)
                      ·
                        rfl

theorem cell23_6180371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_6180371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180371 prefixEnd_6180371 := by exact prefixLift 6180371
  have htrace : WordTrace (prefixWord ++ tailWord_6180371) baseStart_6180371 baseEnd_6180371 := by
    simpa [prefixWord, tailWord_6180371, baseEnd_6180371] using wordTrace_append hprefix tailTrace_6180371
  have hstable : (prefixWord ++ tailWord_6180371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180371).length < 2 ^ (prefixWord ++ tailWord_6180371).sum := by decide
  have hdescent : baseEnd_6180371 < baseStart_6180371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
