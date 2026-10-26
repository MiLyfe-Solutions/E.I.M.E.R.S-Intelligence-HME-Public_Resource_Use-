import V185TrunkScan23Chunk1319

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7818877 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7818877 : Nat := 118140960795 + 7818877 * 2 ^ 59
def prefixEnd_7818877 : Nat := 4983230072969 + 3 ^ 40 * 7818877 * 2
def baseEnd_7818877 : Nat := 4014842079384510341479145

theorem tailTrace_7818877 : CollatzResearch.WordTrace tailWord_7818877 prefixEnd_7818877 4014842079384510341479145 := by
  unfold tailWord_7818877
  simp only [CollatzResearch.WordTrace]
  refine ⟨285177872494551461723438885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190118581663034307815625923 285177872494551461723438885)
  ·
    refine ⟨53470851092728399073144791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285177872494551461723438885 53470851092728399073144791)
    ·
      refine ⟨80206276639092598609717187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53470851092728399073144791 80206276639092598609717187)
      ·
        refine ⟨120309414958638897914575781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80206276639092598609717187 120309414958638897914575781)
        ·
          refine ⟨22558015304744793358982959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120309414958638897914575781 22558015304744793358982959)
          ·
            refine ⟨33837022957117190038474439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22558015304744793358982959 33837022957117190038474439)
            ·
              refine ⟨50755534435675785057711659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33837022957117190038474439 50755534435675785057711659)
              ·
                refine ⟨76133301653513677586567489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50755534435675785057711659 76133301653513677586567489)
                ·
                  refine ⟨57099976240135258189925617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76133301653513677586567489 57099976240135258189925617)
                  ·
                    refine ⟨42824982180101443642444213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57099976240135258189925617 42824982180101443642444213)
                    ·
                      refine ⟨4014842079384510341479145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42824982180101443642444213 4014842079384510341479145)
                      ·
                        rfl

theorem cell23_7818877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7818877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818877 prefixEnd_7818877 := by exact prefixLift 7818877
  have htrace : WordTrace (prefixWord ++ tailWord_7818877) baseStart_7818877 baseEnd_7818877 := by
    simpa [prefixWord, tailWord_7818877, baseEnd_7818877] using wordTrace_append hprefix tailTrace_7818877
  have hstable : (prefixWord ++ tailWord_7818877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818877).length < 2 ^ (prefixWord ++ tailWord_7818877).sum := by decide
  have hdescent : baseEnd_7818877 < baseStart_7818877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818917 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_7818917 : Nat := 118140960795 + 7818917 * 2 ^ 59
def prefixEnd_7818917 : Nat := 4983230072969 + 3 ^ 40 * 7818917 * 2
def baseEnd_7818917 : Nat := 4014862618610690184978961

theorem tailTrace_7818917 : CollatzResearch.WordTrace tailWord_7818917 prefixEnd_7818917 4014862618610690184978961 := by
  unfold tailWord_7818917
  simp only [CollatzResearch.WordTrace]
  refine ⟨285179331414406548554895005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190119554276271032369930003 285179331414406548554895005)
  ·
    refine ⟨106942249280402455708085627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285179331414406548554895005 106942249280402455708085627)
    ·
      refine ⟨160413373920603683562128441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106942249280402455708085627 160413373920603683562128441)
      ·
        refine ⟨120310030440452762671596331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160413373920603683562128441 120310030440452762671596331)
        ·
          refine ⟨180465045660679144007394497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120310030440452762671596331 180465045660679144007394497)
          ·
            refine ⟨135348784245509358005545873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180465045660679144007394497 135348784245509358005545873)
            ·
              refine ⟨101511588184132018504159405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135348784245509358005545873 101511588184132018504159405)
              ·
                refine ⟨38066845569049506939059777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101511588184132018504159405 38066845569049506939059777)
                ·
                  refine ⟨28550134176787130204294833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38066845569049506939059777 28550134176787130204294833)
                  ·
                    refine ⟨21412600632590347653221125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28550134176787130204294833 21412600632590347653221125)
                    ·
                      refine ⟨4014862618610690184978961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21412600632590347653221125 4014862618610690184978961)
                      ·
                        rfl

theorem cell23_7818917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_7818917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818917 prefixEnd_7818917 := by exact prefixLift 7818917
  have htrace : WordTrace (prefixWord ++ tailWord_7818917) baseStart_7818917 baseEnd_7818917 := by
    simpa [prefixWord, tailWord_7818917, baseEnd_7818917] using wordTrace_append hprefix tailTrace_7818917
  have hstable : (prefixWord ++ tailWord_7818917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818917).length < 2 ^ (prefixWord ++ tailWord_7818917).sum := by decide
  have hdescent : baseEnd_7818917 < baseStart_7818917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818944 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 5]
def baseStart_7818944 : Nat := 118140960795 + 7818944 * 2 ^ 59
def prefixEnd_7818944 : Nat := 4983230072969 + 3 ^ 40 * 7818944 * 2
def baseEnd_7818944 : Nat := 446097386954262397704593

theorem tailTrace_7818944 : CollatzResearch.WordTrace tailWord_7818944 prefixEnd_7818944 446097386954262397704593 := by
  unfold tailWord_7818944
  simp only [CollatzResearch.WordTrace]
  refine ⟨142590158092654366083063943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190120210790205821444085257 142590158092654366083063943)
  ·
    refine ⟨213885237138981549124595915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142590158092654366083063943 213885237138981549124595915)
    ·
      refine ⟨320827855708472323686893873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213885237138981549124595915 320827855708472323686893873)
      ·
        refine ⟨240620891781354242765170405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320827855708472323686893873 240620891781354242765170405)
        ·
          refine ⟨45116417209003920518469451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240620891781354242765170405 45116417209003920518469451)
          ·
            refine ⟨67674625813505880777704177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45116417209003920518469451 67674625813505880777704177)
            ·
              refine ⟨50755969360129410583278133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67674625813505880777704177 50755969360129410583278133)
              ·
                refine ⟨4758372127512132242182325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50755969360129410583278133 4758372127512132242182325)
                ·
                  refine ⟨446097386954262397704593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758372127512132242182325 446097386954262397704593)
                  ·
                    rfl

theorem cell23_7818944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 5].length) (baseStart_7818944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818944 prefixEnd_7818944 := by exact prefixLift 7818944
  have htrace : WordTrace (prefixWord ++ tailWord_7818944) baseStart_7818944 baseEnd_7818944 := by
    simpa [prefixWord, tailWord_7818944, baseEnd_7818944] using wordTrace_append hprefix tailTrace_7818944
  have hstable : (prefixWord ++ tailWord_7818944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818944).length < 2 ^ (prefixWord ++ tailWord_7818944).sum := by decide
  have hdescent : baseEnd_7818944 < baseStart_7818944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818961 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 5]
def baseStart_7818961 : Nat := 118140960795 + 7818961 * 2 ^ 59
def prefixEnd_7818961 : Nat := 4983230072969 + 3 ^ 40 * 7818961 * 2
def baseEnd_7818961 : Nat := 446098356862165334758751

theorem tailTrace_7818961 : CollatzResearch.WordTrace tailWord_7818961 prefixEnd_7818961 446098356862165334758751 := by
  unfold tailWord_7818961
  simp only [CollatzResearch.WordTrace]
  refine ⟨285180936226247144069496737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190120624150831429379664491 285180936226247144069496737)
  ·
    refine ⟨213885702169685358052122553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285180936226247144069496737 213885702169685358052122553)
    ·
      refine ⟨160414276627264018539091915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213885702169685358052122553 160414276627264018539091915)
      ·
        refine ⟨240621414940896027808637873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160414276627264018539091915 240621414940896027808637873)
        ·
          refine ⟨180466061205672020856478405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240621414940896027808637873 180466061205672020856478405)
          ·
            refine ⟨33837386476063503910589701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180466061205672020856478405 33837386476063503910589701)
            ·
              refine ⟨6344509964261906983235569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33837386476063503910589701 6344509964261906983235569)
              ·
                refine ⟨4758382473196430237426677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344509964261906983235569 4758382473196430237426677)
                ·
                  refine ⟨446098356862165334758751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758382473196430237426677 446098356862165334758751)
                  ·
                    rfl

theorem cell23_7818961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 5].length) (baseStart_7818961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818961 prefixEnd_7818961 := by exact prefixLift 7818961
  have htrace : WordTrace (prefixWord ++ tailWord_7818961) baseStart_7818961 baseEnd_7818961 := by
    simpa [prefixWord, tailWord_7818961, baseEnd_7818961] using wordTrace_append hprefix tailTrace_7818961
  have hstable : (prefixWord ++ tailWord_7818961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818961).length < 2 ^ (prefixWord ++ tailWord_7818961).sum := by decide
  have hdescent : baseEnd_7818961 < baseStart_7818961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818967 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7818967 : Nat := 118140960795 + 7818967 * 2 ^ 59
def prefixEnd_7818967 : Nat := 4983230072969 + 3 ^ 40 * 7818967 * 2
def baseEnd_7818967 : Nat := 4014888292643414989353731

theorem tailTrace_7818967 : CollatzResearch.WordTrace tailWord_7818967 prefixEnd_7818967 4014888292643414989353731 := by
  unfold tailWord_7818967
  simp only [CollatzResearch.WordTrace]
  refine ⟨285181155064225407094215155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190120770042816938062810103 285181155064225407094215155)
  ·
    refine ⟨427771732596338110641322733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285181155064225407094215155 427771732596338110641322733)
    ·
      refine ⟨160414399723626791490496025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427771732596338110641322733 160414399723626791490496025)
      ·
        refine ⟨120310799792720093617872019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160414399723626791490496025 120310799792720093617872019)
        ·
          refine ⟨180466199689080140426808029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120310799792720093617872019 180466199689080140426808029)
          ·
            refine ⟨67674824883405052660053011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180466199689080140426808029 67674824883405052660053011)
            ·
              refine ⟨101512237325107578990079517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67674824883405052660053011 101512237325107578990079517)
              ·
                refine ⟨38067088996915342121279819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101512237325107578990079517 38067088996915342121279819)
                ·
                  refine ⟨57100633495373013181919729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38067088996915342121279819 57100633495373013181919729)
                  ·
                    refine ⟨42825475121529759886439797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57100633495373013181919729 42825475121529759886439797)
                    ·
                      refine ⟨4014888292643414989353731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42825475121529759886439797 4014888292643414989353731)
                      ·
                        rfl

theorem cell23_7818967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7818967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818967 prefixEnd_7818967 := by exact prefixLift 7818967
  have htrace : WordTrace (prefixWord ++ tailWord_7818967) baseStart_7818967 baseEnd_7818967 := by
    simpa [prefixWord, tailWord_7818967, baseEnd_7818967] using wordTrace_append hprefix tailTrace_7818967
  have hstable : (prefixWord ++ tailWord_7818967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818967).length < 2 ^ (prefixWord ++ tailWord_7818967).sum := by decide
  have hdescent : baseEnd_7818967 < baseStart_7818967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818994 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7818994 : Nat := 118140960795 + 7818994 * 2 ^ 59
def prefixEnd_7818994 : Nat := 4983230072969 + 3 ^ 40 * 7818994 * 2
def baseEnd_7818994 : Nat := 4014902156621086383716107

theorem tailTrace_7818994 : CollatzResearch.WordTrace tailWord_7818994 prefixEnd_7818994 4014902156621086383716107 := by
  unfold tailWord_7818994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71295534958781897676362009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190121426556751727136965357 71295534958781897676362009)
  ·
    refine ⟨53471651219086423257271507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71295534958781897676362009 53471651219086423257271507)
    ·
      refine ⟨80207476828629634885907261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53471651219086423257271507 80207476828629634885907261)
      ·
        refine ⟨30077803810736113082215223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80207476828629634885907261 30077803810736113082215223)
        ·
          refine ⟨45116705716104169623322835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30077803810736113082215223 45116705716104169623322835)
          ·
            refine ⟨67675058574156254434984253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45116705716104169623322835 67675058574156254434984253)
            ·
              refine ⟨25378146965308595413119095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67675058574156254434984253 25378146965308595413119095)
              ·
                refine ⟨38067220447962893119678643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25378146965308595413119095 38067220447962893119678643)
                ·
                  refine ⟨57100830671944339679517965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38067220447962893119678643 57100830671944339679517965)
                  ·
                    refine ⟨21412811501979127379819237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57100830671944339679517965 21412811501979127379819237)
                    ·
                      refine ⟨4014902156621086383716107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21412811501979127379819237 4014902156621086383716107)
                      ·
                        rfl

theorem cell23_7818994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7818994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818994 prefixEnd_7818994 := by exact prefixLift 7818994
  have htrace : WordTrace (prefixWord ++ tailWord_7818994) baseStart_7818994 baseEnd_7818994 := by
    simpa [prefixWord, tailWord_7818994, baseEnd_7818994] using wordTrace_append hprefix tailTrace_7818994
  have hstable : (prefixWord ++ tailWord_7818994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818994).length < 2 ^ (prefixWord ++ tailWord_7818994).sum := by decide
  have hdescent : baseEnd_7818994 < baseStart_7818994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819004 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_7819004 : Nat := 118140960795 + 7819004 * 2 ^ 59
def prefixEnd_7819004 : Nat := 4983230072969 + 3 ^ 40 * 7819004 * 2
def baseEnd_7819004 : Nat := 1338302430475877114863687

theorem tailTrace_7819004 : CollatzResearch.WordTrace tailWord_7819004 prefixEnd_7819004 1338302430475877114863687 := by
  unfold tailWord_7819004
  simp only [CollatzResearch.WordTrace]
  refine ⟨142591252282545681206656033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190121669710060908275541377 142591252282545681206656033)
  ·
    refine ⟨106943439211909260904992025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142591252282545681206656033 106943439211909260904992025)
    ·
      refine ⟨80207579408931945678744019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106943439211909260904992025 80207579408931945678744019)
      ·
        refine ⟨120311369113397918518116029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80207579408931945678744019 120311369113397918518116029)
        ·
          refine ⟨45116763417524219444293511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120311369113397918518116029 45116763417524219444293511)
          ·
            refine ⟨67675145126286329166440267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45116763417524219444293511 67675145126286329166440267)
            ·
              refine ⟨101512717689429493749660401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67675145126286329166440267 101512717689429493749660401)
              ·
                refine ⟨76134538267072120312245301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101512717689429493749660401 76134538267072120312245301)
                ·
                  refine ⟨7137612962538011279272997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76134538267072120312245301 7137612962538011279272997)
                  ·
                    refine ⟨1338302430475877114863687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7137612962538011279272997 1338302430475877114863687)
                    ·
                      rfl

theorem cell23_7819004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_7819004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819004 prefixEnd_7819004 := by exact prefixLift 7819004
  have htrace : WordTrace (prefixWord ++ tailWord_7819004) baseStart_7819004 baseEnd_7819004 := by
    simpa [prefixWord, tailWord_7819004, baseEnd_7819004] using wordTrace_append hprefix tailTrace_7819004
  have hstable : (prefixWord ++ tailWord_7819004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819004).length < 2 ^ (prefixWord ++ tailWord_7819004).sum := by decide
  have hdescent : baseEnd_7819004 < baseStart_7819004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819007 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_7819007 : Nat := 118140960795 + 7819007 * 2 ^ 59
def prefixEnd_7819007 : Nat := 4983230072969 + 3 ^ 40 * 7819007 * 2
def baseEnd_7819007 : Nat := 4014908831869594832853547

theorem tailTrace_7819007 : CollatzResearch.WordTrace tailWord_7819007 prefixEnd_7819007 4014908831869594832853547 := by
  unfold tailWord_7819007
  simp only [CollatzResearch.WordTrace]
  refine ⟨285182613984080493925671275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190121742656053662617114183 285182613984080493925671275)
  ·
    refine ⟨427773920976120740888506913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285182613984080493925671275 427773920976120740888506913)
    ·
      refine ⟨320830440732090555666380185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427773920976120740888506913 320830440732090555666380185)
      ·
        refine ⟨240622830549067916749785139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320830440732090555666380185 240622830549067916749785139)
        ·
          refine ⟨360934245823601875124677709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240622830549067916749785139 360934245823601875124677709)
          ·
            refine ⟨135350342183850703171754141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360934245823601875124677709 135350342183850703171754141)
            ·
              refine ⟨50756378318944013689407803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135350342183850703171754141 50756378318944013689407803)
              ·
                refine ⟨76134567478416020534111705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50756378318944013689407803 76134567478416020534111705)
                ·
                  refine ⟨57100925608812015400583779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76134567478416020534111705 57100925608812015400583779)
                  ·
                    refine ⟨85651388413218023100875669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57100925608812015400583779 85651388413218023100875669)
                    ·
                      refine ⟨4014908831869594832853547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85651388413218023100875669 4014908831869594832853547)
                      ·
                        rfl

theorem cell23_7819007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_7819007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819007 prefixEnd_7819007 := by exact prefixLift 7819007
  have htrace : WordTrace (prefixWord ++ tailWord_7819007) baseStart_7819007 baseEnd_7819007 := by
    simpa [prefixWord, tailWord_7819007, baseEnd_7819007] using wordTrace_append hprefix tailTrace_7819007
  have hstable : (prefixWord ++ tailWord_7819007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819007).length < 2 ^ (prefixWord ++ tailWord_7819007).sum := by decide
  have hdescent : baseEnd_7819007 < baseStart_7819007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819085 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 6]
def baseStart_7819085 : Nat := 118140960795 + 7819085 * 2 ^ 59
def prefixEnd_7819085 : Nat := 4983230072969 + 3 ^ 40 * 7819085 * 2
def baseEnd_7819085 : Nat := 446105431484516169742021

theorem tailTrace_7819085 : CollatzResearch.WordTrace tailWord_7819085 prefixEnd_7819085 446105431484516169742021 := by
  unfold tailWord_7819085
  simp only [CollatzResearch.WordTrace]
  refine ⟨285185458877797913247010709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190123639251865275498007139 285185458877797913247010709)
  ·
    refine ⟨13368068384896777183453627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285185458877797913247010709 13368068384896777183453627)
    ·
      refine ⟨20052102577345165775180441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13368068384896777183453627 20052102577345165775180441)
      ·
        refine ⟨15039076933008874331385331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20052102577345165775180441 15039076933008874331385331)
        ·
          refine ⟨22558615399513311497077997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15039076933008874331385331 22558615399513311497077997)
          ·
            refine ⟨8459480774817491811404249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22558615399513311497077997 8459480774817491811404249)
            ·
              refine ⟨6344610581113118858553187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8459480774817491811404249 6344610581113118858553187)
              ·
                refine ⟨9516915871669678287829781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344610581113118858553187 9516915871669678287829781)
                ·
                  refine ⟨446105431484516169742021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9516915871669678287829781 446105431484516169742021)
                  ·
                    rfl

theorem cell23_7819085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_7819085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819085 prefixEnd_7819085 := by exact prefixLift 7819085
  have htrace : WordTrace (prefixWord ++ tailWord_7819085) baseStart_7819085 baseEnd_7819085 := by
    simpa [prefixWord, tailWord_7819085, baseEnd_7819085] using wordTrace_append hprefix tailTrace_7819085
  have hstable : (prefixWord ++ tailWord_7819085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819085).length < 2 ^ (prefixWord ++ tailWord_7819085).sum := by decide
  have hdescent : baseEnd_7819085 < baseStart_7819085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819169 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7819169 : Nat := 118140960795 + 7819169 * 2 ^ 59
def prefixEnd_7819169 : Nat := 4983230072969 + 3 ^ 40 * 7819169 * 2
def baseEnd_7819169 : Nat := 4014992015735623199027803

theorem tailTrace_7819169 : CollatzResearch.WordTrace tailWord_7819169 prefixEnd_7819169 4014992015735623199027803 := by
  unfold tailWord_7819169
  simp only [CollatzResearch.WordTrace]
  refine ⟨285188522609493595593068561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190125681739662397062045707 285188522609493595593068561)
  ·
    refine ⟨213891391957120196694801421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285188522609493595593068561 213891391957120196694801421)
    ·
      refine ⟨80209271983920073760550533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213891391957120196694801421 80209271983920073760550533)
      ·
        refine ⟨15039238496985013830103225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80209271983920073760550533 15039238496985013830103225)
        ·
          refine ⟨11279428872738760372577419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15039238496985013830103225 11279428872738760372577419)
          ·
            refine ⟨16919143309108140558866129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11279428872738760372577419 16919143309108140558866129)
            ·
              refine ⟨12689357481831105419149597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16919143309108140558866129 12689357481831105419149597)
              ·
                refine ⟨4758509055686664532181099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12689357481831105419149597 4758509055686664532181099)
                ·
                  refine ⟨7137763583529996798271649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758509055686664532181099 7137763583529996798271649)
                  ·
                    refine ⟨5353322687647497598703737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137763583529996798271649 5353322687647497598703737)
                    ·
                      refine ⟨4014992015735623199027803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353322687647497598703737 4014992015735623199027803)
                      ·
                        rfl

theorem cell23_7819169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7819169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819169 prefixEnd_7819169 := by exact prefixLift 7819169
  have htrace : WordTrace (prefixWord ++ tailWord_7819169) baseStart_7819169 baseEnd_7819169 := by
    simpa [prefixWord, tailWord_7819169, baseEnd_7819169] using wordTrace_append hprefix tailTrace_7819169
  have hstable : (prefixWord ++ tailWord_7819169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819169).length < 2 ^ (prefixWord ++ tailWord_7819169).sum := by decide
  have hdescent : baseEnd_7819169 < baseStart_7819169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819185 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7819185 : Nat := 118140960795 + 7819185 * 2 ^ 59
def prefixEnd_7819185 : Nat := 4983230072969 + 3 ^ 40 * 7819185 * 2
def baseEnd_7819185 : Nat := 4015000231426095136427729

theorem tailTrace_7819185 : CollatzResearch.WordTrace tailWord_7819185 prefixEnd_7819185 4015000231426095136427729 := by
  unfold tailWord_7819185
  simp only [CollatzResearch.WordTrace]
  refine ⟨285189106177435630325651009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190126070784957086883767339 285189106177435630325651009)
  ·
    refine ⟨213891829633076722744238257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285189106177435630325651009 213891829633076722744238257)
    ·
      refine ⟨160418872224807542058178693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213891829633076722744238257 160418872224807542058178693)
      ·
        refine ⟨30078538542151414135908505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160418872224807542058178693 30078538542151414135908505)
        ·
          refine ⟨22558903906613560601931379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30078538542151414135908505 22558903906613560601931379)
          ·
            refine ⟨33838355859920340902897069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22558903906613560601931379 33838355859920340902897069)
            ·
              refine ⟨12689383447470127838586401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33838355859920340902897069 12689383447470127838586401)
              ·
                refine ⟨9517037585602595878939801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12689383447470127838586401 9517037585602595878939801)
                ·
                  refine ⟨7137778189201946909204851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517037585602595878939801 7137778189201946909204851)
                  ·
                    refine ⟨10706667283802920363807277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137778189201946909204851 10706667283802920363807277)
                    ·
                      refine ⟨4015000231426095136427729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706667283802920363807277 4015000231426095136427729)
                      ·
                        rfl

theorem cell23_7819185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7819185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819185 prefixEnd_7819185 := by exact prefixLift 7819185
  have htrace : WordTrace (prefixWord ++ tailWord_7819185) baseStart_7819185 baseEnd_7819185 := by
    simpa [prefixWord, tailWord_7819185, baseEnd_7819185] using wordTrace_append hprefix tailTrace_7819185
  have hstable : (prefixWord ++ tailWord_7819185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819185).length < 2 ^ (prefixWord ++ tailWord_7819185).sum := by decide
  have hdescent : baseEnd_7819185 < baseStart_7819185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819194 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_7819194 : Nat := 118140960795 + 7819194 * 2 ^ 59
def prefixEnd_7819194 : Nat := 4983230072969 + 3 ^ 40 * 7819194 * 2
def baseEnd_7819194 : Nat := 4015004852751985601215187

theorem tailTrace_7819194 : CollatzResearch.WordTrace tailWord_7819194 prefixEnd_7819194 4015004852751985601215187 := by
  unfold tailWord_7819194
  simp only [CollatzResearch.WordTrace]
  refine ⟨71297358608600756215682159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190126289622935349908485757 71297358608600756215682159)
  ·
    refine ⟨106946037912901134323523239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71297358608600756215682159 106946037912901134323523239)
    ·
      refine ⟨160419056869351701485284859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106946037912901134323523239 160419056869351701485284859)
      ·
        refine ⟨240628585304027552227927289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160419056869351701485284859 240628585304027552227927289)
        ·
          refine ⟨180471438978020664170945467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240628585304027552227927289 180471438978020664170945467)
          ·
            refine ⟨270707158467030996256418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180471438978020664170945467 270707158467030996256418201)
            ·
              refine ⟨203030368850273247192313651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270707158467030996256418201 203030368850273247192313651)
              ·
                refine ⟨304545553275409870788470477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203030368850273247192313651 304545553275409870788470477)
                ·
                  refine ⟨114204582478278701545676429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304545553275409870788470477 114204582478278701545676429)
                  ·
                    refine ⟨42826718429354513079628661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114204582478278701545676429 42826718429354513079628661)
                    ·
                      refine ⟨4015004852751985601215187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42826718429354513079628661 4015004852751985601215187)
                      ·
                        rfl

theorem cell23_7819194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_7819194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819194 prefixEnd_7819194 := by exact prefixLift 7819194
  have htrace : WordTrace (prefixWord ++ tailWord_7819194) baseStart_7819194 baseEnd_7819194 := by
    simpa [prefixWord, tailWord_7819194, baseEnd_7819194] using wordTrace_append hprefix tailTrace_7819194
  have hstable : (prefixWord ++ tailWord_7819194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819194).length < 2 ^ (prefixWord ++ tailWord_7819194).sum := by decide
  have hdescent : baseEnd_7819194 < baseStart_7819194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819278 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_7819278 : Nat := 118140960795 + 7819278 * 2 ^ 59
def prefixEnd_7819278 : Nat := 4983230072969 + 3 ^ 40 * 7819278 * 2
def baseEnd_7819278 : Nat := 1338349328375654424188267

theorem tailTrace_7819278 : CollatzResearch.WordTrace tailWord_7819278 prefixEnd_7819278 1338349328375654424188267 := by
  unfold tailWord_7819278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35649062270762338401098311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190128332110732471472524325 35649062270762338401098311)
  ·
    refine ⟨53473593406143507601647467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35649062270762338401098311 53473593406143507601647467)
    ·
      refine ⟨80210390109215261402471201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53473593406143507601647467 80210390109215261402471201)
      ·
        refine ⟨60157792581911446051853401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80210390109215261402471201 60157792581911446051853401)
        ·
          refine ⟨45118344436433584538890051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60157792581911446051853401 45118344436433584538890051)
          ·
            refine ⟨67677516654650376808335077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45118344436433584538890051 67677516654650376808335077)
            ·
              refine ⟨12689534372746945651562827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67677516654650376808335077 12689534372746945651562827)
              ·
                refine ⟨19034301559120418477344241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12689534372746945651562827 19034301559120418477344241)
                ·
                  refine ⟨14275726169340313858008181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19034301559120418477344241 14275726169340313858008181)
                  ·
                    refine ⟨1338349328375654424188267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14275726169340313858008181 1338349328375654424188267)
                    ·
                      rfl

theorem cell23_7819278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_7819278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819278 prefixEnd_7819278 := by exact prefixLift 7819278
  have htrace : WordTrace (prefixWord ++ tailWord_7819278) baseStart_7819278 baseEnd_7819278 := by
    simpa [prefixWord, tailWord_7819278, baseEnd_7819278] using wordTrace_append hprefix tailTrace_7819278
  have hstable : (prefixWord ++ tailWord_7819278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819278).length < 2 ^ (prefixWord ++ tailWord_7819278).sum := by decide
  have hdescent : baseEnd_7819278 < baseStart_7819278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819291 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 7, 4]
def baseStart_7819291 : Nat := 118140960795 + 7819291 * 2 ^ 59
def prefixEnd_7819291 : Nat := 4983230072969 + 3 ^ 40 * 7819291 * 2
def baseEnd_7819291 : Nat := 1338351553458490573900747

theorem tailTrace_7819291 : CollatzResearch.WordTrace tailWord_7819291 prefixEnd_7819291 1338351553458490573900747 := by
  unfold tailWord_7819291
  simp only [CollatzResearch.WordTrace]
  refine ⟨285192972315051610429009727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190128648210034406952673151 285192972315051610429009727)
  ·
    refine ⟨427789458472577415643514591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285192972315051610429009727 427789458472577415643514591)
    ·
      refine ⟨641684187708866123465271887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427789458472577415643514591 641684187708866123465271887)
      ·
        refine ⟨962526281563299185197907831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641684187708866123465271887 962526281563299185197907831)
        ·
          refine ⟨1443789422344948777796861747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962526281563299185197907831 1443789422344948777796861747)
          ·
            refine ⟨2165684133517423166695292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443789422344948777796861747 2165684133517423166695292621)
            ·
              refine ⟨812131550069033687510734733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2165684133517423166695292621 812131550069033687510734733)
              ·
                refine ⟨304549331275887632816525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812131550069033687510734733 304549331275887632816525525)
                ·
                  refine ⟨7137874951778616394137317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304549331275887632816525525 7137874951778616394137317)
                  ·
                    refine ⟨1338351553458490573900747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7137874951778616394137317 1338351553458490573900747)
                    ·
                      rfl

theorem cell23_7819291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 4].length) (baseStart_7819291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819291 prefixEnd_7819291 := by exact prefixLift 7819291
  have htrace : WordTrace (prefixWord ++ tailWord_7819291) baseStart_7819291 baseEnd_7819291 := by
    simpa [prefixWord, tailWord_7819291, baseEnd_7819291] using wordTrace_append hprefix tailTrace_7819291
  have hstable : (prefixWord ++ tailWord_7819291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819291).length < 2 ^ (prefixWord ++ tailWord_7819291).sum := by decide
  have hdescent : baseEnd_7819291 < baseStart_7819291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819298 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7819298 : Nat := 118140960795 + 7819298 * 2 ^ 59
def prefixEnd_7819298 : Nat := 4983230072969 + 3 ^ 40 * 7819298 * 2
def baseEnd_7819298 : Nat := 4015058254740053194314709

theorem tailTrace_7819298 : CollatzResearch.WordTrace tailWord_7819298 prefixEnd_7819298 4015058254740053194314709 := by
  unfold tailWord_7819298
  simp only [CollatzResearch.WordTrace]
  refine ⟨71298306906506562656128637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190128818417350833749676365 71298306906506562656128637)
  ·
    refine ⟨26736865089939960996048239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71298306906506562656128637 26736865089939960996048239)
    ·
      refine ⟨40105297634909941494072359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26736865089939960996048239 40105297634909941494072359)
      ·
        refine ⟨60157946452364912241108539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40105297634909941494072359 60157946452364912241108539)
        ·
          refine ⟨90236919678547368361662809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60157946452364912241108539 90236919678547368361662809)
          ·
            refine ⟨67677689758910526271247107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90236919678547368361662809 67677689758910526271247107)
            ·
              refine ⟨101516534638365789406870661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67677689758910526271247107 101516534638365789406870661)
              ·
                refine ⟨19034350244693585513788249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101516534638365789406870661 19034350244693585513788249)
                ·
                  refine ⟨14275762683520189135341187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19034350244693585513788249 14275762683520189135341187)
                  ·
                    refine ⟨21413644025280283703011781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14275762683520189135341187 21413644025280283703011781)
                    ·
                      refine ⟨4015058254740053194314709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21413644025280283703011781 4015058254740053194314709)
                      ·
                        rfl

theorem cell23_7819298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7819298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819298 prefixEnd_7819298 := by exact prefixLift 7819298
  have htrace : WordTrace (prefixWord ++ tailWord_7819298) baseStart_7819298 baseEnd_7819298 := by
    simpa [prefixWord, tailWord_7819298, baseEnd_7819298] using wordTrace_append hprefix tailTrace_7819298
  have hstable : (prefixWord ++ tailWord_7819298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819298).length < 2 ^ (prefixWord ++ tailWord_7819298).sum := by decide
  have hdescent : baseEnd_7819298 < baseStart_7819298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819331 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3]
def baseStart_7819331 : Nat := 118140960795 + 7819331 * 2 ^ 59
def prefixEnd_7819331 : Nat := 4983230072969 + 3 ^ 40 * 7819331 * 2
def baseEnd_7819331 : Nat := 4015075199601651565202057

theorem tailTrace_7819331 : CollatzResearch.WordTrace tailWord_7819331 prefixEnd_7819331 4015075199601651565202057 := by
  unfold tailWord_7819331
  simp only [CollatzResearch.WordTrace]
  refine ⟨285194431234906697260465847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190129620823271131506977231 285194431234906697260465847)
  ·
    refine ⟨427791646852360045890698771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285194431234906697260465847 427791646852360045890698771)
    ·
      refine ⟨641687470278540068836048157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427791646852360045890698771 641687470278540068836048157)
      ·
        refine ⟨240632801354452525813518059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641687470278540068836048157 240632801354452525813518059)
        ·
          refine ⟨360949202031678788720277089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240632801354452525813518059 360949202031678788720277089)
          ·
            refine ⟨270711901523759091540207817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360949202031678788720277089 270711901523759091540207817)
            ·
              refine ⟨203033926142819318655155863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270711901523759091540207817 203033926142819318655155863)
              ·
                refine ⟨304550889214228977982733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203033926142819318655155863 304550889214228977982733795)
                ·
                  refine ⟨456826333821343466974100693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304550889214228977982733795 456826333821343466974100693)
                  ·
                    refine ⟨10706867198937737507205485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 456826333821343466974100693 10706867198937737507205485)
                    ·
                      refine ⟨4015075199601651565202057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706867198937737507205485 4015075199601651565202057)
                      ·
                        rfl

theorem cell23_7819331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_7819331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819331 prefixEnd_7819331 := by exact prefixLift 7819331
  have htrace : WordTrace (prefixWord ++ tailWord_7819331) baseStart_7819331 baseEnd_7819331 := by
    simpa [prefixWord, tailWord_7819331, baseEnd_7819331] using wordTrace_append hprefix tailTrace_7819331
  have hstable : (prefixWord ++ tailWord_7819331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819331).length < 2 ^ (prefixWord ++ tailWord_7819331).sum := by decide
  have hdescent : baseEnd_7819331 < baseStart_7819331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819342 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_7819342 : Nat := 118140960795 + 7819342 * 2 ^ 59
def prefixEnd_7819342 : Nat := 4983230072969 + 3 ^ 40 * 7819342 * 2
def baseEnd_7819342 : Nat := 1338360282629617007388169

theorem tailTrace_7819342 : CollatzResearch.WordTrace tailWord_7819342 prefixEnd_7819342 1338360282629617007388169 := by
  unfold tailWord_7819342
  simp only [CollatzResearch.WordTrace]
  refine ⟨35649354054733355767389535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190129888291911230759410853 35649354054733355767389535)
  ·
    refine ⟨53474031082100033651084303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35649354054733355767389535 53474031082100033651084303)
    ·
      refine ⟨80211046623150050476626455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53474031082100033651084303 80211046623150050476626455)
      ·
        refine ⟨120316569934725075714939683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80211046623150050476626455 120316569934725075714939683)
        ·
          refine ⟨180474854902087613572409525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120316569934725075714939683 180474854902087613572409525)
          ·
            refine ⟨16919517647070713772413393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180474854902087613572409525 16919517647070713772413393)
            ·
              refine ⟨12689638235303035329310045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16919517647070713772413393 12689638235303035329310045)
              ·
                refine ⟨4758614338238638248491267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12689638235303035329310045 4758614338238638248491267)
                ·
                  refine ⟨7137921507357957372736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758614338238638248491267 7137921507357957372736901)
                  ·
                    refine ⟨1338360282629617007388169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7137921507357957372736901 1338360282629617007388169)
                    ·
                      rfl

theorem cell23_7819342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_7819342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819342 prefixEnd_7819342 := by exact prefixLift 7819342
  have htrace : WordTrace (prefixWord ++ tailWord_7819342) baseStart_7819342 baseEnd_7819342 := by
    simpa [prefixWord, tailWord_7819342, baseEnd_7819342] using wordTrace_append hprefix tailTrace_7819342
  have hstable : (prefixWord ++ tailWord_7819342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819342).length < 2 ^ (prefixWord ++ tailWord_7819342).sum := by decide
  have hdescent : baseEnd_7819342 < baseStart_7819342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819365 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_7819365 : Nat := 118140960795 + 7819365 * 2 ^ 59
def prefixEnd_7819365 : Nat := 4983230072969 + 3 ^ 40 * 7819365 * 2
def baseEnd_7819365 : Nat := 4015092657943904432176901

theorem tailTrace_7819365 : CollatzResearch.WordTrace tailWord_7819365 prefixEnd_7819365 4015092657943904432176901 := by
  unfold tailWord_7819365
  simp only [CollatzResearch.WordTrace]
  refine ⟨285195671316783521067203549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190130447544522347378135699 285195671316783521067203549)
  ·
    refine ⟨106948376743793820400201331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285195671316783521067203549 106948376743793820400201331)
    ·
      refine ⟨160422565115690730600301997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106948376743793820400201331 160422565115690730600301997)
      ·
        refine ⟨60158461918384023975113249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160422565115690730600301997 60158461918384023975113249)
        ·
          refine ⟨45118846438788017981334937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60158461918384023975113249 45118846438788017981334937)
          ·
            refine ⟨33839134829091013486001203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45118846438788017981334937 33839134829091013486001203)
            ·
              refine ⟨50758702243636520229001805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33839134829091013486001203 50758702243636520229001805)
              ·
                refine ⟨19034513341363695085875677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50758702243636520229001805 19034513341363695085875677)
                ·
                  refine ⟨7137942503011385657203379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19034513341363695085875677 7137942503011385657203379)
                  ·
                    refine ⟨10706913754517078485805069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137942503011385657203379 10706913754517078485805069)
                    ·
                      refine ⟨4015092657943904432176901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706913754517078485805069 4015092657943904432176901)
                      ·
                        rfl

theorem cell23_7819365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_7819365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819365 prefixEnd_7819365 := by exact prefixLift 7819365
  have htrace : WordTrace (prefixWord ++ tailWord_7819365) baseStart_7819365 baseEnd_7819365 := by
    simpa [prefixWord, tailWord_7819365, baseEnd_7819365] using wordTrace_append hprefix tailTrace_7819365
  have hstable : (prefixWord ++ tailWord_7819365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819365).length < 2 ^ (prefixWord ++ tailWord_7819365).sum := by decide
  have hdescent : baseEnd_7819365 < baseStart_7819365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819382 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7819382 : Nat := 118140960795 + 7819382 * 2 ^ 59
def prefixEnd_7819382 : Nat := 4983230072969 + 3 ^ 40 * 7819382 * 2
def baseEnd_7819382 : Nat := 4015101387115030865664323

theorem tailTrace_7819382 : CollatzResearch.WordTrace tailWord_7819382 prefixEnd_7819382 4015101387115030865664323 := by
  unfold tailWord_7819382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17824768209857620810660775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190130860905147955313714933 17824768209857620810660775)
  ·
    refine ⟨26737152314786431215991163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17824768209857620810660775 26737152314786431215991163)
    ·
      refine ⟨40105728472179646823986745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737152314786431215991163 40105728472179646823986745)
      ·
        refine ⟨30079296354134735117990059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40105728472179646823986745 30079296354134735117990059)
        ·
          refine ⟨45118944531202102676985089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30079296354134735117990059 45118944531202102676985089)
          ·
            refine ⟨33839208398401577007738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45118944531202102676985089 33839208398401577007738817)
            ·
              refine ⟨25379406298801182755804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33839208398401577007738817 25379406298801182755804113)
              ·
                refine ⟨19034554724100887066853085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25379406298801182755804113 19034554724100887066853085)
                ·
                  refine ⟨7137958021537832650069907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19034554724100887066853085 7137958021537832650069907)
                  ·
                    refine ⟨10706937032306748975104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137958021537832650069907 10706937032306748975104861)
                    ·
                      refine ⟨4015101387115030865664323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706937032306748975104861 4015101387115030865664323)
                      ·
                        rfl

theorem cell23_7819382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7819382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819382 prefixEnd_7819382 := by exact prefixLift 7819382
  have htrace : WordTrace (prefixWord ++ tailWord_7819382) baseStart_7819382 baseEnd_7819382 := by
    simpa [prefixWord, tailWord_7819382, baseEnd_7819382] using wordTrace_append hprefix tailTrace_7819382
  have hstable : (prefixWord ++ tailWord_7819382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819382).length < 2 ^ (prefixWord ++ tailWord_7819382).sum := by decide
  have hdescent : baseEnd_7819382 < baseStart_7819382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819385 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_7819385 : Nat := 118140960795 + 7819385 * 2 ^ 59
def prefixEnd_7819385 : Nat := 4983230072969 + 3 ^ 40 * 7819385 * 2
def baseEnd_7819385 : Nat := 1338367642518998117975603

theorem tailTrace_7819385 : CollatzResearch.WordTrace tailWord_7819385 prefixEnd_7819385 1338367642518998117975603 := by
  unfold tailWord_7819385
  simp only [CollatzResearch.WordTrace]
  refine ⟨285196400776711064482931609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190130933851140709655287739 285196400776711064482931609)
  ·
    refine ⟨213897300582533298362198707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285196400776711064482931609 213897300582533298362198707)
    ·
      refine ⟨320845950873799947543298061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213897300582533298362198707 320845950873799947543298061)
      ·
        refine ⟨120317231577674980328736773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320845950873799947543298061 120317231577674980328736773)
        ·
          refine ⟨22559480920814058811638145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120317231577674980328736773 22559480920814058811638145)
          ·
            refine ⟨16919610690610544108728609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22559480920814058811638145 16919610690610544108728609)
            ·
              refine ⟨12689708017957908081546457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16919610690610544108728609 12689708017957908081546457)
              ·
                refine ⟨9517281013468431061159843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12689708017957908081546457 9517281013468431061159843)
                ·
                  refine ⟨14275921520202646591739765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9517281013468431061159843 14275921520202646591739765)
                  ·
                    refine ⟨1338367642518998117975603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14275921520202646591739765 1338367642518998117975603)
                    ·
                      rfl

theorem cell23_7819385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_7819385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819385 prefixEnd_7819385 := by exact prefixLift 7819385
  have htrace : WordTrace (prefixWord ++ tailWord_7819385) baseStart_7819385 baseEnd_7819385 := by
    simpa [prefixWord, tailWord_7819385, baseEnd_7819385] using wordTrace_append hprefix tailTrace_7819385
  have hstable : (prefixWord ++ tailWord_7819385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819385).length < 2 ^ (prefixWord ++ tailWord_7819385).sum := by decide
  have hdescent : baseEnd_7819385 < baseStart_7819385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819408 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_7819408 : Nat := 118140960795 + 7819408 * 2 ^ 59
def prefixEnd_7819408 : Nat := 4983230072969 + 3 ^ 40 * 7819408 * 2
def baseEnd_7819408 : Nat := 4015114737612047763939203

theorem tailTrace_7819408 : CollatzResearch.WordTrace tailWord_7819408 prefixEnd_7819408 4015114737612047763939203 := by
  unfold tailWord_7819408
  simp only [CollatzResearch.WordTrace]
  refine ⟨142598619827813869705509439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190131493103751826274012585 142598619827813869705509439)
  ·
    refine ⟨213897929741720804558264159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142598619827813869705509439 213897929741720804558264159)
    ·
      refine ⟨320846894612581206837396239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213897929741720804558264159 320846894612581206837396239)
      ·
        refine ⟨481270341918871810256094359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320846894612581206837396239 481270341918871810256094359)
        ·
          refine ⟨721905512878307715384141539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481270341918871810256094359 721905512878307715384141539)
          ·
            refine ⟨1082858269317461573076212309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721905512878307715384141539 1082858269317461573076212309)
            ·
              refine ⟨12689745343564002809486863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1082858269317461573076212309 12689745343564002809486863)
              ·
                refine ⟨19034618015346004214230295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12689745343564002809486863 19034618015346004214230295)
                ·
                  refine ⟨28551927023019006321345443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19034618015346004214230295 28551927023019006321345443)
                  ·
                    refine ⟨42827890534528509482018165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28551927023019006321345443 42827890534528509482018165)
                    ·
                      refine ⟨4015114737612047763939203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42827890534528509482018165 4015114737612047763939203)
                      ·
                        rfl

theorem cell23_7819408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_7819408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819408 prefixEnd_7819408 := by exact prefixLift 7819408
  have htrace : WordTrace (prefixWord ++ tailWord_7819408) baseStart_7819408 baseEnd_7819408 := by
    simpa [prefixWord, tailWord_7819408, baseEnd_7819408] using wordTrace_append hprefix tailTrace_7819408
  have hstable : (prefixWord ++ tailWord_7819408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819408).length < 2 ^ (prefixWord ++ tailWord_7819408).sum := by decide
  have hdescent : baseEnd_7819408 < baseStart_7819408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819416 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7819416 : Nat := 118140960795 + 7819416 * 2 ^ 59
def prefixEnd_7819416 : Nat := 4983230072969 + 3 ^ 40 * 7819416 * 2
def baseEnd_7819416 : Nat := 4015118845457283732639167

theorem tailTrace_7819416 : CollatzResearch.WordTrace tailWord_7819416 prefixEnd_7819416 4015118845457283732639167 := by
  unfold tailWord_7819416
  simp only [CollatzResearch.WordTrace]
  refine ⟨142598765719799378388655051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190131687626399171184873401 142598765719799378388655051)
  ·
    refine ⟨213898148579699067582982577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142598765719799378388655051 213898148579699067582982577)
    ·
      refine ⟨160423611434774300687236933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213898148579699067582982577 160423611434774300687236933)
      ·
        refine ⟨30079427144020181378856925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160423611434774300687236933 30079427144020181378856925)
        ·
          refine ⟨11279785179007568017071347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30079427144020181378856925 11279785179007568017071347)
          ·
            refine ⟨16919677768511352025607021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11279785179007568017071347 16919677768511352025607021)
            ·
              refine ⟨6344879163191757009602633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16919677768511352025607021 6344879163191757009602633)
              ·
                refine ⟨4758659372393817757201975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344879163191757009602633 4758659372393817757201975)
                ·
                  refine ⟨7137989058590726635802963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758659372393817757201975 7137989058590726635802963)
                  ·
                    refine ⟨10706983587886089953704445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137989058590726635802963 10706983587886089953704445)
                    ·
                      refine ⟨4015118845457283732639167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706983587886089953704445 4015118845457283732639167)
                      ·
                        rfl

theorem cell23_7819416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7819416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819416 prefixEnd_7819416 := by exact prefixLift 7819416
  have htrace : WordTrace (prefixWord ++ tailWord_7819416) baseStart_7819416 baseEnd_7819416 := by
    simpa [prefixWord, tailWord_7819416, baseEnd_7819416] using wordTrace_append hprefix tailTrace_7819416
  have hstable : (prefixWord ++ tailWord_7819416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819416).length < 2 ^ (prefixWord ++ tailWord_7819416).sum := by decide
  have hdescent : baseEnd_7819416 < baseStart_7819416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819488 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 6]
def baseStart_7819488 : Nat := 118140960795 + 7819488 * 2 ^ 59
def prefixEnd_7819488 : Nat := 4983230072969 + 3 ^ 40 * 7819488 * 2
def baseEnd_7819488 : Nat := 1338385272021469150312945

theorem tailTrace_7819488 : CollatzResearch.WordTrace tailWord_7819488 prefixEnd_7819488 1338385272021469150312945 := by
  unfold tailWord_7819488
  simp only [CollatzResearch.WordTrace]
  refine ⟨142600078747668956536965559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190133438330225275382620745 142600078747668956536965559)
  ·
    refine ⟨213900118121503434805448339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142600078747668956536965559 213900118121503434805448339)
    ·
      refine ⟨320850177182255152208172509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213900118121503434805448339 320850177182255152208172509)
      ·
        refine ⟨120318816443345682078064691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320850177182255152208172509 120318816443345682078064691)
        ·
          refine ⟨180478224665018523117097037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120318816443345682078064691 180478224665018523117097037)
          ·
            refine ⟨67679334249381946168911389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180478224665018523117097037 67679334249381946168911389)
            ·
              refine ⟨25379750343518229813341771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67679334249381946168911389 25379750343518229813341771)
              ·
                refine ⟨38069625515277344720012657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25379750343518229813341771 38069625515277344720012657)
                ·
                  refine ⟨28552219136458008540009493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38069625515277344720012657 28552219136458008540009493)
                  ·
                    refine ⟨1338385272021469150312945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28552219136458008540009493 1338385272021469150312945)
                    ·
                      rfl

theorem cell23_7819488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_7819488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819488 prefixEnd_7819488 := by exact prefixLift 7819488
  have htrace : WordTrace (prefixWord ++ tailWord_7819488) baseStart_7819488 baseEnd_7819488 := by
    simpa [prefixWord, tailWord_7819488, baseEnd_7819488] using wordTrace_append hprefix tailTrace_7819488
  have hstable : (prefixWord ++ tailWord_7819488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819488).length < 2 ^ (prefixWord ++ tailWord_7819488).sum := by decide
  have hdescent : baseEnd_7819488 < baseStart_7819488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819516 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_7819516 : Nat := 118140960795 + 7819516 * 2 ^ 59
def prefixEnd_7819516 : Nat := 4983230072969 + 3 ^ 40 * 7819516 * 2
def baseEnd_7819516 : Nat := 4015170193522733341388707

theorem tailTrace_7819516 : CollatzResearch.WordTrace tailWord_7819516 prefixEnd_7819516 4015170193522733341388707 := by
  unfold tailWord_7819516
  simp only [CollatzResearch.WordTrace]
  refine ⟨142600589369618236927975201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190134119159490982570633601 142600589369618236927975201)
  ·
    refine ⟨106950442027213677695981401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142600589369618236927975201 106950442027213677695981401)
    ·
      refine ⟨80212831520410258271986051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106950442027213677695981401 80212831520410258271986051)
      ·
        refine ⟨120319247280615387407979077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80212831520410258271986051 120319247280615387407979077)
        ·
          refine ⟨22559858865115385138996077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120319247280615387407979077 22559858865115385138996077)
          ·
            refine ⟨8459947074418269427123529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22559858865115385138996077 8459947074418269427123529)
            ·
              refine ⟨6344960305813702070342647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8459947074418269427123529 6344960305813702070342647)
              ·
                refine ⟨9517440458720553105513971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344960305813702070342647 9517440458720553105513971)
                ·
                  refine ⟨14276160688080829658270957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9517440458720553105513971 14276160688080829658270957)
                  ·
                    refine ⟨5353560258030311121851609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14276160688080829658270957 5353560258030311121851609)
                    ·
                      refine ⟨4015170193522733341388707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353560258030311121851609 4015170193522733341388707)
                      ·
                        rfl

theorem cell23_7819516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_7819516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819516 prefixEnd_7819516 := by exact prefixLift 7819516
  have htrace : WordTrace (prefixWord ++ tailWord_7819516) baseStart_7819516 baseEnd_7819516 := by
    simpa [prefixWord, tailWord_7819516, baseEnd_7819516] using wordTrace_append hprefix tailTrace_7819516
  have hstable : (prefixWord ++ tailWord_7819516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819516).length < 2 ^ (prefixWord ++ tailWord_7819516).sum := by decide
  have hdescent : baseEnd_7819516 < baseStart_7819516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819529 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 2, 2, 2]
def baseStart_7819529 : Nat := 118140960795 + 7819529 * 2 ^ 59
def prefixEnd_7819529 : Nat := 4983230072969 + 3 ^ 40 * 7819529 * 2
def baseEnd_7819529 : Nat := 4015176868771241790526147

theorem tailTrace_7819529 : CollatzResearch.WordTrace tailWord_7819529 prefixEnd_7819529 4015176868771241790526147 := by
  unfold tailWord_7819529
  simp only [CollatzResearch.WordTrace]
  refine ⟨285201652888189377076173641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190134435258792918050782427 285201652888189377076173641)
  ·
    refine ⟨213901239666142032807130231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285201652888189377076173641 213901239666142032807130231)
    ·
      refine ⟨320851859499213049210695347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213901239666142032807130231 320851859499213049210695347)
      ·
        refine ⟨481277789248819573816043021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320851859499213049210695347 481277789248819573816043021)
        ·
          refine ⟨180479170968307340181016133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481277789248819573816043021 180479170968307340181016133)
          ·
            refine ⟨33839844556557626283940525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180479170968307340181016133 33839844556557626283940525)
            ·
              refine ⟨12689941708709109856477697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33839844556557626283940525 12689941708709109856477697)
              ·
                refine ⟨9517456281531832392358273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12689941708709109856477697 9517456281531832392358273)
                ·
                  refine ⟨7138092211148874294268705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517456281531832392358273 7138092211148874294268705)
                  ·
                    refine ⟨5353569158361655720701529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138092211148874294268705 5353569158361655720701529)
                    ·
                      refine ⟨4015176868771241790526147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353569158361655720701529 4015176868771241790526147)
                      ·
                        rfl

theorem cell23_7819529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 2, 2].length) (baseStart_7819529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819529 prefixEnd_7819529 := by exact prefixLift 7819529
  have htrace : WordTrace (prefixWord ++ tailWord_7819529) baseStart_7819529 baseEnd_7819529 := by
    simpa [prefixWord, tailWord_7819529, baseEnd_7819529] using wordTrace_append hprefix tailTrace_7819529
  have hstable : (prefixWord ++ tailWord_7819529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819529).length < 2 ^ (prefixWord ++ tailWord_7819529).sum := by decide
  have hdescent : baseEnd_7819529 < baseStart_7819529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819546 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_7819546 : Nat := 118140960795 + 7819546 * 2 ^ 59
def prefixEnd_7819546 : Nat := 4983230072969 + 3 ^ 40 * 7819546 * 2
def baseEnd_7819546 : Nat := 4015185597942368224013569

theorem tailTrace_7819546 : CollatzResearch.WordTrace tailWord_7819546 prefixEnd_7819546 4015185597942368224013569 := by
  unfold tailWord_7819546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71300568232281947244885623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190134848619418525986361661 71300568232281947244885623)
  ·
    refine ⟨106950852348422920867328435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71300568232281947244885623 106950852348422920867328435)
    ·
      refine ⟨160426278522634381300992653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106950852348422920867328435 160426278522634381300992653)
      ·
        refine ⟨60159854445987892987872245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160426278522634381300992653 60159854445987892987872245)
        ·
          refine ⟨5639986354311364967613023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60159854445987892987872245 5639986354311364967613023)
          ·
            refine ⟨8459979531467047451419535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639986354311364967613023 8459979531467047451419535)
            ·
              refine ⟨12689969297200571177129303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459979531467047451419535 12689969297200571177129303)
              ·
                refine ⟨19034953945800856765693955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12689969297200571177129303 19034953945800856765693955)
                ·
                  refine ⟨28552430918701285148540933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19034953945800856765693955 28552430918701285148540933)
                  ·
                    refine ⟨5353580797256490965351425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28552430918701285148540933 5353580797256490965351425)
                    ·
                      refine ⟨4015185597942368224013569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353580797256490965351425 4015185597942368224013569)
                      ·
                        rfl

theorem cell23_7819546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_7819546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819546 prefixEnd_7819546 := by exact prefixLift 7819546
  have htrace : WordTrace (prefixWord ++ tailWord_7819546) baseStart_7819546 baseEnd_7819546 := by
    simpa [prefixWord, tailWord_7819546, baseEnd_7819546] using wordTrace_append hprefix tailTrace_7819546
  have hstable : (prefixWord ++ tailWord_7819546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819546).length < 2 ^ (prefixWord ++ tailWord_7819546).sum := by decide
  have hdescent : baseEnd_7819546 < baseStart_7819546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819569 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 5]
def baseStart_7819569 : Nat := 118140960795 + 7819569 * 2 ^ 59
def prefixEnd_7819569 : Nat := 4983230072969 + 3 ^ 40 * 7819569 * 2
def baseEnd_7819569 : Nat := 446133045333046848225107

theorem tailTrace_7819569 : CollatzResearch.WordTrace tailWord_7819569 prefixEnd_7819569 446133045333046848225107 := by
  unfold tailWord_7819569
  simp only [CollatzResearch.WordTrace]
  refine ⟨285203111808044463907629761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190135407872029642605086507 285203111808044463907629761)
  ·
    refine ⟨213902333856033347930722321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285203111808044463907629761 213902333856033347930722321)
    ·
      refine ⟨160426750392025010948041741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213902333856033347930722321 160426750392025010948041741)
      ·
        refine ⟨60160031397009379105515653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160426750392025010948041741 60160031397009379105515653)
        ·
          refine ⟨11280005886939258582284185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60160031397009379105515653 11280005886939258582284185)
          ·
            refine ⟨8460004415204443936713139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11280005886939258582284185 8460004415204443936713139)
            ·
              refine ⟨12690006622806665905069709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460004415204443936713139 12690006622806665905069709)
              ·
                refine ⟨4758752483552499714401141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12690006622806665905069709 4758752483552499714401141)
                ·
                  refine ⟨446133045333046848225107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758752483552499714401141 446133045333046848225107)
                  ·
                    rfl

theorem cell23_7819569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 5].length) (baseStart_7819569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819569 prefixEnd_7819569 := by exact prefixLift 7819569
  have htrace : WordTrace (prefixWord ++ tailWord_7819569) baseStart_7819569 baseEnd_7819569 := by
    simpa [prefixWord, tailWord_7819569, baseEnd_7819569] using wordTrace_append hprefix tailTrace_7819569
  have hstable : (prefixWord ++ tailWord_7819569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819569).length < 2 ^ (prefixWord ++ tailWord_7819569).sum := by decide
  have hdescent : baseEnd_7819569 < baseStart_7819569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819582 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7819582 : Nat := 118140960795 + 7819582 * 2 ^ 59
def prefixEnd_7819582 : Nat := 4983230072969 + 3 ^ 40 * 7819582 * 2
def baseEnd_7819582 : Nat := 1338401361081976694387801

theorem tailTrace_7819582 : CollatzResearch.WordTrace tailWord_7819582 prefixEnd_7819582 1338401361081976694387801 := by
  unfold tailWord_7819582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650448244624670890981625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190135723971331578085235333 35650448244624670890981625)
  ·
    refine ⟨26737836183468503168236219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35650448244624670890981625 26737836183468503168236219)
    ·
      refine ⟨40106754275202754752354329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737836183468503168236219 40106754275202754752354329)
      ·
        refine ⟨30080065706402066064265747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40106754275202754752354329 30080065706402066064265747)
        ·
          refine ⟨45120098559603099096398621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30080065706402066064265747 45120098559603099096398621)
          ·
            refine ⟨16920036959851162161149483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45120098559603099096398621 16920036959851162161149483)
            ·
              refine ⟨25380055439776743241724225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16920036959851162161149483 25380055439776743241724225)
              ·
                refine ⟨19035041579832557431293169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25380055439776743241724225 19035041579832557431293169)
                ·
                  refine ⟨14276281184874418073469877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19035041579832557431293169 14276281184874418073469877)
                  ·
                    refine ⟨1338401361081976694387801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14276281184874418073469877 1338401361081976694387801)
                    ·
                      rfl

theorem cell23_7819582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7819582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819582 prefixEnd_7819582 := by exact prefixLift 7819582
  have htrace : WordTrace (prefixWord ++ tailWord_7819582) baseStart_7819582 baseEnd_7819582 := by
    simpa [prefixWord, tailWord_7819582, baseEnd_7819582] using wordTrace_append hprefix tailTrace_7819582
  have hstable : (prefixWord ++ tailWord_7819582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819582).length < 2 ^ (prefixWord ++ tailWord_7819582).sum := by decide
  have hdescent : baseEnd_7819582 < baseStart_7819582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819595 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 3, 4]
def baseStart_7819595 : Nat := 118140960795 + 7819595 * 2 ^ 59
def prefixEnd_7819595 : Nat := 4983230072969 + 3 ^ 40 * 7819595 * 2
def baseEnd_7819595 : Nat := 1338403586164812844100281

theorem tailTrace_7819595 : CollatzResearch.WordTrace tailWord_7819595 prefixEnd_7819595 1338403586164812844100281 := by
  unfold tailWord_7819595
  simp only [CollatzResearch.WordTrace]
  refine ⟨285204060105950270348076239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190136040070633513565384159 285204060105950270348076239)
  ·
    refine ⟨427806090158925405522114359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285204060105950270348076239 427806090158925405522114359)
    ·
      refine ⟨641709135238388108283171539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427806090158925405522114359 641709135238388108283171539)
      ·
        refine ⟨962563702857582162424757309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641709135238388108283171539 962563702857582162424757309)
        ·
          refine ⟨360961388571593310909283991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962563702857582162424757309 360961388571593310909283991)
          ·
            refine ⟨541442082857389966363925987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360961388571593310909283991 541442082857389966363925987)
            ·
              refine ⟨812163124286084949545888981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541442082857389966363925987 812163124286084949545888981)
              ·
                refine ⟨19035073225455116004981773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 812163124286084949545888981 19035073225455116004981773)
                ·
                  refine ⟨7138152459545668501868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19035073225455116004981773 7138152459545668501868165)
                  ·
                    refine ⟨1338403586164812844100281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138152459545668501868165 1338403586164812844100281)
                    ·
                      rfl

theorem cell23_7819595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 4].length) (baseStart_7819595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819595 prefixEnd_7819595 := by exact prefixLift 7819595
  have htrace : WordTrace (prefixWord ++ tailWord_7819595) baseStart_7819595 baseEnd_7819595 := by
    simpa [prefixWord, tailWord_7819595, baseEnd_7819595] using wordTrace_append hprefix tailTrace_7819595
  have hstable : (prefixWord ++ tailWord_7819595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819595).length < 2 ^ (prefixWord ++ tailWord_7819595).sum := by decide
  have hdescent : baseEnd_7819595 < baseStart_7819595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819602 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_7819602 : Nat := 118140960795 + 7819602 * 2 ^ 59
def prefixEnd_7819602 : Nat := 4983230072969 + 3 ^ 40 * 7819602 * 2
def baseEnd_7819602 : Nat := 4015214352859020004913311

theorem tailTrace_7819602 : CollatzResearch.WordTrace tailWord_7819602 prefixEnd_7819602 4015214352859020004913311 := by
  unfold tailWord_7819602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71301078854231227635895265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190136210277949940362387373 71301078854231227635895265)
  ·
    refine ⟨53475809140673420726921449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71301078854231227635895265 53475809140673420726921449)
    ·
      refine ⟨40106856855505065545191087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53475809140673420726921449 40106856855505065545191087)
      ·
        refine ⟨60160285283257598317786631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40106856855505065545191087 60160285283257598317786631)
        ·
          refine ⟨90240427924886397476679947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60160285283257598317786631 90240427924886397476679947)
          ·
            refine ⟨135360641887329596215019921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90240427924886397476679947 135360641887329596215019921)
            ·
              refine ⟨101520481415497197161264941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135360641887329596215019921 101520481415497197161264941)
              ·
                refine ⟨38070180530811448935474353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101520481415497197161264941 38070180530811448935474353)
                ·
                  refine ⟨28552635398108586701605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38070180530811448935474353 28552635398108586701605765)
                  ·
                    refine ⟨5353619137145360006551081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28552635398108586701605765 5353619137145360006551081)
                    ·
                      refine ⟨4015214352859020004913311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353619137145360006551081 4015214352859020004913311)
                      ·
                        rfl

theorem cell23_7819602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_7819602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819602 prefixEnd_7819602 := by exact prefixLift 7819602
  have htrace : WordTrace (prefixWord ++ tailWord_7819602) baseStart_7819602 baseEnd_7819602 := by
    simpa [prefixWord, tailWord_7819602, baseEnd_7819602] using wordTrace_append hprefix tailTrace_7819602
  have hstable : (prefixWord ++ tailWord_7819602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819602).length < 2 ^ (prefixWord ++ tailWord_7819602).sum := by decide
  have hdescent : baseEnd_7819602 < baseStart_7819602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819608 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 10]
def baseStart_7819608 : Nat := 118140960795 + 7819608 * 2 ^ 59
def prefixEnd_7819608 : Nat := 4983230072969 + 3 ^ 40 * 7819608 * 2
def baseEnd_7819608 : Nat := 446135270415882997937587

theorem tailTrace_7819608 : CollatzResearch.WordTrace tailWord_7819608 prefixEnd_7819608 446135270415882997937587 := by
  unfold tailWord_7819608
  simp only [CollatzResearch.WordTrace]
  refine ⟨142602267127451586784149739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190136356169935449045532985 142602267127451586784149739)
  ·
    refine ⟨213903400691177380176224609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142602267127451586784149739 213903400691177380176224609)
    ·
      refine ⟨160427550518383035132168457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213903400691177380176224609 160427550518383035132168457)
      ·
        refine ⟨120320662888787276349126343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160427550518383035132168457 120320662888787276349126343)
        ·
          refine ⟨180480994333180914523689515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120320662888787276349126343 180480994333180914523689515)
          ·
            refine ⟨270721491499771371785534273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180480994333180914523689515 270721491499771371785534273)
            ·
              refine ⟨203041118624828528839150705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270721491499771371785534273 203041118624828528839150705)
              ·
                refine ⟨152280838968621396629363029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203041118624828528839150705 152280838968621396629363029)
                ·
                  refine ⟨446135270415882997937587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152280838968621396629363029 446135270415882997937587)
                  ·
                    rfl

theorem cell23_7819608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 10].length) (baseStart_7819608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819608 prefixEnd_7819608 := by exact prefixLift 7819608
  have htrace : WordTrace (prefixWord ++ tailWord_7819608) baseStart_7819608 baseEnd_7819608 := by
    simpa [prefixWord, tailWord_7819608, baseEnd_7819608] using wordTrace_append hprefix tailTrace_7819608
  have hstable : (prefixWord ++ tailWord_7819608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819608).length < 2 ^ (prefixWord ++ tailWord_7819608).sum := by decide
  have hdescent : baseEnd_7819608 < baseStart_7819608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819629 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_7819629 : Nat := 118140960795 + 7819629 * 2 ^ 59
def prefixEnd_7819629 : Nat := 4983230072969 + 3 ^ 40 * 7819629 * 2
def baseEnd_7819629 : Nat := 1338409405612230466425229

theorem tailTrace_7819629 : CollatzResearch.WordTrace tailWord_7819629 prefixEnd_7819629 1338409405612230466425229 := by
  unfold tailWord_7819629
  simp only [CollatzResearch.WordTrace]
  refine ⟨285205300187827094154813941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190136866791884729436542627 285205300187827094154813941)
  ·
    refine ⟨26737996892608790077013807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285205300187827094154813941 26737996892608790077013807)
    ·
      refine ⟨40106995338913185115520711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737996892608790077013807 40106995338913185115520711)
      ·
        refine ⟨60160493008369777673281067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40106995338913185115520711 60160493008369777673281067)
        ·
          refine ⟨90240739512554666509921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60160493008369777673281067 90240739512554666509921601)
          ·
            refine ⟨67680554634415999882441201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90240739512554666509921601 67680554634415999882441201)
            ·
              refine ⟨50760415975811999911830901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67680554634415999882441201 50760415975811999911830901)
              ·
                refine ⟨4758788997732374991734147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50760415975811999911830901 4758788997732374991734147)
                ·
                  refine ⟨7138183496598562487601221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758788997732374991734147 7138183496598562487601221)
                  ·
                    refine ⟨1338409405612230466425229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138183496598562487601221 1338409405612230466425229)
                    ·
                      rfl

theorem cell23_7819629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_7819629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819629 prefixEnd_7819629 := by exact prefixLift 7819629
  have htrace : WordTrace (prefixWord ++ tailWord_7819629) baseStart_7819629 baseEnd_7819629 := by
    simpa [prefixWord, tailWord_7819629, baseEnd_7819629] using wordTrace_append hprefix tailTrace_7819629
  have hstable : (prefixWord ++ tailWord_7819629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819629).length < 2 ^ (prefixWord ++ tailWord_7819629).sum := by decide
  have hdescent : baseEnd_7819629 < baseStart_7819629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819655 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 5, 5]
def baseStart_7819655 : Nat := 118140960795 + 7819655 * 2 ^ 59
def prefixEnd_7819655 : Nat := 4983230072969 + 3 ^ 40 * 7819655 * 2
def baseEnd_7819655 : Nat := 1338413855777902765850189

theorem tailTrace_7819655 : CollatzResearch.WordTrace tailWord_7819655 prefixEnd_7819655 1338413855777902765850189 := by
  unfold tailWord_7819655
  simp only [CollatzResearch.WordTrace]
  refine ⟨285206248485732900595260419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190137498990488600396840279 285206248485732900595260419)
  ·
    refine ⟨427809372728599350892890629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285206248485732900595260419 427809372728599350892890629)
    ·
      refine ⟨80214257386612378292416993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427809372728599350892890629 80214257386612378292416993)
      ·
        refine ⟨60160693039959283719312745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80214257386612378292416993 60160693039959283719312745)
        ·
          refine ⟨45120519779969462789484559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60160693039959283719312745 45120519779969462789484559)
          ·
            refine ⟨67680779669954194184226839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45120519779969462789484559 67680779669954194184226839)
            ·
              refine ⟨101521169504931291276340259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67680779669954194184226839 101521169504931291276340259)
              ·
                refine ⟨152281754257396936914510389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101521169504931291276340259 152281754257396936914510389)
                ·
                  refine ⟨14276414461630962835735349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152281754257396936914510389 14276414461630962835735349)
                  ·
                    refine ⟨1338413855777902765850189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14276414461630962835735349 1338413855777902765850189)
                    ·
                      rfl

theorem cell23_7819655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_7819655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819655 prefixEnd_7819655 := by exact prefixLift 7819655
  have htrace : WordTrace (prefixWord ++ tailWord_7819655) baseStart_7819655 baseEnd_7819655 := by
    simpa [prefixWord, tailWord_7819655, baseEnd_7819655] using wordTrace_append hprefix tailTrace_7819655
  have hstable : (prefixWord ++ tailWord_7819655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819655).length < 2 ^ (prefixWord ++ tailWord_7819655).sum := by decide
  have hdescent : baseEnd_7819655 < baseStart_7819655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819670 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7819670 : Nat := 118140960795 + 7819670 * 2 ^ 59
def prefixEnd_7819670 : Nat := 4983230072969 + 3 ^ 40 * 7819670 * 2
def baseEnd_7819670 : Nat := 4015249269543525738862999

theorem tailTrace_7819670 : CollatzResearch.WordTrace tailWord_7819670 prefixEnd_7819670 4015249269543525738862999 := by
  unfold tailWord_7819670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17825424723792409884816029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190137863720452372104704309 17825424723792409884816029)
  ·
    refine ⟨6684534271422153706806011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17825424723792409884816029 6684534271422153706806011)
    ·
      refine ⟨10026801407133230560209017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684534271422153706806011 10026801407133230560209017)
      ·
        refine ⟨7520101055349922920156763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10026801407133230560209017 7520101055349922920156763)
        ·
          refine ⟨11280151583024884380235145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520101055349922920156763 11280151583024884380235145)
          ·
            refine ⟨8460113687268663285176359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11280151583024884380235145 8460113687268663285176359)
            ·
              refine ⟨12690170530902994927764539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460113687268663285176359 12690170530902994927764539)
              ·
                refine ⟨19035255796354492391646809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12690170530902994927764539 19035255796354492391646809)
                ·
                  refine ⟨14276441847265869293735107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19035255796354492391646809 14276441847265869293735107)
                  ·
                    refine ⟨21414662770898803940602661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14276441847265869293735107 21414662770898803940602661)
                    ·
                      refine ⟨4015249269543525738862999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21414662770898803940602661 4015249269543525738862999)
                      ·
                        rfl

theorem cell23_7819670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7819670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819670 prefixEnd_7819670 := by exact prefixLift 7819670
  have htrace : WordTrace (prefixWord ++ tailWord_7819670) baseStart_7819670 baseEnd_7819670 := by
    simpa [prefixWord, tailWord_7819670, baseEnd_7819670] using wordTrace_append hprefix tailTrace_7819670
  have hstable : (prefixWord ++ tailWord_7819670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819670).length < 2 ^ (prefixWord ++ tailWord_7819670).sum := by decide
  have hdescent : baseEnd_7819670 < baseStart_7819670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819672 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_7819672 : Nat := 118140960795 + 7819672 * 2 ^ 59
def prefixEnd_7819672 : Nat := 4983230072969 + 3 ^ 40 * 7819672 * 2
def baseEnd_7819672 : Nat := 1338416765501611577012663

theorem tailTrace_7819672 : CollatzResearch.WordTrace tailWord_7819672 prefixEnd_7819672 1338416765501611577012663 := by
  unfold tailWord_7819672
  simp only [CollatzResearch.WordTrace]
  refine ⟨142603434263335656249314635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190137912351114208332419513 142603434263335656249314635)
  ·
    refine ⟨213905151395003484373971953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142603434263335656249314635 213905151395003484373971953)
    ·
      refine ⟨160428863546252613280478965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213905151395003484373971953 160428863546252613280478965)
      ·
        refine ⟨15040205957461182495044903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160428863546252613280478965 15040205957461182495044903)
        ·
          refine ⟨22560308936191773742567355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15040205957461182495044903 22560308936191773742567355)
          ·
            refine ⟨33840463404287660613851033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22560308936191773742567355 33840463404287660613851033)
            ·
              refine ⟨25380347553215745460388275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33840463404287660613851033 25380347553215745460388275)
              ·
                refine ⟨38070521329823618190582413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25380347553215745460388275 38070521329823618190582413)
                ·
                  refine ⟨14276445498683856821468405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38070521329823618190582413 14276445498683856821468405)
                  ·
                    refine ⟨1338416765501611577012663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14276445498683856821468405 1338416765501611577012663)
                    ·
                      rfl

theorem cell23_7819672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_7819672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819672 prefixEnd_7819672 := by exact prefixLift 7819672
  have htrace : WordTrace (prefixWord ++ tailWord_7819672) baseStart_7819672 baseEnd_7819672 := by
    simpa [prefixWord, tailWord_7819672, baseEnd_7819672] using wordTrace_append hprefix tailTrace_7819672
  have hstable : (prefixWord ++ tailWord_7819672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819672).length < 2 ^ (prefixWord ++ tailWord_7819672).sum := by decide
  have hdescent : baseEnd_7819672 < baseStart_7819672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819685 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_7819685 : Nat := 118140960795 + 7819685 * 2 ^ 59
def prefixEnd_7819685 : Nat := 4983230072969 + 3 ^ 40 * 7819685 * 2
def baseEnd_7819685 : Nat := 1338418990584447726725143

theorem tailTrace_7819685 : CollatzResearch.WordTrace tailWord_7819685 prefixEnd_7819685 1338418990584447726725143 := by
  unfold tailWord_7819685
  simp only [CollatzResearch.WordTrace]
  refine ⟨285207342675624215718852509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190138228450416143812568339 285207342675624215718852509)
  ·
    refine ⟨106952753503359080894569691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285207342675624215718852509 106952753503359080894569691)
    ·
      refine ⟨160429130255038621341854537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106952753503359080894569691 160429130255038621341854537)
      ·
        refine ⟨120321847691278966006390903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160429130255038621341854537 120321847691278966006390903)
        ·
          refine ⟨180482771536918449009586355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120321847691278966006390903 180482771536918449009586355)
          ·
            refine ⟨270724157305377673514379533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180482771536918449009586355 270724157305377673514379533)
            ·
              refine ⟨101521558989516627567892325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270724157305377673514379533 101521558989516627567892325)
              ·
                refine ⟨19035292310534367668979811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101521558989516627567892325 19035292310534367668979811)
                ·
                  refine ⟨28552938465801551503469717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19035292310534367668979811 28552938465801551503469717)
                  ·
                    refine ⟨1338418990584447726725143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28552938465801551503469717 1338418990584447726725143)
                    ·
                      rfl

theorem cell23_7819685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_7819685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819685 prefixEnd_7819685 := by exact prefixLift 7819685
  have htrace : WordTrace (prefixWord ++ tailWord_7819685) baseStart_7819685 baseEnd_7819685 := by
    simpa [prefixWord, tailWord_7819685, baseEnd_7819685] using wordTrace_append hprefix tailTrace_7819685
  have hstable : (prefixWord ++ tailWord_7819685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819685).length < 2 ^ (prefixWord ++ tailWord_7819685).sum := by decide
  have hdescent : baseEnd_7819685 < baseStart_7819685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819732 : List Nat := [2, 4, 1, 2, 2, 2, 1, 9]
def baseStart_7819732 : Nat := 118140960795 + 7819732 * 2 ^ 59
def prefixEnd_7819732 : Nat := 4983230072969 + 3 ^ 40 * 7819732 * 2
def baseEnd_7819732 : Nat := 148714115012744610973619

theorem tailTrace_7819732 : CollatzResearch.WordTrace tailWord_7819732 prefixEnd_7819732 148714115012744610973619 := by
  unfold tailWord_7819732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142604528453226971372906725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190139371270969295163875633 142604528453226971372906725)
  ·
    refine ⟨26738349084980057132420011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142604528453226971372906725 26738349084980057132420011)
    ·
      refine ⟨40107523627470085698630017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26738349084980057132420011 40107523627470085698630017)
      ·
        refine ⟨30080642720602564273972513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40107523627470085698630017 30080642720602564273972513)
        ·
          refine ⟨22560482040451923205479385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30080642720602564273972513 22560482040451923205479385)
          ·
            refine ⟨16920361530338942404109539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22560482040451923205479385 16920361530338942404109539)
            ·
              refine ⟨25380542295508413606164309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16920361530338942404109539 25380542295508413606164309)
              ·
                refine ⟨148714115012744610973619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25380542295508413606164309 148714115012744610973619)
                ·
                  rfl

theorem cell23_7819732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 9].length) (baseStart_7819732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819732 prefixEnd_7819732 := by exact prefixLift 7819732
  have htrace : WordTrace (prefixWord ++ tailWord_7819732) baseStart_7819732 baseEnd_7819732 := by
    simpa [prefixWord, tailWord_7819732, baseEnd_7819732] using wordTrace_append hprefix tailTrace_7819732
  have hstable : (prefixWord ++ tailWord_7819732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819732).length < 2 ^ (prefixWord ++ tailWord_7819732).sum := by decide
  have hdescent : baseEnd_7819732 < baseStart_7819732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819743 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 1, 2, 2]
def baseStart_7819743 : Nat := 118140960795 + 7819743 * 2 ^ 59
def prefixEnd_7819743 : Nat := 4983230072969 + 3 ^ 40 * 7819743 * 2
def baseEnd_7819743 : Nat := 4015286753631303953250163

theorem tailTrace_7819743 : CollatzResearch.WordTrace tailWord_7819743 prefixEnd_7819743 4015286753631303953250163 := by
  unfold tailWord_7819743
  simp only [CollatzResearch.WordTrace]
  refine ⟨285209458109414091624463883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190139638739609394416309255 285209458109414091624463883)
  ·
    refine ⟨427814187164121137436695825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285209458109414091624463883 427814187164121137436695825)
    ·
      refine ⟨320860640373090853077521869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427814187164121137436695825 320860640373090853077521869)
      ·
        refine ⟨120322740139909069904070701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320860640373090853077521869 120322740139909069904070701)
        ·
          refine ⟨45121027552465901214026513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120322740139909069904070701 45121027552465901214026513)
          ·
            refine ⟨33840770664349425910519885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45121027552465901214026513 33840770664349425910519885)
            ·
              refine ⟨12690288999131034716444957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33840770664349425910519885 12690288999131034716444957)
              ·
                refine ⟨4758858374674138018666859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12690288999131034716444957 4758858374674138018666859)
                ·
                  refine ⟨7138287562011207028000289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758858374674138018666859 7138287562011207028000289)
                  ·
                    refine ⟨5353715671508405271000217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138287562011207028000289 5353715671508405271000217)
                    ·
                      refine ⟨4015286753631303953250163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5353715671508405271000217 4015286753631303953250163)
                      ·
                        rfl

theorem cell23_7819743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_7819743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819743 prefixEnd_7819743 := by exact prefixLift 7819743
  have htrace : WordTrace (prefixWord ++ tailWord_7819743) baseStart_7819743 baseEnd_7819743 := by
    simpa [prefixWord, tailWord_7819743, baseEnd_7819743] using wordTrace_append hprefix tailTrace_7819743
  have hstable : (prefixWord ++ tailWord_7819743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819743).length < 2 ^ (prefixWord ++ tailWord_7819743).sum := by decide
  have hdescent : baseEnd_7819743 < baseStart_7819743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819749 : List Nat := [1, 3, 1, 5, 3, 1, 9]
def baseStart_7819749 : Nat := 118140960795 + 7819749 * 2 ^ 59
def prefixEnd_7819749 : Nat := 4983230072969 + 3 ^ 40 * 7819749 * 2
def baseEnd_7819749 : Nat := 49571479438459641108335

theorem tailTrace_7819749 : CollatzResearch.WordTrace tailWord_7819749 prefixEnd_7819749 49571479438459641108335 := by
  unfold tailWord_7819749
  simp only [CollatzResearch.WordTrace]
  refine ⟨285209676947392354649182301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190139784631594903099454867 285209676947392354649182301)
  ·
    refine ⟨106953628855272132993443363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285209676947392354649182301 106953628855272132993443363)
    ·
      refine ⟨160430443282908199490165045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106953628855272132993443363 160430443282908199490165045)
      ·
        refine ⟨15040354057772643702202973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160430443282908199490165045 15040354057772643702202973)
        ·
          refine ⟨5640132771664741388326115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15040354057772643702202973 5640132771664741388326115)
          ·
            refine ⟨8460199157497112082489173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640132771664741388326115 8460199157497112082489173)
            ·
              refine ⟨49571479438459641108335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8460199157497112082489173 49571479438459641108335)
              ·
                rfl

theorem cell23_7819749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 9].length) (baseStart_7819749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819749 prefixEnd_7819749 := by exact prefixLift 7819749
  have htrace : WordTrace (prefixWord ++ tailWord_7819749) baseStart_7819749 baseEnd_7819749 := by
    simpa [prefixWord, tailWord_7819749, baseEnd_7819749] using wordTrace_append hprefix tailTrace_7819749
  have hstable : (prefixWord ++ tailWord_7819749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819749).length < 2 ^ (prefixWord ++ tailWord_7819749).sum := by decide
  have hdescent : baseEnd_7819749 < baseStart_7819749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819755 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_7819755 : Nat := 118140960795 + 7819755 * 2 ^ 59
def prefixEnd_7819755 : Nat := 4983230072969 + 3 ^ 40 * 7819755 * 2
def baseEnd_7819755 : Nat := 4015292915399157906300107

theorem tailTrace_7819755 : CollatzResearch.WordTrace tailWord_7819755 prefixEnd_7819755 4015292915399157906300107 := by
  unfold tailWord_7819755
  simp only [CollatzResearch.WordTrace]
  refine ⟨285209895785370617673900719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190139930523580411782600479 285209895785370617673900719)
  ·
    refine ⟨427814843678055926510851079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285209895785370617673900719 427814843678055926510851079)
    ·
      refine ⟨641722265517083889766276619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427814843678055926510851079 641722265517083889766276619)
      ·
        refine ⟨962583398275625834649414929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641722265517083889766276619 962583398275625834649414929)
        ·
          refine ⟨721937548706719375987061197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962583398275625834649414929 721937548706719375987061197)
          ·
            refine ⟨270726580765019765995147949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 721937548706719375987061197 270726580765019765995147949)
            ·
              refine ⟨101522467786882412248180481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270726580765019765995147949 101522467786882412248180481)
              ·
                refine ⟨76141850840161809186135361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101522467786882412248180481 76141850840161809186135361)
                ·
                  refine ⟨57106388130121356889601521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76141850840161809186135361 57106388130121356889601521)
                  ·
                    refine ⟨42829791097591017667201141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57106388130121356889601521 42829791097591017667201141)
                    ·
                      refine ⟨4015292915399157906300107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42829791097591017667201141 4015292915399157906300107)
                      ·
                        rfl

theorem cell23_7819755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_7819755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819755 prefixEnd_7819755 := by exact prefixLift 7819755
  have htrace : WordTrace (prefixWord ++ tailWord_7819755) baseStart_7819755 baseEnd_7819755 := by
    simpa [prefixWord, tailWord_7819755, baseEnd_7819755] using wordTrace_append hprefix tailTrace_7819755
  have hstable : (prefixWord ++ tailWord_7819755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819755).length < 2 ^ (prefixWord ++ tailWord_7819755).sum := by decide
  have hdescent : baseEnd_7819755 < baseStart_7819755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819759 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_7819759 : Nat := 118140960795 + 7819759 * 2 ^ 59
def prefixEnd_7819759 : Nat := 4983230072969 + 3 ^ 40 * 7819759 * 2
def baseEnd_7819759 : Nat := 4015294969321775890650089

theorem tailTrace_7819759 : CollatzResearch.WordTrace tailWord_7819759 prefixEnd_7819759 4015294969321775890650089 := by
  unfold tailWord_7819759
  simp only [CollatzResearch.WordTrace]
  refine ⟨285210041677356126357046331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190140027784904084238030887 285210041677356126357046331)
  ·
    refine ⟨427815062516034189535569497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285210041677356126357046331 427815062516034189535569497)
    ·
      refine ⟨320861296887025642151677123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427815062516034189535569497 320861296887025642151677123)
      ·
        refine ⟨481291945330538463227515685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320861296887025642151677123 481291945330538463227515685)
        ·
          refine ⟨90242239749475961855159191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481291945330538463227515685 90242239749475961855159191)
          ·
            refine ⟨135363359624213942782738787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90242239749475961855159191 135363359624213942782738787)
            ·
              refine ⟨203045039436320914174108181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135363359624213942782738787 203045039436320914174108181)
              ·
                refine ⟨9517736223577542851911321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203045039436320914174108181 9517736223577542851911321)
                ·
                  refine ⟨7138302167683157138933491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517736223577542851911321 7138302167683157138933491)
                  ·
                    refine ⟨10707453251524735708400237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7138302167683157138933491 10707453251524735708400237)
                    ·
                      refine ⟨4015294969321775890650089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10707453251524735708400237 4015294969321775890650089)
                      ·
                        rfl

theorem cell23_7819759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_7819759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819759 prefixEnd_7819759 := by exact prefixLift 7819759
  have htrace : WordTrace (prefixWord ++ tailWord_7819759) baseStart_7819759 baseEnd_7819759 := by
    simpa [prefixWord, tailWord_7819759, baseEnd_7819759] using wordTrace_append hprefix tailTrace_7819759
  have hstable : (prefixWord ++ tailWord_7819759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819759).length < 2 ^ (prefixWord ++ tailWord_7819759).sum := by decide
  have hdescent : baseEnd_7819759 < baseStart_7819759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819775 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 8]
def baseStart_7819775 : Nat := 118140960795 + 7819775 * 2 ^ 59
def prefixEnd_7819775 : Nat := 4983230072969 + 3 ^ 40 * 7819775 * 2
def baseEnd_7819775 : Nat := 1338434395004082609350005

theorem tailTrace_7819775 : CollatzResearch.WordTrace tailWord_7819775 prefixEnd_7819775 1338434395004082609350005 := by
  unfold tailWord_7819775
  simp only [CollatzResearch.WordTrace]
  refine ⟨285210625245298161089628779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190140416830198774059752519 285210625245298161089628779)
  ·
    refine ⟨427815937867947241634443169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285210625245298161089628779 427815937867947241634443169)
    ·
      refine ⟨320861953400960431225832377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427815937867947241634443169 320861953400960431225832377)
      ·
        refine ⟨240646465050720323419374283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320861953400960431225832377 240646465050720323419374283)
        ·
          refine ⟨360969697576080485129061425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240646465050720323419374283 360969697576080485129061425)
          ·
            refine ⟨270727273182060363846796069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360969697576080485129061425 270727273182060363846796069)
            ·
              refine ⟨50761363721636318221274263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270727273182060363846796069 50761363721636318221274263)
              ·
                refine ⟨76142045582454477331911395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50761363721636318221274263 76142045582454477331911395)
                ·
                  refine ⟨114213068373681715997867093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76142045582454477331911395 114213068373681715997867093)
                  ·
                    refine ⟨1338434395004082609350005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114213068373681715997867093 1338434395004082609350005)
                    ·
                      rfl

theorem cell23_7819775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_7819775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819775 prefixEnd_7819775 := by exact prefixLift 7819775
  have htrace : WordTrace (prefixWord ++ tailWord_7819775) baseStart_7819775 baseEnd_7819775 := by
    simpa [prefixWord, tailWord_7819775, baseEnd_7819775] using wordTrace_append hprefix tailTrace_7819775
  have hstable : (prefixWord ++ tailWord_7819775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819775).length < 2 ^ (prefixWord ++ tailWord_7819775).sum := by decide
  have hdescent : baseEnd_7819775 < baseStart_7819775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819802 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7819802 : Nat := 118140960795 + 7819802 * 2 ^ 59
def prefixEnd_7819802 : Nat := 4983230072969 + 3 ^ 40 * 7819802 * 2
def baseEnd_7819802 : Nat := 4015317048989919222412391

theorem tailTrace_7819802 : CollatzResearch.WordTrace tailWord_7819802 prefixEnd_7819802 4015317048989919222412391 := by
  unfold tailWord_7819802
  simp only [CollatzResearch.WordTrace]
  refine ⟨71302902504050086175215415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190141073344133563133907773 71302902504050086175215415)
  ·
    refine ⟨106954353756075129262823123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71302902504050086175215415 106954353756075129262823123)
    ·
      refine ⟨160431530634112693894234685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106954353756075129262823123 160431530634112693894234685)
      ·
        refine ⟨60161823987792260210338007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160431530634112693894234685 60161823987792260210338007)
        ·
          refine ⟨90242735981688390315507011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60161823987792260210338007 90242735981688390315507011)
          ·
            refine ⟨135364103972532585473260517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90242735981688390315507011 135364103972532585473260517)
            ·
              refine ⟨25380769494849859776236347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135364103972532585473260517 25380769494849859776236347)
              ·
                refine ⟨38071154242274789664354521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25380769494849859776236347 38071154242274789664354521)
                ·
                  refine ⟨28553365681706092248265891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38071154242274789664354521 28553365681706092248265891)
                  ·
                    refine ⟨42830048522559138372398837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28553365681706092248265891 42830048522559138372398837)
                    ·
                      refine ⟨4015317048989919222412391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42830048522559138372398837 4015317048989919222412391)
                      ·
                        rfl

theorem cell23_7819802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7819802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819802 prefixEnd_7819802 := by exact prefixLift 7819802
  have htrace : WordTrace (prefixWord ++ tailWord_7819802) baseStart_7819802 baseEnd_7819802 := by
    simpa [prefixWord, tailWord_7819802, baseEnd_7819802] using wordTrace_append hprefix tailTrace_7819802
  have hstable : (prefixWord ++ tailWord_7819802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819802).length < 2 ^ (prefixWord ++ tailWord_7819802).sum := by decide
  have hdescent : baseEnd_7819802 < baseStart_7819802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819835 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 11]
def baseStart_7819835 : Nat := 118140960795 + 7819835 * 2 ^ 59
def prefixEnd_7819835 : Nat := 4983230072969 + 3 ^ 40 * 7819835 * 2
def baseEnd_7819835 : Nat := 1338444664617172531099913

theorem tailTrace_7819835 : CollatzResearch.WordTrace tailWord_7819835 prefixEnd_7819835 1338444664617172531099913 := by
  unfold tailWord_7819835
  simp only [CollatzResearch.WordTrace]
  refine ⟨285212813625080791336812959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190141875750053860891208639 285212813625080791336812959)
  ·
    refine ⟨427819220437621187005219439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285212813625080791336812959 427819220437621187005219439)
    ·
      refine ⟨641728830656431780507829159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427819220437621187005219439 641728830656431780507829159)
      ·
        refine ⟨962593245984647670761743739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641728830656431780507829159 962593245984647670761743739)
        ·
          refine ⟨1443889868976971506142615609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962593245984647670761743739 1443889868976971506142615609)
          ·
            refine ⟨1082917401732728629606961707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443889868976971506142615609 1082917401732728629606961707)
            ·
              refine ⟨1624376102599092944410442561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082917401732728629606961707 1624376102599092944410442561)
              ·
                refine ⟨1218282076949319708307831921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624376102599092944410442561 1218282076949319708307831921)
                ·
                  refine ⟨913711557711989781230873941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218282076949319708307831921 913711557711989781230873941)
                  ·
                    refine ⟨1338444664617172531099913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 913711557711989781230873941 1338444664617172531099913)
                    ·
                      rfl

theorem cell23_7819835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_7819835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819835 prefixEnd_7819835 := by exact prefixLift 7819835
  have htrace : WordTrace (prefixWord ++ tailWord_7819835) baseStart_7819835 baseEnd_7819835 := by
    simpa [prefixWord, tailWord_7819835, baseEnd_7819835] using wordTrace_append hprefix tailTrace_7819835
  have hstable : (prefixWord ++ tailWord_7819835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819835).length < 2 ^ (prefixWord ++ tailWord_7819835).sum := by decide
  have hdescent : baseEnd_7819835 < baseStart_7819835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819852 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_7819852 : Nat := 118140960795 + 7819852 * 2 ^ 59
def prefixEnd_7819852 : Nat := 4983230072969 + 3 ^ 40 * 7819852 * 2
def baseEnd_7819852 : Nat := 1338447574340881342262387

theorem tailTrace_7819852 : CollatzResearch.WordTrace tailWord_7819852 prefixEnd_7819852 1338447574340881342262387 := by
  unfold tailWord_7819852
  simp only [CollatzResearch.WordTrace]
  refine ⟨142606716833009601620090905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190142289110679468826787873 142606716833009601620090905)
  ·
    refine ⟨106955037624757201215068179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142606716833009601620090905 106955037624757201215068179)
    ·
      refine ⟨160432556437135801822602269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106955037624757201215068179 160432556437135801822602269)
      ·
        refine ⟨60162208663925925683475851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160432556437135801822602269 60162208663925925683475851)
        ·
          refine ⟨90243312995888888525213777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60162208663925925683475851 90243312995888888525213777)
          ·
            refine ⟨67682484746916666393910333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90243312995888888525213777 67682484746916666393910333)
            ·
              refine ⟨25380931780093749897716375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67682484746916666393910333 25380931780093749897716375)
              ·
                refine ⟨38071397670140624846574563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25380931780093749897716375 38071397670140624846574563)
                ·
                  refine ⟨57107096505210937269861845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38071397670140624846574563 57107096505210937269861845)
                  ·
                    refine ⟨1338447574340881342262387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57107096505210937269861845 1338447574340881342262387)
                    ·
                      rfl

theorem cell23_7819852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_7819852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819852 prefixEnd_7819852 := by exact prefixLift 7819852
  have htrace : WordTrace (prefixWord ++ tailWord_7819852) baseStart_7819852 baseEnd_7819852 := by
    simpa [prefixWord, tailWord_7819852, baseEnd_7819852] using wordTrace_append hprefix tailTrace_7819852
  have hstable : (prefixWord ++ tailWord_7819852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819852).length < 2 ^ (prefixWord ++ tailWord_7819852).sum := by decide
  have hdescent : baseEnd_7819852 < baseStart_7819852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819909 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_7819909 : Nat := 118140960795 + 7819909 * 2 ^ 59
def prefixEnd_7819909 : Nat := 4983230072969 + 3 ^ 40 * 7819909 * 2
def baseEnd_7819909 : Nat := 4015371991419950303774399

theorem tailTrace_7819909 : CollatzResearch.WordTrace tailWord_7819909 prefixEnd_7819909 4015371991419950303774399 := by
  unfold tailWord_7819909
  simp only [CollatzResearch.WordTrace]
  refine ⟨285215512626812701975006781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190143675084541801316671187 285215512626812701975006781)
  ·
    refine ⟨106955817235054763240627543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285215512626812701975006781 106955817235054763240627543)
    ·
      refine ⟨160433725852582144860941315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106955817235054763240627543 160433725852582144860941315)
      ·
        refine ⟨240650588778873217291411973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160433725852582144860941315 240650588778873217291411973)
        ·
          refine ⟨45121985396038728242139745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240650588778873217291411973 45121985396038728242139745)
          ·
            refine ⟨33841489047029046181604809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45121985396038728242139745 33841489047029046181604809)
            ·
              refine ⟨25381116785271784636203607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33841489047029046181604809 25381116785271784636203607)
              ·
                refine ⟨38071675177907676954305411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25381116785271784636203607 38071675177907676954305411)
                ·
                  refine ⟨57107512766861515431458117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38071675177907676954305411 57107512766861515431458117)
                  ·
                    refine ⟨10707658643786534143398397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57107512766861515431458117 10707658643786534143398397)
                    ·
                      refine ⟨4015371991419950303774399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10707658643786534143398397 4015371991419950303774399)
                      ·
                        rfl

theorem cell23_7819909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_7819909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819909 prefixEnd_7819909 := by exact prefixLift 7819909
  have htrace : WordTrace (prefixWord ++ tailWord_7819909) baseStart_7819909 baseEnd_7819909 := by
    simpa [prefixWord, tailWord_7819909, baseEnd_7819909] using wordTrace_append hprefix tailTrace_7819909
  have hstable : (prefixWord ++ tailWord_7819909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819909).length < 2 ^ (prefixWord ++ tailWord_7819909).sum := by decide
  have hdescent : baseEnd_7819909 < baseStart_7819909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819916 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_7819916 : Nat := 118140960795 + 7819916 * 2 ^ 59
def prefixEnd_7819916 : Nat := 4983230072969 + 3 ^ 40 * 7819916 * 2
def baseEnd_7819916 : Nat := 1338458528594843925462289

theorem tailTrace_7819916 : CollatzResearch.WordTrace tailWord_7819916 prefixEnd_7819916 1338458528594843925462289 := by
  unfold tailWord_7819916
  simp only [CollatzResearch.WordTrace]
  refine ⟨142607883968893671085255801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190143845291858228113674401 142607883968893671085255801)
  ·
    refine ⟨106955912976670253313941851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142607883968893671085255801 106955912976670253313941851)
    ·
      refine ⟨160433869465005379970912777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106955912976670253313941851 160433869465005379970912777)
      ·
        refine ⟨120325402098754034978184583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160433869465005379970912777 120325402098754034978184583)
        ·
          refine ⟨180488103148131052467276875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120325402098754034978184583 180488103148131052467276875)
          ·
            refine ⟨270732154722196578700915313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180488103148131052467276875 270732154722196578700915313)
            ·
              refine ⟨203049116041647434025686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270732154722196578700915313 203049116041647434025686485)
              ·
                refine ⟨4758963657226111734977027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203049116041647434025686485 4758963657226111734977027)
                ·
                  refine ⟨7138445485839167602465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758963657226111734977027 7138445485839167602465541)
                  ·
                    refine ⟨1338458528594843925462289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138445485839167602465541 1338458528594843925462289)
                    ·
                      rfl

theorem cell23_7819916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_7819916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7819916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7819916 prefixEnd_7819916 := by exact prefixLift 7819916
  have htrace : WordTrace (prefixWord ++ tailWord_7819916) baseStart_7819916 baseEnd_7819916 := by
    simpa [prefixWord, tailWord_7819916, baseEnd_7819916] using wordTrace_append hprefix tailTrace_7819916
  have hstable : (prefixWord ++ tailWord_7819916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819916).length < 2 ^ (prefixWord ++ tailWord_7819916).sum := by decide
  have hdescent : baseEnd_7819916 < baseStart_7819916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820009 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_7820009 : Nat := 118140960795 + 7820009 * 2 ^ 59
def prefixEnd_7820009 : Nat := 4983230072969 + 3 ^ 40 * 7820009 * 2
def baseEnd_7820009 : Nat := 4015423339485399912523939

theorem tailTrace_7820009 : CollatzResearch.WordTrace tailWord_7820009 prefixEnd_7820009 4015423339485399912523939 := by
  unfold tailWord_7820009
  simp only [CollatzResearch.WordTrace]
  refine ⟨285219159926450419053647081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190146106617633612702431387 285219159926450419053647081)
  ·
    refine ⟨213914369944837814290235311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285219159926450419053647081 213914369944837814290235311)
    ·
      refine ⟨320871554917256721435352967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213914369944837814290235311 320871554917256721435352967)
      ·
        refine ⟨481307332375885082153029451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320871554917256721435352967 481307332375885082153029451)
        ·
          refine ⟨721960998563827623229544177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481307332375885082153029451 721960998563827623229544177)
          ·
            refine ⟨541470748922870717422158133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721960998563827623229544177 541470748922870717422158133)
            ·
              refine ⟨50762882711519129758327325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541470748922870717422158133 50762882711519129758327325)
              ·
                refine ⟨19036081016819673659372747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50762882711519129758327325 19036081016819673659372747)
                ·
                  refine ⟨28554121525229510489059121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19036081016819673659372747 28554121525229510489059121)
                  ·
                    refine ⟨21415591143922132866794341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28554121525229510489059121 21415591143922132866794341)
                    ·
                      refine ⟨4015423339485399912523939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21415591143922132866794341 4015423339485399912523939)
                      ·
                        rfl

theorem cell23_7820009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_7820009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820009 prefixEnd_7820009 := by exact prefixLift 7820009
  have htrace : WordTrace (prefixWord ++ tailWord_7820009) baseStart_7820009 baseEnd_7820009 := by
    simpa [prefixWord, tailWord_7820009, baseEnd_7820009] using wordTrace_append hprefix tailTrace_7820009
  have hstable : (prefixWord ++ tailWord_7820009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820009).length < 2 ^ (prefixWord ++ tailWord_7820009).sum := by decide
  have hdescent : baseEnd_7820009 < baseStart_7820009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820016 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_7820016 : Nat := 118140960795 + 7820016 * 2 ^ 59
def prefixEnd_7820016 : Nat := 4983230072969 + 3 ^ 40 * 7820016 * 2
def baseEnd_7820016 : Nat := 4015426933849981385136407

theorem tailTrace_7820016 : CollatzResearch.WordTrace tailWord_7820016 prefixEnd_7820016 4015426933849981385136407 := by
  unfold tailWord_7820016
  simp only [CollatzResearch.WordTrace]
  refine ⟨142609707618712529624575951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190146276824950039499434601 142609707618712529624575951)
  ·
    refine ⟨213914561428068794436863927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142609707618712529624575951 213914561428068794436863927)
    ·
      refine ⟨320871842142103191655295891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213914561428068794436863927 320871842142103191655295891)
      ·
        refine ⟨481307763213154787482943837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320871842142103191655295891 481307763213154787482943837)
        ·
          refine ⟨180490411204933045306103939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481307763213154787482943837 180490411204933045306103939)
          ·
            refine ⟨270735616807399567959155909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180490411204933045306103939 270735616807399567959155909)
            ·
              refine ⟨50762928151387418992341733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270735616807399567959155909 50762928151387418992341733)
              ·
                refine ⟨9518049028385141061064075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50762928151387418992341733 9518049028385141061064075)
                ·
                  refine ⟨14277073542577711591596113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9518049028385141061064075 14277073542577711591596113)
                  ·
                    refine ⟨10707805156933283693697085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14277073542577711591596113 10707805156933283693697085)
                    ·
                      refine ⟨4015426933849981385136407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10707805156933283693697085 4015426933849981385136407)
                      ·
                        rfl

theorem cell23_7820016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_7820016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820016 prefixEnd_7820016 := by exact prefixLift 7820016
  have htrace : WordTrace (prefixWord ++ tailWord_7820016) baseStart_7820016 baseEnd_7820016 := by
    simpa [prefixWord, tailWord_7820016, baseEnd_7820016] using wordTrace_append hprefix tailTrace_7820016
  have hstable : (prefixWord ++ tailWord_7820016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820016).length < 2 ^ (prefixWord ++ tailWord_7820016).sum := by decide
  have hdescent : baseEnd_7820016 < baseStart_7820016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820030 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7820030 : Nat := 118140960795 + 7820030 * 2 ^ 59
def prefixEnd_7820030 : Nat := 4983230072969 + 3 ^ 40 * 7820030 * 2
def baseEnd_7820030 : Nat := 4015434122579144330361343

theorem tailTrace_7820030 : CollatzResearch.WordTrace tailWord_7820030 prefixEnd_7820030 4015434122579144330361343 := by
  unfold tailWord_7820030
  simp only [CollatzResearch.WordTrace]
  refine ⟨35652490732421792455020193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190146617239582893093441029 35652490732421792455020193)
  ·
    refine ⟨26739368049316344341265145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35652490732421792455020193 26739368049316344341265145)
    ·
      refine ⟨20054526036987258255948859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26739368049316344341265145 20054526036987258255948859)
      ·
        refine ⟨30081789055480887383923289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20054526036987258255948859 30081789055480887383923289)
        ·
          refine ⟨22561341791610665537942467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30081789055480887383923289 22561341791610665537942467)
          ·
            refine ⟨33842012687415998306913701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22561341791610665537942467 33842012687415998306913701)
            ·
              refine ⟨6345377378890499682546319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33842012687415998306913701 6345377378890499682546319)
              ·
                refine ⟨9518066068335749523819479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345377378890499682546319 9518066068335749523819479)
                ·
                  refine ⟨14277099102503624285729219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9518066068335749523819479 14277099102503624285729219)
                  ·
                    refine ⟨21415648653755436428593829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14277099102503624285729219 21415648653755436428593829)
                    ·
                      refine ⟨4015434122579144330361343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21415648653755436428593829 4015434122579144330361343)
                      ·
                        rfl

theorem cell23_7820030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7820030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820030 prefixEnd_7820030 := by exact prefixLift 7820030
  have htrace : WordTrace (prefixWord ++ tailWord_7820030) baseStart_7820030 baseEnd_7820030 := by
    simpa [prefixWord, tailWord_7820030, baseEnd_7820030] using wordTrace_append hprefix tailTrace_7820030
  have hstable : (prefixWord ++ tailWord_7820030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820030).length < 2 ^ (prefixWord ++ tailWord_7820030).sum := by decide
  have hdescent : baseEnd_7820030 < baseStart_7820030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820063 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_7820063 : Nat := 118140960795 + 7820063 * 2 ^ 59
def prefixEnd_7820063 : Nat := 4983230072969 + 3 ^ 40 * 7820063 * 2
def baseEnd_7820063 : Nat := 4015451067440742701248691

theorem tailTrace_7820063 : CollatzResearch.WordTrace tailWord_7820063 prefixEnd_7820063 4015451067440742701248691 := by
  unfold tailWord_7820063
  simp only [CollatzResearch.WordTrace]
  refine ⟨285221129468254786276112843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190147419645503190850741895 285221129468254786276112843)
  ·
    refine ⟨427831694202382179414169265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285221129468254786276112843 427831694202382179414169265)
    ·
      refine ⟨320873770651786634560626949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427831694202382179414169265 320873770651786634560626949)
      ·
        refine ⟨60163831997209993980117553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320873770651786634560626949 60163831997209993980117553)
        ·
          refine ⟨45122873997907495485088165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60163831997209993980117553 45122873997907495485088165)
          ·
            refine ⟨8460538874607655403454031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45122873997907495485088165 8460538874607655403454031)
            ·
              refine ⟨12690808311911483105181047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460538874607655403454031 12690808311911483105181047)
              ·
                refine ⟨19036212467867224657771571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12690808311911483105181047 19036212467867224657771571)
                ·
                  refine ⟨28554318701800836986657357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19036212467867224657771571 28554318701800836986657357)
                  ·
                    refine ⟨10707869513175313869996509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28554318701800836986657357 10707869513175313869996509)
                    ·
                      refine ⟨4015451067440742701248691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10707869513175313869996509 4015451067440742701248691)
                      ·
                        rfl

theorem cell23_7820063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_7820063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820063 prefixEnd_7820063 := by exact prefixLift 7820063
  have htrace : WordTrace (prefixWord ++ tailWord_7820063) baseStart_7820063 baseEnd_7820063 := by
    simpa [prefixWord, tailWord_7820063, baseEnd_7820063] using wordTrace_append hprefix tailTrace_7820063
  have hstable : (prefixWord ++ tailWord_7820063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820063).length < 2 ^ (prefixWord ++ tailWord_7820063).sum := by decide
  have hdescent : baseEnd_7820063 < baseStart_7820063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820139 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 7]
def baseStart_7820139 : Nat := 118140960795 + 7820139 * 2 ^ 59
def prefixEnd_7820139 : Nat := 4983230072969 + 3 ^ 40 * 7820139 * 2
def baseEnd_7820139 : Nat := 1338496697323494801299447

theorem tailTrace_7820139 : CollatzResearch.WordTrace tailWord_7820139 prefixEnd_7820139 1338496697323494801299447 := by
  unfold tailWord_7820139
  simp only [CollatzResearch.WordTrace]
  refine ⟨285223901415979451255879471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190149267610652967503919647 285223901415979451255879471)
  ·
    refine ⟨427835852123969176883819207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285223901415979451255879471 427835852123969176883819207)
    ·
      refine ⟨641753778185953765325728811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427835852123969176883819207 641753778185953765325728811)
      ·
        refine ⟨962630667278930647988593217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641753778185953765325728811 962630667278930647988593217)
        ·
          refine ⟨721973000459197985991444913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962630667278930647988593217 721973000459197985991444913)
          ·
            refine ⟨541479750344398489493583685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721973000459197985991444913 541479750344398489493583685)
            ·
              refine ⟨101527453189574716780046941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541479750344398489493583685 101527453189574716780046941)
              ·
                refine ⟨38072794946090518792517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101527453189574716780046941 38072794946090518792517603)
                ·
                  refine ⟨57109192419135778188776405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38072794946090518792517603 57109192419135778188776405)
                  ·
                    refine ⟨1338496697323494801299447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57109192419135778188776405 1338496697323494801299447)
                    ·
                      rfl

theorem cell23_7820139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_7820139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820139 prefixEnd_7820139 := by exact prefixLift 7820139
  have htrace : WordTrace (prefixWord ++ tailWord_7820139) baseStart_7820139 baseEnd_7820139 := by
    simpa [prefixWord, tailWord_7820139, baseEnd_7820139] using wordTrace_append hprefix tailTrace_7820139
  have hstable : (prefixWord ++ tailWord_7820139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820139).length < 2 ^ (prefixWord ++ tailWord_7820139).sum := by decide
  have hdescent : baseEnd_7820139 < baseStart_7820139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820193 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7820193 : Nat := 118140960795 + 7820193 * 2 ^ 59
def prefixEnd_7820193 : Nat := 4983230072969 + 3 ^ 40 * 7820193 * 2
def baseEnd_7820193 : Nat := 4015517819925827192623093

theorem tailTrace_7820193 : CollatzResearch.WordTrace tailWord_7820193 prefixEnd_7820193 4015517819925827192623093 := by
  unfold tailWord_7820193
  simp only [CollatzResearch.WordTrace]
  refine ⟨285225870957783818478345233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190150580638522545652230155 285225870957783818478345233)
  ·
    refine ⟨213919403218337863858758925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285225870957783818478345233 213919403218337863858758925)
    ·
      refine ⟨80219776206876698947034597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213919403218337863858758925 80219776206876698947034597)
      ·
        refine ⟨15041208038789381052568987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80219776206876698947034597 15041208038789381052568987)
        ·
          refine ⟨22561812058184071578853481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041208038789381052568987 22561812058184071578853481)
          ·
            refine ⟨16921359043638053684140111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22561812058184071578853481 16921359043638053684140111)
            ·
              refine ⟨25382038565457080526210167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16921359043638053684140111 25382038565457080526210167)
              ·
                refine ⟨38073057848185620789315251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25382038565457080526210167 38073057848185620789315251)
                ·
                  refine ⟨57109586772278431183972877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38073057848185620789315251 57109586772278431183972877)
                  ·
                    refine ⟨21416095039604411693989829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57109586772278431183972877 21416095039604411693989829)
                    ·
                      refine ⟨4015517819925827192623093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21416095039604411693989829 4015517819925827192623093)
                      ·
                        rfl

theorem cell23_7820193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7820193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820193 prefixEnd_7820193 := by exact prefixLift 7820193
  have htrace : WordTrace (prefixWord ++ tailWord_7820193) baseStart_7820193 baseEnd_7820193 := by
    simpa [prefixWord, tailWord_7820193, baseEnd_7820193] using wordTrace_append hprefix tailTrace_7820193
  have hstable : (prefixWord ++ tailWord_7820193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820193).length < 2 ^ (prefixWord ++ tailWord_7820193).sum := by decide
  have hdescent : baseEnd_7820193 < baseStart_7820193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820213 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_7820213 : Nat := 118140960795 + 7820213 * 2 ^ 59
def prefixEnd_7820213 : Nat := 4983230072969 + 3 ^ 40 * 7820213 * 2
def baseEnd_7820213 : Nat := 4015528089538917114373001

theorem tailTrace_7820213 : CollatzResearch.WordTrace tailWord_7820213 prefixEnd_7820213 4015528089538917114373001 := by
  unfold tailWord_7820213
  simp only [CollatzResearch.WordTrace]
  refine ⟨285226600417711361894073293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190151066945140907929382195 285226600417711361894073293)
  ·
    refine ⟨106959975156641760710277485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285226600417711361894073293 106959975156641760710277485)
    ·
      refine ⟨40109990683740660266354057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106959975156641760710277485 40109990683740660266354057)
      ·
        refine ⟨30082493012805495199765543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40109990683740660266354057 30082493012805495199765543)
        ·
          refine ⟨45123739519208242799648315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30082493012805495199765543 45123739519208242799648315)
          ·
            refine ⟨67685609278812364199472473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45123739519208242799648315 67685609278812364199472473)
            ·
              refine ⟨50764206959109273149604355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67685609278812364199472473 50764206959109273149604355)
              ·
                refine ⟨76146310438663909724406533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50764206959109273149604355 76146310438663909724406533)
                ·
                  refine ⟨14277433207249483073326225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76146310438663909724406533 14277433207249483073326225)
                  ·
                    refine ⟨10708074905437112304994669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14277433207249483073326225 10708074905437112304994669)
                    ·
                      refine ⟨4015528089538917114373001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10708074905437112304994669 4015528089538917114373001)
                      ·
                        rfl

theorem cell23_7820213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_7820213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820213 prefixEnd_7820213 := by exact prefixLift 7820213
  have htrace : WordTrace (prefixWord ++ tailWord_7820213) baseStart_7820213 baseEnd_7820213 := by
    simpa [prefixWord, tailWord_7820213, baseEnd_7820213] using wordTrace_append hprefix tailTrace_7820213
  have hstable : (prefixWord ++ tailWord_7820213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820213).length < 2 ^ (prefixWord ++ tailWord_7820213).sum := by decide
  have hdescent : baseEnd_7820213 < baseStart_7820213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820216 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 8]
def baseStart_7820216 : Nat := 118140960795 + 7820216 * 2 ^ 59
def prefixEnd_7820216 : Nat := 4983230072969 + 3 ^ 40 * 7820216 * 2
def baseEnd_7820216 : Nat := 446169958886764511403943

theorem tailTrace_7820216 : CollatzResearch.WordTrace tailWord_7820216 prefixEnd_7820216 446169958886764511403943 := by
  unfold tailWord_7820216
  simp only [CollatzResearch.WordTrace]
  refine ⟨142613354918350246703216251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190151139891133662270955001 142613354918350246703216251)
  ·
    refine ⟨213920032377525370054824377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142613354918350246703216251 213920032377525370054824377)
    ·
      refine ⟨160440024283144027541118283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213920032377525370054824377 160440024283144027541118283)
      ·
        refine ⟨240660036424716041311677425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160440024283144027541118283 240660036424716041311677425)
        ·
          refine ⟨180495027318537030983758069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240660036424716041311677425 180495027318537030983758069)
          ·
            refine ⟨16921408811112846654727319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180495027318537030983758069 16921408811112846654727319)
            ·
              refine ⟨25382113216669269982090979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16921408811112846654727319 25382113216669269982090979)
              ·
                refine ⟨38073169825003904973136469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25382113216669269982090979 38073169825003904973136469)
                ·
                  refine ⟨446169958886764511403943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38073169825003904973136469 446169958886764511403943)
                  ·
                    rfl

theorem cell23_7820216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 8].length) (baseStart_7820216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820216 prefixEnd_7820216 := by exact prefixLift 7820216
  have htrace : WordTrace (prefixWord ++ tailWord_7820216) baseStart_7820216 baseEnd_7820216 := by
    simpa [prefixWord, tailWord_7820216, baseEnd_7820216] using wordTrace_append hprefix tailTrace_7820216
  have hstable : (prefixWord ++ tailWord_7820216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820216).length < 2 ^ (prefixWord ++ tailWord_7820216).sum := by decide
  have hdescent : baseEnd_7820216 < baseStart_7820216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820236 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7820236 : Nat := 118140960795 + 7820236 * 2 ^ 59
def prefixEnd_7820236 : Nat := 4983230072969 + 3 ^ 40 * 7820236 * 2
def baseEnd_7820236 : Nat := 4015539899593970524385395

theorem tailTrace_7820236 : CollatzResearch.WordTrace tailWord_7820236 prefixEnd_7820236 4015539899593970524385395 := by
  unfold tailWord_7820236
  simp only [CollatzResearch.WordTrace]
  refine ⟨142613719648314018411080281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190151626197752024548107041 142613719648314018411080281)
  ·
    refine ⟨106960289736235513808310211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142613719648314018411080281 106960289736235513808310211)
    ·
      refine ⟨160440434604353270712465317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106960289736235513808310211 160440434604353270712465317)
      ·
        refine ⟨30082581488316238258587247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160440434604353270712465317 30082581488316238258587247)
        ·
          refine ⟨45123872232474357387880871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30082581488316238258587247 45123872232474357387880871)
          ·
            refine ⟨67685808348711536081821307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45123872232474357387880871 67685808348711536081821307)
            ·
              refine ⟨101528712523067304122731961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67685808348711536081821307 101528712523067304122731961)
              ·
                refine ⟨76146534392300478092048971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101528712523067304122731961 76146534392300478092048971)
                ·
                  refine ⟨114219801588450717138073457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76146534392300478092048971 114219801588450717138073457)
                  ·
                    refine ⟨85664851191338037853555093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114219801588450717138073457 85664851191338037853555093)
                    ·
                      refine ⟨4015539899593970524385395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85664851191338037853555093 4015539899593970524385395)
                      ·
                        rfl

theorem cell23_7820236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7820236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820236 prefixEnd_7820236 := by exact prefixLift 7820236
  have htrace : WordTrace (prefixWord ++ tailWord_7820236) baseStart_7820236 baseEnd_7820236 := by
    simpa [prefixWord, tailWord_7820236, baseEnd_7820236] using wordTrace_append hprefix tailTrace_7820236
  have hstable : (prefixWord ++ tailWord_7820236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820236).length < 2 ^ (prefixWord ++ tailWord_7820236).sum := by decide
  have hdescent : baseEnd_7820236 < baseStart_7820236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820300 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_7820300 : Nat := 118140960795 + 7820300 * 2 ^ 59
def prefixEnd_7820300 : Nat := 4983230072969 + 3 ^ 40 * 7820300 * 2
def baseEnd_7820300 : Nat := 4015572762355858273985101

theorem tailTrace_7820300 : CollatzResearch.WordTrace tailWord_7820300 prefixEnd_7820300 4015572762355858273985101 := by
  unfold tailWord_7820300
  simp only [CollatzResearch.WordTrace]
  refine ⟨142614886784198087876245177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190153182378930783834993569 142614886784198087876245177)
  ·
    refine ⟨106961165088148565907183883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142614886784198087876245177 106961165088148565907183883)
    ·
      refine ⟨160441747632222848860775825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106961165088148565907183883 160441747632222848860775825)
      ·
        refine ⟨120331310724167136645581869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160441747632222848860775825 120331310724167136645581869)
        ·
          refine ⟨45124241521562676242093201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120331310724167136645581869 45124241521562676242093201)
          ·
            refine ⟨33843181141172007181569901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45124241521562676242093201 33843181141172007181569901)
            ·
              refine ⟨12691192927939502693088713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33843181141172007181569901 12691192927939502693088713)
              ·
                refine ⟨9518394695954627019816535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12691192927939502693088713 9518394695954627019816535)
                ·
                  refine ⟨14277592043931940529724803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9518394695954627019816535 14277592043931940529724803)
                  ·
                    refine ⟨21416388065897910794587205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14277592043931940529724803 21416388065897910794587205)
                    ·
                      refine ⟨4015572762355858273985101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21416388065897910794587205 4015572762355858273985101)
                      ·
                        rfl

theorem cell23_7820300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_7820300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820300 prefixEnd_7820300 := by exact prefixLift 7820300
  have htrace : WordTrace (prefixWord ++ tailWord_7820300) baseStart_7820300 baseEnd_7820300 := by
    simpa [prefixWord, tailWord_7820300, baseEnd_7820300] using wordTrace_append hprefix tailTrace_7820300
  have hstable : (prefixWord ++ tailWord_7820300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820300).length < 2 ^ (prefixWord ++ tailWord_7820300).sum := by decide
  have hdescent : baseEnd_7820300 < baseStart_7820300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820327 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7820327 : Nat := 118140960795 + 7820327 * 2 ^ 59
def prefixEnd_7820327 : Nat := 4983230072969 + 3 ^ 40 * 7820327 * 2
def baseEnd_7820327 : Nat := 1338528875444509889449159

theorem tailTrace_7820327 : CollatzResearch.WordTrace tailWord_7820327 prefixEnd_7820327 1338528875444509889449159 := by
  unfold tailWord_7820327
  simp only [CollatzResearch.WordTrace]
  refine ⟨285230758339298359363723235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190153838892865572909148823 285230758339298359363723235)
  ·
    refine ⟨427846137508947539045584853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285230758339298359363723235 427846137508947539045584853)
    ·
      refine ⟨10027643847865957946380895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 427846137508947539045584853 10027643847865957946380895)
      ·
        refine ⟨15041465771798936919571343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027643847865957946380895 15041465771798936919571343)
        ·
          refine ⟨22562198657698405379357015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041465771798936919571343 22562198657698405379357015)
          ·
            refine ⟨33843297986547608069035523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562198657698405379357015 33843297986547608069035523)
            ·
              refine ⟨50764946979821412103553285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33843297986547608069035523 50764946979821412103553285)
              ·
                refine ⟨9518427558716514769416241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50764946979821412103553285 9518427558716514769416241)
                ·
                  refine ⟨7138820669037386077062181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518427558716514769416241 7138820669037386077062181)
                  ·
                    refine ⟨1338528875444509889449159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138820669037386077062181 1338528875444509889449159)
                    ·
                      rfl

theorem cell23_7820327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7820327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820327 prefixEnd_7820327 := by exact prefixLift 7820327
  have htrace : WordTrace (prefixWord ++ tailWord_7820327) baseStart_7820327 baseEnd_7820327 := by
    simpa [prefixWord, tailWord_7820327, baseEnd_7820327] using wordTrace_append hprefix tailTrace_7820327
  have hstable : (prefixWord ++ tailWord_7820327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820327).length < 2 ^ (prefixWord ++ tailWord_7820327).sum := by decide
  have hdescent : baseEnd_7820327 < baseStart_7820327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820336 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 9]
def baseStart_7820336 : Nat := 118140960795 + 7820336 * 2 ^ 59
def prefixEnd_7820336 : Nat := 4983230072969 + 3 ^ 40 * 7820336 * 2
def baseEnd_7820336 : Nat := 1338530415886473377711645

theorem tailTrace_7820336 : CollatzResearch.WordTrace tailWord_7820336 prefixEnd_7820336 1338530415886473377711645 := by
  unfold tailWord_7820336
  simp only [CollatzResearch.WordTrace]
  refine ⟨142615543298132876950400431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190154057730843835933867241 142615543298132876950400431)
  ·
    refine ⟨213923314947199315425600647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142615543298132876950400431 213923314947199315425600647)
    ·
      refine ⟨320884972420798973138400971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213923314947199315425600647 320884972420798973138400971)
      ·
        refine ⟨481327458631198459707601457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320884972420798973138400971 481327458631198459707601457)
        ·
          refine ⟨360995593973398844780701093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481327458631198459707601457 360995593973398844780701093)
          ·
            refine ⟨67686673870012283396381455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360995593973398844780701093 67686673870012283396381455)
            ·
              refine ⟨101530010805018425094572183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67686673870012283396381455 101530010805018425094572183)
              ·
                refine ⟨152295016207527637641858275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101530010805018425094572183 152295016207527637641858275)
                ·
                  refine ⟨228442524311291456462787413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152295016207527637641858275 228442524311291456462787413)
                  ·
                    refine ⟨1338530415886473377711645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228442524311291456462787413 1338530415886473377711645)
                    ·
                      rfl

theorem cell23_7820336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_7820336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820336 prefixEnd_7820336 := by exact prefixLift 7820336
  have htrace : WordTrace (prefixWord ++ tailWord_7820336) baseStart_7820336 baseEnd_7820336 := by
    simpa [prefixWord, tailWord_7820336, baseEnd_7820336] using wordTrace_append hprefix tailTrace_7820336
  have hstable : (prefixWord ++ tailWord_7820336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820336).length < 2 ^ (prefixWord ++ tailWord_7820336).sum := by decide
  have hdescent : baseEnd_7820336 < baseStart_7820336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820340 : List Nat := [2, 5, 1, 2, 1, 1, 3, 8]
def baseStart_7820340 : Nat := 118140960795 + 7820340 * 2 ^ 59
def prefixEnd_7820340 : Nat := 4983230072969 + 3 ^ 40 * 7820340 * 2
def baseEnd_7820340 : Nat := 148725677836371782129071

theorem tailTrace_7820340 : CollatzResearch.WordTrace tailWord_7820340 prefixEnd_7820340 148725677836371782129071 := by
  unfold tailWord_7820340
  simp only [CollatzResearch.WordTrace]
  refine ⟨142615616244125631291973237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190154154992167508389297649 142615616244125631291973237)
  ·
    refine ⟨13370214022886777933622491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142615616244125631291973237 13370214022886777933622491)
    ·
      refine ⟨20055321034330166900433737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370214022886777933622491 20055321034330166900433737)
      ·
        refine ⟨15041490775747625175325303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20055321034330166900433737 15041490775747625175325303)
        ·
          refine ⟨22562236163621437762987955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041490775747625175325303 22562236163621437762987955)
          ·
            refine ⟨33843354245432156644481933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562236163621437762987955 33843354245432156644481933)
            ·
              refine ⟨12691257842037058741680725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33843354245432156644481933 12691257842037058741680725)
              ·
                refine ⟨148725677836371782129071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12691257842037058741680725 148725677836371782129071)
                ·
                  rfl

theorem cell23_7820340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 8].length) (baseStart_7820340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820340 prefixEnd_7820340 := by exact prefixLift 7820340
  have htrace : WordTrace (prefixWord ++ tailWord_7820340) baseStart_7820340 baseEnd_7820340 := by
    simpa [prefixWord, tailWord_7820340, baseEnd_7820340] using wordTrace_append hprefix tailTrace_7820340
  have hstable : (prefixWord ++ tailWord_7820340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820340).length < 2 ^ (prefixWord ++ tailWord_7820340).sum := by decide
  have hdescent : baseEnd_7820340 < baseStart_7820340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820360 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_7820360 : Nat := 118140960795 + 7820360 * 2 ^ 59
def prefixEnd_7820360 : Nat := 4983230072969 + 3 ^ 40 * 7820360 * 2
def baseEnd_7820360 : Nat := 4015603571195128039234825

theorem tailTrace_7820360 : CollatzResearch.WordTrace tailWord_7820360 prefixEnd_7820360 4015603571195128039234825 := by
  unfold tailWord_7820360
  simp only [CollatzResearch.WordTrace]
  refine ⟨142615980974089402999837267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190154641298785870666449689 142615980974089402999837267)
  ·
    refine ⟨213923971461134104499755901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142615980974089402999837267 213923971461134104499755901)
    ·
      refine ⟨80221489297925289187408463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213923971461134104499755901 80221489297925289187408463)
      ·
        refine ⟨120332233946887933781112695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80221489297925289187408463 120332233946887933781112695)
        ·
          refine ⟨180498350920331900671669043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120332233946887933781112695 180498350920331900671669043)
          ·
            refine ⟨270747526380497851007503565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180498350920331900671669043 270747526380497851007503565)
            ·
              refine ⟨101530322392686694127813837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270747526380497851007503565 101530322392686694127813837)
              ·
                refine ⟨38073870897257510297930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101530322392686694127813837 38073870897257510297930189)
                ·
                  refine ⟨14277701586471566361723821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38073870897257510297930189 14277701586471566361723821)
                  ·
                    refine ⟨5354138094926837385646433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14277701586471566361723821 5354138094926837385646433)
                    ·
                      refine ⟨4015603571195128039234825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354138094926837385646433 4015603571195128039234825)
                      ·
                        rfl

theorem cell23_7820360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_7820360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820360 prefixEnd_7820360 := by exact prefixLift 7820360
  have htrace : WordTrace (prefixWord ++ tailWord_7820360) baseStart_7820360 baseEnd_7820360 := by
    simpa [prefixWord, tailWord_7820360, baseEnd_7820360] using wordTrace_append hprefix tailTrace_7820360
  have hstable : (prefixWord ++ tailWord_7820360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820360).length < 2 ^ (prefixWord ++ tailWord_7820360).sum := by decide
  have hdescent : baseEnd_7820360 < baseStart_7820360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820413 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 7]
def baseStart_7820413 : Nat := 118140960795 + 7820413 * 2 ^ 59
def prefixEnd_7820413 : Nat := 4983230072969 + 3 ^ 40 * 7820413 * 2
def baseEnd_7820413 : Nat := 446181198407757370208009

theorem tailTrace_7820413 : CollatzResearch.WordTrace tailWord_7820413 prefixEnd_7820413 446181198407757370208009 := by
  unfold tailWord_7820413
  simp only [CollatzResearch.WordTrace]
  refine ⟨285233895016986796051353893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190155930011324530700902595 285233895016986796051353893)
  ·
    refine ⟨53481355315685024259628855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285233895016986796051353893 53481355315685024259628855)
    ·
      refine ⟨80222032973527536389443283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53481355315685024259628855 80222032973527536389443283)
      ·
        refine ⟨120333049460291304584164925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80222032973527536389443283 120333049460291304584164925)
        ·
          refine ⟨45124893547609239219061847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120333049460291304584164925 45124893547609239219061847)
          ·
            refine ⟨67687340321413858828592771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45124893547609239219061847 67687340321413858828592771)
            ·
              refine ⟨101531010482120788242889157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67687340321413858828592771 101531010482120788242889157)
              ·
                refine ⟨19037064465397647795541717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101531010482120788242889157 19037064465397647795541717)
                ·
                  refine ⟨446181198407757370208009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19037064465397647795541717 446181198407757370208009)
                  ·
                    rfl

theorem cell23_7820413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_7820413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820413 prefixEnd_7820413 := by exact prefixLift 7820413
  have htrace : WordTrace (prefixWord ++ tailWord_7820413) baseStart_7820413 baseEnd_7820413 := by
    simpa [prefixWord, tailWord_7820413, baseEnd_7820413] using wordTrace_append hprefix tailTrace_7820413
  have hstable : (prefixWord ++ tailWord_7820413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820413).length < 2 ^ (prefixWord ++ tailWord_7820413).sum := by decide
  have hdescent : baseEnd_7820413 < baseStart_7820413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820447 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 7]
def baseStart_7820447 : Nat := 118140960795 + 7820447 * 2 ^ 59
def prefixEnd_7820447 : Nat := 4983230072969 + 3 ^ 40 * 7820447 * 2
def baseEnd_7820447 : Nat := 446183138223563244316325

theorem tailTrace_7820447 : CollatzResearch.WordTrace tailWord_7820447 prefixEnd_7820447 446183138223563244316325 := by
  unfold tailWord_7820447
  simp only [CollatzResearch.WordTrace]
  refine ⟨285235135098863619858091595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190156756732575746572061063 285235135098863619858091595)
  ·
    refine ⟨427852702648295429787137393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285235135098863619858091595 427852702648295429787137393)
    ·
      refine ⟨320889526986221572340353045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427852702648295429787137393 320889526986221572340353045)
      ·
        refine ⟨15041696577479136203454049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320889526986221572340353045 15041696577479136203454049)
        ·
          refine ⟨11281272433109352152590537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15041696577479136203454049 11281272433109352152590537)
          ·
            refine ⟨8460954324832014114442903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11281272433109352152590537 8460954324832014114442903)
            ·
              refine ⟨12691431487248021171664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460954324832014114442903 12691431487248021171664355)
              ·
                refine ⟨19037147230872031757496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691431487248021171664355 19037147230872031757496533)
                ·
                  refine ⟨446183138223563244316325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19037147230872031757496533 446183138223563244316325)
                  ·
                    rfl

theorem cell23_7820447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 7].length) (baseStart_7820447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820447 prefixEnd_7820447 := by exact prefixLift 7820447
  have htrace : WordTrace (prefixWord ++ tailWord_7820447) baseStart_7820447 baseEnd_7820447 := by
    simpa [prefixWord, tailWord_7820447, baseEnd_7820447] using wordTrace_append hprefix tailTrace_7820447
  have hstable : (prefixWord ++ tailWord_7820447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820447).length < 2 ^ (prefixWord ++ tailWord_7820447).sum := by decide
  have hdescent : baseEnd_7820447 < baseStart_7820447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820453 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_7820453 : Nat := 118140960795 + 7820453 * 2 ^ 59
def prefixEnd_7820453 : Nat := 4983230072969 + 3 ^ 40 * 7820453 * 2
def baseEnd_7820453 : Nat := 4015651324895996175371897

theorem tailTrace_7820453 : CollatzResearch.WordTrace tailWord_7820453 prefixEnd_7820453 4015651324895996175371897 := by
  unfold tailWord_7820453
  simp only [CollatzResearch.WordTrace]
  refine ⟨285235353936841882882810013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190156902624561255255206675 285235353936841882882810013)
  ·
    refine ⟨106963257726315706081053755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285235353936841882882810013 106963257726315706081053755)
    ·
      refine ⟨160444886589473559121580633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106963257726315706081053755 160444886589473559121580633)
      ·
        refine ⟨120333664942105169341185475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160444886589473559121580633 120333664942105169341185475)
        ·
          refine ⟨180500497413157754011778213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120333664942105169341185475 180500497413157754011778213)
          ·
            refine ⟨33843843264967078877208415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180500497413157754011778213 33843843264967078877208415)
            ·
              refine ⟨50765764897450618315812623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33843843264967078877208415 50765764897450618315812623)
              ·
                refine ⟨76148647346175927473718935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50765764897450618315812623 76148647346175927473718935)
                ·
                  refine ⟨114222971019263891210578403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76148647346175927473718935 114222971019263891210578403)
                  ·
                    refine ⟨171334456528895836815867605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114222971019263891210578403 171334456528895836815867605)
                    ·
                      refine ⟨4015651324895996175371897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171334456528895836815867605 4015651324895996175371897)
                      ·
                        rfl

theorem cell23_7820453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_7820453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820453 prefixEnd_7820453 := by exact prefixLift 7820453
  have htrace : WordTrace (prefixWord ++ tailWord_7820453) baseStart_7820453 baseEnd_7820453 := by
    simpa [prefixWord, tailWord_7820453, baseEnd_7820453] using wordTrace_append hprefix tailTrace_7820453
  have hstable : (prefixWord ++ tailWord_7820453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820453).length < 2 ^ (prefixWord ++ tailWord_7820453).sum := by decide
  have hdescent : baseEnd_7820453 < baseStart_7820453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820458 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7820458 : Nat := 118140960795 + 7820458 * 2 ^ 59
def prefixEnd_7820458 : Nat := 4983230072969 + 3 ^ 40 * 7820458 * 2
def baseEnd_7820458 : Nat := 4015653892299268655809375

theorem tailTrace_7820458 : CollatzResearch.WordTrace tailWord_7820458 prefixEnd_7820458 4015653892299268655809375 := by
  unfold tailWord_7820458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71308884075455942184185507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190157024201215845824494685 71308884075455942184185507)
  ·
    refine ⟨106963326113183913276278261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71308884075455942184185507 106963326113183913276278261)
    ·
      refine ⟨10027811823110991869651087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106963326113183913276278261 10027811823110991869651087)
      ·
        refine ⟨15041717734666487804476631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027811823110991869651087 15041717734666487804476631)
        ·
          refine ⟨22562576601999731706714947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15041717734666487804476631 22562576601999731706714947)
          ·
            refine ⟨33843864902999597560072421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562576601999731706714947 33843864902999597560072421)
            ·
              refine ⟨6345724669312424542513579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33843864902999597560072421 6345724669312424542513579)
              ·
                refine ⟨9518587003968636813770369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345724669312424542513579 9518587003968636813770369)
                ·
                  refine ⟨7138940252976477610327777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518587003968636813770369 7138940252976477610327777)
                  ·
                    refine ⟨5354205189732358207745833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138940252976477610327777 5354205189732358207745833)
                    ·
                      refine ⟨4015653892299268655809375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354205189732358207745833 4015653892299268655809375)
                      ·
                        rfl

theorem cell23_7820458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7820458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820458 prefixEnd_7820458 := by exact prefixLift 7820458
  have htrace : WordTrace (prefixWord ++ tailWord_7820458) baseStart_7820458 baseEnd_7820458 := by
    simpa [prefixWord, tailWord_7820458, baseEnd_7820458] using wordTrace_append hprefix tailTrace_7820458
  have hstable : (prefixWord ++ tailWord_7820458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820458).length < 2 ^ (prefixWord ++ tailWord_7820458).sum := by decide
  have hdescent : baseEnd_7820458 < baseStart_7820458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820463 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_7820463 : Nat := 118140960795 + 7820463 * 2 ^ 59
def prefixEnd_7820463 : Nat := 4983230072969 + 3 ^ 40 * 7820463 * 2
def baseEnd_7820463 : Nat := 4015656459702541136246851

theorem tailTrace_7820463 : CollatzResearch.WordTrace tailWord_7820463 prefixEnd_7820463 4015656459702541136246851 := by
  unfold tailWord_7820463
  simp only [CollatzResearch.WordTrace]
  refine ⟨285235718666805654590674043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190157145777870436393782695 285235718666805654590674043)
  ·
    refine ⟨427853578000208481886011065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285235718666805654590674043 427853578000208481886011065)
    ·
      refine ⟨320890183500156361414508299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427853578000208481886011065 320890183500156361414508299)
      ·
        refine ⟨481335275250234542121762449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320890183500156361414508299 481335275250234542121762449)
        ·
          refine ⟨361001456437675906591321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481335275250234542121762449 361001456437675906591321837)
          ·
            refine ⟨135375546164128464971745689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361001456437675906591321837 135375546164128464971745689)
            ·
              refine ⟨101531659623096348728809267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135375546164128464971745689 101531659623096348728809267)
              ·
                refine ⟨152297489434644523093213901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101531659623096348728809267 152297489434644523093213901)
                ·
                  refine ⟨57111558537991696159955213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152297489434644523093213901 57111558537991696159955213)
                  ·
                    refine ⟨21416834451746886059983205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57111558537991696159955213 21416834451746886059983205)
                    ·
                      refine ⟨4015656459702541136246851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21416834451746886059983205 4015656459702541136246851)
                      ·
                        rfl

theorem cell23_7820463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_7820463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820463 prefixEnd_7820463 := by exact prefixLift 7820463
  have htrace : WordTrace (prefixWord ++ tailWord_7820463) baseStart_7820463 baseEnd_7820463 := by
    simpa [prefixWord, tailWord_7820463, baseEnd_7820463] using wordTrace_append hprefix tailTrace_7820463
  have hstable : (prefixWord ++ tailWord_7820463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820463).length < 2 ^ (prefixWord ++ tailWord_7820463).sum := by decide
  have hdescent : baseEnd_7820463 < baseStart_7820463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820503 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 8]
def baseStart_7820503 : Nat := 118140960795 + 7820503 * 2 ^ 59
def prefixEnd_7820503 : Nat := 4983230072969 + 3 ^ 40 * 7820503 * 2
def baseEnd_7820503 : Nat := 446186333214302331082963

theorem tailTrace_7820503 : CollatzResearch.WordTrace tailWord_7820503 prefixEnd_7820503 446186333214302331082963 := by
  unfold tailWord_7820503
  simp only [CollatzResearch.WordTrace]
  refine ⟨285237177586660741422130163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190158118391107160948086775 285237177586660741422130163)
  ·
    refine ⟨427855766379991112133195245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285237177586660741422130163 427855766379991112133195245)
    ·
      refine ⟨160445912392496667049948217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427855766379991112133195245 160445912392496667049948217)
      ·
        refine ⟨120334434294372500287461163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160445912392496667049948217 120334434294372500287461163)
        ·
          refine ⟨180501651441558750431191745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120334434294372500287461163 180501651441558750431191745)
          ·
            refine ⟨135376238581169062823393809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180501651441558750431191745 135376238581169062823393809)
            ·
              refine ⟨101532178935876797117545357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135376238581169062823393809 101532178935876797117545357)
              ·
                refine ⟨38074567100953798919079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101532178935876797117545357 38074567100953798919079509)
                ·
                  refine ⟨446186333214302331082963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38074567100953798919079509 446186333214302331082963)
                  ·
                    rfl

theorem cell23_7820503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 8].length) (baseStart_7820503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820503 prefixEnd_7820503 := by exact prefixLift 7820503
  have htrace : WordTrace (prefixWord ++ tailWord_7820503) baseStart_7820503 baseEnd_7820503 := by
    simpa [prefixWord, tailWord_7820503, baseEnd_7820503] using wordTrace_append hprefix tailTrace_7820503
  have hstable : (prefixWord ++ tailWord_7820503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820503).length < 2 ^ (prefixWord ++ tailWord_7820503).sum := by decide
  have hdescent : baseEnd_7820503 < baseStart_7820503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820520 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 6]
def baseStart_7820520 : Nat := 118140960795 + 7820520 * 2 ^ 59
def prefixEnd_7820520 : Nat := 4983230072969 + 3 ^ 40 * 7820520 * 2
def baseEnd_7820520 : Nat := 446187303122205268137121

theorem tailTrace_7820520 : CollatzResearch.WordTrace tailWord_7820520 prefixEnd_7820520 446187303122205268137121 := by
  unfold tailWord_7820520
  simp only [CollatzResearch.WordTrace]
  refine ⟨142618898813799576662749507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190158531751732768883666009 142618898813799576662749507)
  ·
    refine ⟨213928348220699364994124261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142618898813799576662749507 213928348220699364994124261)
    ·
      refine ⟨40111565291381130936398299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213928348220699364994124261 40111565291381130936398299)
      ·
        refine ⟨60167347937071696404597449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40111565291381130936398299 60167347937071696404597449)
        ·
          refine ⟨45125510952803772303448087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60167347937071696404597449 45125510952803772303448087)
          ·
            refine ⟨67688266429205658455172131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45125510952803772303448087 67688266429205658455172131)
            ·
              refine ⟨101532399643808487682758197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67688266429205658455172131 101532399643808487682758197)
              ·
                refine ⟨9518662466607045720258581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101532399643808487682758197 9518662466607045720258581)
                ·
                  refine ⟨446187303122205268137121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9518662466607045720258581 446187303122205268137121)
                  ·
                    rfl

theorem cell23_7820520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 6].length) (baseStart_7820520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820520 prefixEnd_7820520 := by exact prefixLift 7820520
  have htrace : WordTrace (prefixWord ++ tailWord_7820520) baseStart_7820520 baseEnd_7820520 := by
    simpa [prefixWord, tailWord_7820520, baseEnd_7820520] using wordTrace_append hprefix tailTrace_7820520
  have hstable : (prefixWord ++ tailWord_7820520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820520).length < 2 ^ (prefixWord ++ tailWord_7820520).sum := by decide
  have hdescent : baseEnd_7820520 < baseStart_7820520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820563 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 10]
def baseStart_7820563 : Nat := 118140960795 + 7820563 * 2 ^ 59
def prefixEnd_7820563 : Nat := 4983230072969 + 3 ^ 40 * 7820563 * 2
def baseEnd_7820563 : Nat := 1338569269255996914998797

theorem tailTrace_7820563 : CollatzResearch.WordTrace tailWord_7820563 prefixEnd_7820563 1338569269255996914998797 := by
  unfold tailWord_7820563
  simp only [CollatzResearch.WordTrace]
  refine ⟨285239365966443371669314343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190159577310962247779542895 285239365966443371669314343)
  ·
    refine ⟨427859048949665057503971515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285239365966443371669314343 427859048949665057503971515)
    ·
      refine ⟨641788573424497586255957273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427859048949665057503971515 641788573424497586255957273)
      ·
        refine ⟨481341430068373189691967955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641788573424497586255957273 481341430068373189691967955)
        ·
          refine ⟨722012145102559784537951933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481341430068373189691967955 722012145102559784537951933)
          ·
            refine ⟨270754554413459919201731975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722012145102559784537951933 270754554413459919201731975)
            ·
              refine ⟨406131831620189878802597963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270754554413459919201731975 406131831620189878802597963)
              ·
                refine ⟨609197747430284818203896945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406131831620189878802597963 609197747430284818203896945)
                ·
                  refine ⟨456898310572713613652922709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609197747430284818203896945 456898310572713613652922709)
                  ·
                    refine ⟨1338569269255996914998797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 456898310572713613652922709 1338569269255996914998797)
                    ·
                      rfl

theorem cell23_7820563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_7820563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820563 prefixEnd_7820563 := by exact prefixLift 7820563
  have htrace : WordTrace (prefixWord ++ tailWord_7820563) baseStart_7820563 baseEnd_7820563 := by
    simpa [prefixWord, tailWord_7820563, baseEnd_7820563] using wordTrace_append hprefix tailTrace_7820563
  have hstable : (prefixWord ++ tailWord_7820563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820563).length < 2 ^ (prefixWord ++ tailWord_7820563).sum := by decide
  have hdescent : baseEnd_7820563 < baseStart_7820563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820584 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7820584 : Nat := 118140960795 + 7820584 * 2 ^ 59
def prefixEnd_7820584 : Nat := 4983230072969 + 3 ^ 40 * 7820584 * 2
def baseEnd_7820584 : Nat := 1338572863620578387611265

theorem tailTrace_7820584 : CollatzResearch.WordTrace tailWord_7820584 prefixEnd_7820584 1338572863620578387611265 := by
  unfold tailWord_7820584
  simp only [CollatzResearch.WordTrace]
  refine ⟨142620065949683646127914403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190160087932911528170552537 142620065949683646127914403)
  ·
    refine ⟨213930098924525469191871605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142620065949683646127914403 213930098924525469191871605)
    ·
      refine ⟨20055946774174262736737963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213930098924525469191871605 20055946774174262736737963)
      ·
        refine ⟨30083920161261394105106945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20055946774174262736737963 30083920161261394105106945)
        ·
          refine ⟨22562940120946045578830209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30083920161261394105106945 22562940120946045578830209)
          ·
            refine ⟨16922205090709534184122657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22562940120946045578830209 16922205090709534184122657)
            ·
              refine ⟨12691653818032150638091993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16922205090709534184122657 12691653818032150638091993)
              ·
                refine ⟨9518740363524112978568995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12691653818032150638091993 9518740363524112978568995)
                ·
                  refine ⟨14278110545286169467853493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9518740363524112978568995 14278110545286169467853493)
                  ·
                    refine ⟨1338572863620578387611265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14278110545286169467853493 1338572863620578387611265)
                    ·
                      rfl

theorem cell23_7820584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7820584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820584 prefixEnd_7820584 := by exact prefixLift 7820584
  have htrace : WordTrace (prefixWord ++ tailWord_7820584) baseStart_7820584 baseEnd_7820584 := by
    simpa [prefixWord, tailWord_7820584, baseEnd_7820584] using wordTrace_append hprefix tailTrace_7820584
  have hstable : (prefixWord ++ tailWord_7820584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820584).length < 2 ^ (prefixWord ++ tailWord_7820584).sum := by decide
  have hdescent : baseEnd_7820584 < baseStart_7820584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820597 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7820597 : Nat := 118140960795 + 7820597 * 2 ^ 59
def prefixEnd_7820597 : Nat := 4983230072969 + 3 ^ 40 * 7820597 * 2
def baseEnd_7820597 : Nat := 1338575088703414537323745

theorem tailTrace_7820597 : CollatzResearch.WordTrace tailWord_7820597 prefixEnd_7820597 1338575088703414537323745 := by
  unfold tailWord_7820597
  simp only [CollatzResearch.WordTrace]
  refine ⟨285240606048320195476052045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190160404032213463650701363 285240606048320195476052045)
  ·
    refine ⟨106965227268120073303519517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285240606048320195476052045 106965227268120073303519517)
    ·
      refine ⟨40111960225545027488819819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106965227268120073303519517 40111960225545027488819819)
      ·
        refine ⟨60167940338317541233229729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40111960225545027488819819 60167940338317541233229729)
        ·
          refine ⟨45125955253738155924922297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60167940338317541233229729 45125955253738155924922297)
          ·
            refine ⟨33844466440303616943691723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45125955253738155924922297 33844466440303616943691723)
            ·
              refine ⟨50766699660455425415537585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33844466440303616943691723 50766699660455425415537585)
              ·
                refine ⟨38075024745341569061653189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50766699660455425415537585 38075024745341569061653189)
                ·
                  refine ⟨7139067139751544199059973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38075024745341569061653189 7139067139751544199059973)
                  ·
                    refine ⟨1338575088703414537323745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139067139751544199059973 1338575088703414537323745)
                    ·
                      rfl

theorem cell23_7820597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7820597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820597 prefixEnd_7820597 := by exact prefixLift 7820597
  have htrace : WordTrace (prefixWord ++ tailWord_7820597) baseStart_7820597 baseEnd_7820597 := by
    simpa [prefixWord, tailWord_7820597, baseEnd_7820597] using wordTrace_append hprefix tailTrace_7820597
  have hstable : (prefixWord ++ tailWord_7820597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820597).length < 2 ^ (prefixWord ++ tailWord_7820597).sum := by decide
  have hdescent : baseEnd_7820597 < baseStart_7820597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820600 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_7820600 : Nat := 118140960795 + 7820600 * 2 ^ 59
def prefixEnd_7820600 : Nat := 4983230072969 + 3 ^ 40 * 7820600 * 2
def baseEnd_7820600 : Nat := 4015726806552207100233721

theorem tailTrace_7820600 : CollatzResearch.WordTrace tailWord_7820600 prefixEnd_7820600 4015726806552207100233721 := by
  unfold tailWord_7820600
  simp only [CollatzResearch.WordTrace]
  refine ⟨142620357733654663494205627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190160476978206217992274169 142620357733654663494205627)
  ·
    refine ⟨213930536600481995241308441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142620357733654663494205627 213930536600481995241308441)
    ·
      refine ⟨160447902450361496430981331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213930536600481995241308441 160447902450361496430981331)
      ·
        refine ⟨240671853675542244646471997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160447902450361496430981331 240671853675542244646471997)
        ·
          refine ⟨90251945128328341742426999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240671853675542244646471997 90251945128328341742426999)
          ·
            refine ⟨135377917692492512613640499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90251945128328341742426999 135377917692492512613640499)
            ·
              refine ⟨203066876538738768920460749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135377917692492512613640499 203066876538738768920460749)
              ·
                refine ⟨76150078702027038345172781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203066876538738768920460749 76150078702027038345172781)
                ·
                  refine ⟨28556279513260139379439793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76150078702027038345172781 28556279513260139379439793)
                  ·
                    refine ⟨21417209634945104534579845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28556279513260139379439793 21417209634945104534579845)
                    ·
                      refine ⟨4015726806552207100233721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21417209634945104534579845 4015726806552207100233721)
                      ·
                        rfl

theorem cell23_7820600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_7820600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820600 prefixEnd_7820600 := by exact prefixLift 7820600
  have htrace : WordTrace (prefixWord ++ tailWord_7820600) baseStart_7820600 baseEnd_7820600 := by
    simpa [prefixWord, tailWord_7820600, baseEnd_7820600] using wordTrace_append hprefix tailTrace_7820600
  have hstable : (prefixWord ++ tailWord_7820600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820600).length < 2 ^ (prefixWord ++ tailWord_7820600).sum := by decide
  have hdescent : baseEnd_7820600 < baseStart_7820600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820607 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_7820607 : Nat := 118140960795 + 7820607 * 2 ^ 59
def prefixEnd_7820607 : Nat := 4983230072969 + 3 ^ 40 * 7820607 * 2
def baseEnd_7820607 : Nat := 4015730400916788572846189

theorem tailTrace_7820607 : CollatzResearch.WordTrace tailWord_7820607 prefixEnd_7820607 4015730400916788572846189 := by
  unfold tailWord_7820607
  simp only [CollatzResearch.WordTrace]
  refine ⟨285240970778283967183916075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190160647185522644789277383 285240970778283967183916075)
  ·
    refine ⟨427861456167425950775874113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285240970778283967183916075 427861456167425950775874113)
    ·
      refine ⟨320896092125569463081905585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427861456167425950775874113 320896092125569463081905585)
      ·
        refine ⟨240672069094177097311429189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320896092125569463081905585 240672069094177097311429189)
        ·
          refine ⟨45126012955158205745892973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240672069094177097311429189 45126012955158205745892973)
          ·
            refine ⟨16922254858184327154709865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45126012955158205745892973 16922254858184327154709865)
            ·
              refine ⟨12691691143638245366032399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16922254858184327154709865 12691691143638245366032399)
              ·
                refine ⟨19037536715457368049048599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691691143638245366032399 19037536715457368049048599)
                ·
                  refine ⟨28556305073186052073572899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19037536715457368049048599 28556305073186052073572899)
                  ·
                    refine ⟨42834457609779078110359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28556305073186052073572899 42834457609779078110359349)
                    ·
                      refine ⟨4015730400916788572846189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42834457609779078110359349 4015730400916788572846189)
                      ·
                        rfl

theorem cell23_7820607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_7820607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820607 prefixEnd_7820607 := by exact prefixLift 7820607
  have htrace : WordTrace (prefixWord ++ tailWord_7820607) baseStart_7820607 baseEnd_7820607 := by
    simpa [prefixWord, tailWord_7820607, baseEnd_7820607] using wordTrace_append hprefix tailTrace_7820607
  have hstable : (prefixWord ++ tailWord_7820607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820607).length < 2 ^ (prefixWord ++ tailWord_7820607).sum := by decide
  have hdescent : baseEnd_7820607 < baseStart_7820607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820631 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 2, 4]
def baseStart_7820631 : Nat := 118140960795 + 7820631 * 2 ^ 59
def prefixEnd_7820631 : Nat := 4983230072969 + 3 ^ 40 * 7820631 * 2
def baseEnd_7820631 : Nat := 1338580908150832159648693

theorem tailTrace_7820631 : CollatzResearch.WordTrace tailWord_7820631 prefixEnd_7820631 1338580908150832159648693 := by
  unfold tailWord_7820631
  simp only [CollatzResearch.WordTrace]
  refine ⟨285241846130197019282789747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190161230753464679521859831 285241846130197019282789747)
  ·
    refine ⟨427862769195295528924184621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285241846130197019282789747 427862769195295528924184621)
    ·
      refine ⟨160448538448235823346569233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427862769195295528924184621 160448538448235823346569233)
      ·
        refine ⟨120336403836176867509926925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160448538448235823346569233 120336403836176867509926925)
        ·
          refine ⟨45126151438566325316222597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120336403836176867509926925 45126151438566325316222597)
          ·
            refine ⟨8461153394731185996791737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45126151438566325316222597 8461153394731185996791737)
            ·
              refine ⟨6345865046048389497593803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8461153394731185996791737 6345865046048389497593803)
              ·
                refine ⟨9518797569072584246390705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345865046048389497593803 9518797569072584246390705)
                ·
                  refine ⟨7139098176804438184793029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518797569072584246390705 7139098176804438184793029)
                  ·
                    refine ⟨1338580908150832159648693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139098176804438184793029 1338580908150832159648693)
                    ·
                      rfl

theorem cell23_7820631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_7820631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820631 prefixEnd_7820631 := by exact prefixLift 7820631
  have htrace : WordTrace (prefixWord ++ tailWord_7820631) baseStart_7820631 baseEnd_7820631 := by
    simpa [prefixWord, tailWord_7820631, baseEnd_7820631] using wordTrace_append hprefix tailTrace_7820631
  have hstable : (prefixWord ++ tailWord_7820631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820631).length < 2 ^ (prefixWord ++ tailWord_7820631).sum := by decide
  have hdescent : baseEnd_7820631 < baseStart_7820631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820674 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7820674 : Nat := 118140960795 + 7820674 * 2 ^ 59
def prefixEnd_7820674 : Nat := 4983230072969 + 3 ^ 40 * 7820674 * 2
def baseEnd_7820674 : Nat := 1338588268040213270236127

theorem tailTrace_7820674 : CollatzResearch.WordTrace tailWord_7820674 prefixEnd_7820674 1338588268040213270236127 := by
  unfold tailWord_7820674
  simp only [CollatzResearch.WordTrace]
  refine ⟨71310853617260309406651269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190162276312694158417736717 71310853617260309406651269)
  ·
    refine ⟨13370785053236308013747113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71310853617260309406651269 13370785053236308013747113)
    ·
      refine ⟨10028088789927231010310335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13370785053236308013747113 10028088789927231010310335)
      ·
        refine ⟨15042133184890846515465503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10028088789927231010310335 15042133184890846515465503)
        ·
          refine ⟨22563199777336269773198255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15042133184890846515465503 22563199777336269773198255)
          ·
            refine ⟨33844799666004404659797383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22563199777336269773198255 33844799666004404659797383)
            ·
              refine ⟨50767199499006606989696075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33844799666004404659797383 50767199499006606989696075)
              ·
                refine ⟨76150799248509910484544113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50767199499006606989696075 76150799248509910484544113)
                ·
                  refine ⟨57113099436382432863408085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76150799248509910484544113 57113099436382432863408085)
                  ·
                    refine ⟨1338588268040213270236127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57113099436382432863408085 1338588268040213270236127)
                    ·
                      rfl

theorem cell23_7820674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7820674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820674 prefixEnd_7820674 := by exact prefixLift 7820674
  have htrace : WordTrace (prefixWord ++ tailWord_7820674) baseStart_7820674 baseEnd_7820674 := by
    simpa [prefixWord, tailWord_7820674, baseEnd_7820674] using wordTrace_append hprefix tailTrace_7820674
  have hstable : (prefixWord ++ tailWord_7820674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820674).length < 2 ^ (prefixWord ++ tailWord_7820674).sum := by decide
  have hdescent : baseEnd_7820674 < baseStart_7820674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820711 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7820711 : Nat := 118140960795 + 7820711 * 2 ^ 59
def prefixEnd_7820711 : Nat := 4983230072969 + 3 ^ 40 * 7820711 * 2
def baseEnd_7820711 : Nat := 4015783802904856165945711

theorem tailTrace_7820711 : CollatzResearch.WordTrace tailWord_7820711 prefixEnd_7820711 4015783802904856165945711 := by
  unfold tailWord_7820711
  simp only [CollatzResearch.WordTrace]
  refine ⟨285244763969907192945701987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190163175979938128630467991 285244763969907192945701987)
  ·
    refine ⟨427867145954860789418552981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285244763969907192945701987 427867145954860789418552981)
    ·
      refine ⟨20056272466634099503994671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 427867145954860789418552981 20056272466634099503994671)
      ·
        refine ⟨30084408699951149255992007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20056272466634099503994671 30084408699951149255992007)
        ·
          refine ⟨45126613049926723883988011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30084408699951149255992007 45126613049926723883988011)
          ·
            refine ⟨67689919574890085825982017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45126613049926723883988011 67689919574890085825982017)
            ·
              refine ⟨50767439681167564369486513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67689919574890085825982017 50767439681167564369486513)
              ·
                refine ⟨38075579760875673277114885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50767439681167564369486513 38075579760875673277114885)
                ·
                  refine ⟨7139171205164188739459041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38075579760875673277114885 7139171205164188739459041)
                  ·
                    refine ⟨5354378403873141554594281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139171205164188739459041 5354378403873141554594281)
                    ·
                      refine ⟨4015783802904856165945711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354378403873141554594281 4015783802904856165945711)
                      ·
                        rfl

theorem cell23_7820711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7820711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820711 prefixEnd_7820711 := by exact prefixLift 7820711
  have htrace : WordTrace (prefixWord ++ tailWord_7820711) baseStart_7820711 baseEnd_7820711 := by
    simpa [prefixWord, tailWord_7820711, baseEnd_7820711] using wordTrace_append hprefix tailTrace_7820711
  have hstable : (prefixWord ++ tailWord_7820711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820711).length < 2 ^ (prefixWord ++ tailWord_7820711).sum := by decide
  have hdescent : baseEnd_7820711 < baseStart_7820711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820727 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_7820727 : Nat := 118140960795 + 7820727 * 2 ^ 59
def prefixEnd_7820727 : Nat := 4983230072969 + 3 ^ 40 * 7820727 * 2
def baseEnd_7820727 : Nat := 4015792018595328103345637

theorem tailTrace_7820727 : CollatzResearch.WordTrace tailWord_7820727 prefixEnd_7820727 4015792018595328103345637 := by
  unfold tailWord_7820727
  simp only [CollatzResearch.WordTrace]
  refine ⟨285245347537849227678284435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190163565025232818452189623 285245347537849227678284435)
  ·
    refine ⟨427868021306773841517426653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285245347537849227678284435 427868021306773841517426653)
    ·
      refine ⟨160450507990040190569034995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427868021306773841517426653 160450507990040190569034995)
      ·
        refine ⟨240675761985060285853552493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160450507990040190569034995 240675761985060285853552493)
        ·
          refine ⟨90253410744397607195082185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240675761985060285853552493 90253410744397607195082185)
          ·
            refine ⟨67690058058298205396311639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90253410744397607195082185 67690058058298205396311639)
            ·
              refine ⟨101535087087447308094467459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67690058058298205396311639 101535087087447308094467459)
              ·
                refine ⟨152302630631170962141701189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101535087087447308094467459 152302630631170962141701189)
                ·
                  refine ⟨28556743243344555401568973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152302630631170962141701189 28556743243344555401568973)
                  ·
                    refine ⟨10708778716254208275588365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28556743243344555401568973 10708778716254208275588365)
                    ·
                      refine ⟨4015792018595328103345637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10708778716254208275588365 4015792018595328103345637)
                      ·
                        rfl

theorem cell23_7820727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_7820727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820727 prefixEnd_7820727 := by exact prefixLift 7820727
  have htrace : WordTrace (prefixWord ++ tailWord_7820727) baseStart_7820727 baseEnd_7820727 := by
    simpa [prefixWord, tailWord_7820727, baseEnd_7820727] using wordTrace_append hprefix tailTrace_7820727
  have hstable : (prefixWord ++ tailWord_7820727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820727).length < 2 ^ (prefixWord ++ tailWord_7820727).sum := by decide
  have hdescent : baseEnd_7820727 < baseStart_7820727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820767 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_7820767 : Nat := 118140960795 + 7820767 * 2 ^ 59
def prefixEnd_7820767 : Nat := 4983230072969 + 3 ^ 40 * 7820767 * 2
def baseEnd_7820767 : Nat := 4015812557821507946845453

theorem tailTrace_7820767 : CollatzResearch.WordTrace tailWord_7820767 prefixEnd_7820767 4015812557821507946845453 := by
  unfold tailWord_7820767
  simp only [CollatzResearch.WordTrace]
  refine ⟨285246806457704314509740555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190164537638469543006493703 285246806457704314509740555)
  ·
    refine ⟨427870209686556471764610833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285246806457704314509740555 427870209686556471764610833)
    ·
      refine ⟨320902657264917353823458125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427870209686556471764610833 320902657264917353823458125)
      ·
        refine ⟨120338496474344007683796797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320902657264917353823458125 120338496474344007683796797)
        ·
          refine ⟨45126936177879002881423799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120338496474344007683796797 45126936177879002881423799)
          ·
            refine ⟨67690404266818504322135699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45126936177879002881423799 67690404266818504322135699)
            ·
              refine ⟨101535606400227756483203549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67690404266818504322135699 101535606400227756483203549)
              ·
                refine ⟨38075852400085408681201331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101535606400227756483203549 38075852400085408681201331)
                ·
                  refine ⟨57113778600128113021801997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38075852400085408681201331 57113778600128113021801997)
                  ·
                    refine ⟨21417666975048042383175749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57113778600128113021801997 21417666975048042383175749)
                    ·
                      refine ⟨4015812557821507946845453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21417666975048042383175749 4015812557821507946845453)
                      ·
                        rfl

theorem cell23_7820767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_7820767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820767 prefixEnd_7820767 := by exact prefixLift 7820767
  have htrace : WordTrace (prefixWord ++ tailWord_7820767) baseStart_7820767 baseEnd_7820767 := by
    simpa [prefixWord, tailWord_7820767, baseEnd_7820767] using wordTrace_append hprefix tailTrace_7820767
  have hstable : (prefixWord ++ tailWord_7820767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820767).length < 2 ^ (prefixWord ++ tailWord_7820767).sum := by decide
  have hdescent : baseEnd_7820767 < baseStart_7820767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820781 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_7820781 : Nat := 118140960795 + 7820781 * 2 ^ 59
def prefixEnd_7820781 : Nat := 4983230072969 + 3 ^ 40 * 7820781 * 2
def baseEnd_7820781 : Nat := 1338606582183556964023463

theorem tailTrace_7820781 : CollatzResearch.WordTrace tailWord_7820781 prefixEnd_7820781 1338606582183556964023463 := by
  unfold tailWord_7820781
  simp only [CollatzResearch.WordTrace]
  refine ⟨285247317079653594900750197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190164878053102396600500131 285247317079653594900750197)
  ·
    refine ⟨26741935976217524521945331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285247317079653594900750197 26741935976217524521945331)
    ·
      refine ⟨40112903964326286782917997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26741935976217524521945331 40112903964326286782917997)
      ·
        refine ⟨15042338986622357543594249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40112903964326286782917997 15042338986622357543594249)
        ·
          refine ⟨11281754239966768157695687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15042338986622357543594249 11281754239966768157695687)
          ·
            refine ⟨16922631359950152236543531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281754239966768157695687 16922631359950152236543531)
            ·
              refine ⟨25383947039925228354815297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922631359950152236543531 25383947039925228354815297)
              ·
                refine ⟨19037960279943921266111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25383947039925228354815297 19037960279943921266111473)
                ·
                  refine ⟨14278470209957940949583605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19037960279943921266111473 14278470209957940949583605)
                  ·
                    refine ⟨1338606582183556964023463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14278470209957940949583605 1338606582183556964023463)
                    ·
                      rfl

theorem cell23_7820781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_7820781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820781 prefixEnd_7820781 := by exact prefixLift 7820781
  have htrace : WordTrace (prefixWord ++ tailWord_7820781) baseStart_7820781 baseEnd_7820781 := by
    simpa [prefixWord, tailWord_7820781, baseEnd_7820781] using wordTrace_append hprefix tailTrace_7820781
  have hstable : (prefixWord ++ tailWord_7820781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820781).length < 2 ^ (prefixWord ++ tailWord_7820781).sum := by decide
  have hdescent : baseEnd_7820781 < baseStart_7820781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820784 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_7820784 : Nat := 118140960795 + 7820784 * 2 ^ 59
def prefixEnd_7820784 : Nat := 4983230072969 + 3 ^ 40 * 7820784 * 2
def baseEnd_7820784 : Nat := 4015821286992634380332875

theorem tailTrace_7820784 : CollatzResearch.WordTrace tailWord_7820784 prefixEnd_7820784 4015821286992634380332875 := by
  unfold tailWord_7820784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142623713249321363206554703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190164950999095150942072937 142623713249321363206554703)
  ·
    refine ⟨213935569873982044809832055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142623713249321363206554703 213935569873982044809832055)
    ·
      refine ⟨320903354810973067214748083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213935569873982044809832055 320903354810973067214748083)
      ·
        refine ⟨481355032216459600822122125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320903354810973067214748083 481355032216459600822122125)
        ·
          refine ⟨180508137081172350308295797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481355032216459600822122125 180508137081172350308295797)
          ·
            refine ⟨16922637851359907841402731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180508137081172350308295797 16922637851359907841402731)
            ·
              refine ⟨25383956777039861762104097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922637851359907841402731 25383956777039861762104097)
              ·
                refine ⟨19037967582779896321578073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25383956777039861762104097 19037967582779896321578073)
                ·
                  refine ⟨14278475687084922241183555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19037967582779896321578073 14278475687084922241183555)
                  ·
                    refine ⟨21417713530627383361775333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14278475687084922241183555 21417713530627383361775333)
                    ·
                      refine ⟨4015821286992634380332875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21417713530627383361775333 4015821286992634380332875)
                      ·
                        rfl

theorem cell23_7820784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_7820784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820784 prefixEnd_7820784 := by exact prefixLift 7820784
  have htrace : WordTrace (prefixWord ++ tailWord_7820784) baseStart_7820784 baseEnd_7820784 := by
    simpa [prefixWord, tailWord_7820784, baseEnd_7820784] using wordTrace_append hprefix tailTrace_7820784
  have hstable : (prefixWord ++ tailWord_7820784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820784).length < 2 ^ (prefixWord ++ tailWord_7820784).sum := by decide
  have hdescent : baseEnd_7820784 < baseStart_7820784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820787 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3]
def baseStart_7820787 : Nat := 118140960795 + 7820787 * 2 ^ 59
def prefixEnd_7820787 : Nat := 4983230072969 + 3 ^ 40 * 7820787 * 2
def baseEnd_7820787 : Nat := 4015822827434597868595361

theorem tailTrace_7820787 : CollatzResearch.WordTrace tailWord_7820787 prefixEnd_7820787 4015822827434597868595361 := by
  unfold tailWord_7820787
  simp only [CollatzResearch.WordTrace]
  refine ⟨285247535917631857925468615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190165023945087905283645743 285247535917631857925468615)
  ·
    refine ⟨427871303876447786888202923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285247535917631857925468615 427871303876447786888202923)
    ·
      refine ⟨641806955814671680332304385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427871303876447786888202923 641806955814671680332304385)
      ·
        refine ⟨481355216861003760249228289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641806955814671680332304385 481355216861003760249228289)
        ·
          refine ⟨361016412645752820186921217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481355216861003760249228289 361016412645752820186921217)
          ·
            refine ⟨270762309484314615140190913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361016412645752820186921217 270762309484314615140190913)
            ·
              refine ⟨203071732113235961355143185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270762309484314615140190913 203071732113235961355143185)
              ·
                refine ⟨152303799084926971016357389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203071732113235961355143185 152303799084926971016357389)
                ·
                  refine ⟨57113924656847614131134021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152303799084926971016357389 57113924656847614131134021)
                  ·
                    refine ⟨10708860873158927649587629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57113924656847614131134021 10708860873158927649587629)
                    ·
                      refine ⟨4015822827434597868595361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10708860873158927649587629 4015822827434597868595361)
                      ·
                        rfl

theorem cell23_7820787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_7820787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820787 prefixEnd_7820787 := by exact prefixLift 7820787
  have htrace : WordTrace (prefixWord ++ tailWord_7820787) baseStart_7820787 baseEnd_7820787 := by
    simpa [prefixWord, tailWord_7820787, baseEnd_7820787] using wordTrace_append hprefix tailTrace_7820787
  have hstable : (prefixWord ++ tailWord_7820787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820787).length < 2 ^ (prefixWord ++ tailWord_7820787).sum := by decide
  have hdescent : baseEnd_7820787 < baseStart_7820787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820821 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_7820821 : Nat := 118140960795 + 7820821 * 2 ^ 59
def prefixEnd_7820821 : Nat := 4983230072969 + 3 ^ 40 * 7820821 * 2
def baseEnd_7820821 : Nat := 4015840285776850735570205

theorem tailTrace_7820821 : CollatzResearch.WordTrace tailWord_7820821 prefixEnd_7820821 4015840285776850735570205 := by
  unfold tailWord_7820821
  simp only [CollatzResearch.WordTrace]
  refine ⟨285248775999508681732206317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190165850666339121154804211 285248775999508681732206317)
  ·
    refine ⟨106968290999815755649577369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285248775999508681732206317 106968290999815755649577369)
    ·
      refine ⟨80226218249861816737183027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106968290999815755649577369 80226218249861816737183027)
      ·
        refine ⟨120339327374792725105774541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80226218249861816737183027 120339327374792725105774541)
        ·
          refine ⟨45127247765547271914665453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120339327374792725105774541 45127247765547271914665453)
          ·
            refine ⟨16922717912080226967999545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45127247765547271914665453 16922717912080226967999545)
            ·
              refine ⟨12692038434060170225999659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16922717912080226967999545 12692038434060170225999659)
              ·
                refine ⟨19038057651090255338999489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692038434060170225999659 19038057651090255338999489)
                ·
                  refine ⟨14278543238317691504249617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19038057651090255338999489 14278543238317691504249617)
                  ·
                    refine ⟨10708907428738268628187213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14278543238317691504249617 10708907428738268628187213)
                    ·
                      refine ⟨4015840285776850735570205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10708907428738268628187213 4015840285776850735570205)
                      ·
                        rfl

theorem cell23_7820821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_7820821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820821 prefixEnd_7820821 := by exact prefixLift 7820821
  have htrace : WordTrace (prefixWord ++ tailWord_7820821) baseStart_7820821 baseEnd_7820821 := by
    simpa [prefixWord, tailWord_7820821, baseEnd_7820821] using wordTrace_append hprefix tailTrace_7820821
  have hstable : (prefixWord ++ tailWord_7820821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820821).length < 2 ^ (prefixWord ++ tailWord_7820821).sum := by decide
  have hdescent : baseEnd_7820821 < baseStart_7820821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820844 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_7820844 : Nat := 118140960795 + 7820844 * 2 ^ 59
def prefixEnd_7820844 : Nat := 4983230072969 + 3 ^ 40 * 7820844 * 2
def baseEnd_7820844 : Nat := 4015852095831904145582599

theorem tailTrace_7820844 : CollatzResearch.WordTrace tailWord_7820844 prefixEnd_7820844 4015852095831904145582599 := by
  unfold tailWord_7820844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142624807439212678330146793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190166409918950237773529057 142624807439212678330146793)
  ·
    refine ⟨106968605579409508747610095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142624807439212678330146793 106968605579409508747610095)
    ·
      refine ⟨160452908369114263121415143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106968605579409508747610095 160452908369114263121415143)
      ·
        refine ⟨240679362553671394682122715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160452908369114263121415143 240679362553671394682122715)
        ·
          refine ⟨361019043830507092023184073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240679362553671394682122715 361019043830507092023184073)
          ·
            refine ⟨270764282872880319017388055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361019043830507092023184073 270764282872880319017388055)
            ·
              refine ⟨406146424309320478526082083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270764282872880319017388055 406146424309320478526082083)
              ·
                refine ⟨609219636463980717789123125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406146424309320478526082083 609219636463980717789123125)
                ·
                  refine ⟨57114340918498192292730293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609219636463980717789123125 57114340918498192292730293)
                  ·
                    refine ⟨5354469461109205527443465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57114340918498192292730293 5354469461109205527443465)
                    ·
                      refine ⟨4015852095831904145582599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354469461109205527443465 4015852095831904145582599)
                      ·
                        rfl

theorem cell23_7820844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_7820844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820844 prefixEnd_7820844 := by exact prefixLift 7820844
  have htrace : WordTrace (prefixWord ++ tailWord_7820844) baseStart_7820844 baseEnd_7820844 := by
    simpa [prefixWord, tailWord_7820844, baseEnd_7820844] using wordTrace_append hprefix tailTrace_7820844
  have hstable : (prefixWord ++ tailWord_7820844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820844).length < 2 ^ (prefixWord ++ tailWord_7820844).sum := by decide
  have hdescent : baseEnd_7820844 < baseStart_7820844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820874 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_7820874 : Nat := 118140960795 + 7820874 * 2 ^ 59
def prefixEnd_7820874 : Nat := 4983230072969 + 3 ^ 40 * 7820874 * 2
def baseEnd_7820874 : Nat := 4015867500251539028207461

theorem tailTrace_7820874 : CollatzResearch.WordTrace tailWord_7820874 prefixEnd_7820874 4015867500251539028207461 := by
  unfold tailWord_7820874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71312677267079167945971419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190167139378877781189257117 71312677267079167945971419)
  ·
    refine ⟨106969015900618751918957129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71312677267079167945971419 106969015900618751918957129)
    ·
      refine ⟨80226761925464063939217847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106969015900618751918957129 80226761925464063939217847)
      ·
        refine ⟨120340142888196095908826771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80226761925464063939217847 120340142888196095908826771)
        ·
          refine ⟨180510214332294143863240157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120340142888196095908826771 180510214332294143863240157)
          ·
            refine ⟨67691330374610303948715059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180510214332294143863240157 67691330374610303948715059)
            ·
              refine ⟨101536995561915455923072589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67691330374610303948715059 101536995561915455923072589)
              ·
                refine ⟨38076373335718295971152221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101536995561915455923072589 38076373335718295971152221)
                ·
                  refine ⟨14278640000894360989182083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38076373335718295971152221 14278640000894360989182083)
                  ·
                    refine ⟨21417960001341541483773125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14278640000894360989182083 21417960001341541483773125)
                    ·
                      refine ⟨4015867500251539028207461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21417960001341541483773125 4015867500251539028207461)
                      ·
                        rfl

theorem cell23_7820874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_7820874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820874 prefixEnd_7820874 := by exact prefixLift 7820874
  have htrace : WordTrace (prefixWord ++ tailWord_7820874) baseStart_7820874 baseEnd_7820874 := by
    simpa [prefixWord, tailWord_7820874, baseEnd_7820874] using wordTrace_append hprefix tailTrace_7820874
  have hstable : (prefixWord ++ tailWord_7820874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820874).length < 2 ^ (prefixWord ++ tailWord_7820874).sum := by decide
  have hdescent : baseEnd_7820874 < baseStart_7820874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820884 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_7820884 : Nat := 118140960795 + 7820884 * 2 ^ 59
def prefixEnd_7820884 : Nat := 4983230072969 + 3 ^ 40 * 7820884 * 2
def baseEnd_7820884 : Nat := 1338624211686027996360805

theorem tailTrace_7820884 : CollatzResearch.WordTrace tailWord_7820884 prefixEnd_7820884 1338624211686027996360805 := by
  unfold tailWord_7820884
  simp only [CollatzResearch.WordTrace]
  refine ⟨142625536899140221745874853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190167382532186962327833137 142625536899140221745874853)
  ·
    refine ⟨26742288168588791577351535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142625536899140221745874853 26742288168588791577351535)
    ·
      refine ⟨40113432252883187366027303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26742288168588791577351535 40113432252883187366027303)
      ·
        refine ⟨60170148379324781049040955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40113432252883187366027303 60170148379324781049040955)
        ·
          refine ⟨90255222568987171573561433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60170148379324781049040955 90255222568987171573561433)
          ·
            refine ⟨67691416926740378680171075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90255222568987171573561433 67691416926740378680171075)
            ·
              refine ⟨101537125390110568020256613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67691416926740378680171075 101537125390110568020256613)
              ·
                refine ⟨19038211010645731503798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101537125390110568020256613 19038211010645731503798115)
                ·
                  refine ⟨28557316515968597255697173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19038211010645731503798115 28557316515968597255697173)
                  ·
                    refine ⟨1338624211686027996360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28557316515968597255697173 1338624211686027996360805)
                    ·
                      rfl

theorem cell23_7820884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_7820884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820884 prefixEnd_7820884 := by exact prefixLift 7820884
  have htrace : WordTrace (prefixWord ++ tailWord_7820884) baseStart_7820884 baseEnd_7820884 := by
    simpa [prefixWord, tailWord_7820884, baseEnd_7820884] using wordTrace_append hprefix tailTrace_7820884
  have hstable : (prefixWord ++ tailWord_7820884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820884).length < 2 ^ (prefixWord ++ tailWord_7820884).sum := by decide
  have hdescent : baseEnd_7820884 < baseStart_7820884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820897 : List Nat := [1, 2, 3, 1, 1, 3, 12]
def baseStart_7820897 : Nat := 118140960795 + 7820897 * 2 ^ 59
def prefixEnd_7820897 : Nat := 4983230072969 + 3 ^ 40 * 7820897 * 2
def baseEnd_7820897 : Nat := 49578756917365338743455

theorem tailTrace_7820897 : CollatzResearch.WordTrace tailWord_7820897 prefixEnd_7820897 49578756917365338743455 := by
  unfold tailWord_7820897
  simp only [CollatzResearch.WordTrace]
  refine ⟨285251547947233346711972945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190167698631488897807981963 285251547947233346711972945)
  ·
    refine ⟨213938660960425010033979709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285251547947233346711972945 213938660960425010033979709)
    ·
      refine ⟨80226997860159378762742391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213938660960425010033979709 80226997860159378762742391)
      ·
        refine ⟨120340496790239068144113587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80226997860159378762742391 120340496790239068144113587)
        ·
          refine ⟨180510745185358602216170381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120340496790239068144113587 180510745185358602216170381)
          ·
            refine ⟨67691529444509475831063893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180510745185358602216170381 67691529444509475831063893)
            ·
              refine ⟨49578756917365338743455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67691529444509475831063893 49578756917365338743455)
              ·
                rfl

theorem cell23_7820897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 12].length) (baseStart_7820897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820897 prefixEnd_7820897 := by exact prefixLift 7820897
  have htrace : WordTrace (prefixWord ++ tailWord_7820897) baseStart_7820897 baseEnd_7820897 := by
    simpa [prefixWord, tailWord_7820897, baseEnd_7820897] using wordTrace_append hprefix tailTrace_7820897
  have hstable : (prefixWord ++ tailWord_7820897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820897).length < 2 ^ (prefixWord ++ tailWord_7820897).sum := by decide
  have hdescent : baseEnd_7820897 < baseStart_7820897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820901 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_7820901 : Nat := 118140960795 + 7820901 * 2 ^ 59
def prefixEnd_7820901 : Nat := 4983230072969 + 3 ^ 40 * 7820901 * 2
def baseEnd_7820901 : Nat := 1338627121409736807523279

theorem tailTrace_7820901 : CollatzResearch.WordTrace tailWord_7820901 prefixEnd_7820901 1338627121409736807523279 := by
  unfold tailWord_7820901
  simp only [CollatzResearch.WordTrace]
  refine ⟨285251693839218855395118557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190167795892812570263412371 285251693839218855395118557)
  ·
    refine ⟨106969385189707070773169459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285251693839218855395118557 106969385189707070773169459)
    ·
      refine ⟨160454077784560606159754189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106969385189707070773169459 160454077784560606159754189)
      ·
        refine ⟨60170279169210227309907821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160454077784560606159754189 60170279169210227309907821)
        ·
          refine ⟨22563854688453835241215433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60170279169210227309907821 22563854688453835241215433)
          ·
            refine ⟨16922891016340376430911575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22563854688453835241215433 16922891016340376430911575)
            ·
              refine ⟨25384336524510564646367363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922891016340376430911575 25384336524510564646367363)
              ·
                refine ⟨38076504786765846969551045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25384336524510564646367363 38076504786765846969551045)
                ·
                  refine ⟨7139344647518596306790821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38076504786765846969551045 7139344647518596306790821)
                  ·
                    refine ⟨1338627121409736807523279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139344647518596306790821 1338627121409736807523279)
                    ·
                      rfl

theorem cell23_7820901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_7820901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820901 prefixEnd_7820901 := by exact prefixLift 7820901
  have htrace : WordTrace (prefixWord ++ tailWord_7820901) baseStart_7820901 baseEnd_7820901 := by
    simpa [prefixWord, tailWord_7820901, baseEnd_7820901] using wordTrace_append hprefix tailTrace_7820901
  have hstable : (prefixWord ++ tailWord_7820901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820901).length < 2 ^ (prefixWord ++ tailWord_7820901).sum := by decide
  have hdescent : baseEnd_7820901 < baseStart_7820901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820918 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_7820918 : Nat := 118140960795 + 7820918 * 2 ^ 59
def prefixEnd_7820918 : Nat := 4983230072969 + 3 ^ 40 * 7820918 * 2
def baseEnd_7820918 : Nat := 1338630031133445618685753

theorem tailTrace_7820918 : CollatzResearch.WordTrace tailWord_7820918 prefixEnd_7820918 1338630031133445618685753 := by
  unfold tailWord_7820918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828269617509829206155463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190168209253438178198991605 17828269617509829206155463)
  ·
    refine ⟨26742404426264743809233195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17828269617509829206155463 26742404426264743809233195)
    ·
      refine ⟨40113606639397115713849793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26742404426264743809233195 40113606639397115713849793)
      ·
        refine ⟨30085204979547836785387345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40113606639397115713849793 30085204979547836785387345)
        ·
          refine ⟨22563903734660877589040509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30085204979547836785387345 22563903734660877589040509)
          ·
            refine ⟨8461463900497829095890191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22563903734660877589040509 8461463900497829095890191)
            ·
              refine ⟨12692195850746743643835287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461463900497829095890191 12692195850746743643835287)
              ·
                refine ⟨19038293776120115465752931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692195850746743643835287 19038293776120115465752931)
                ·
                  refine ⟨28557440664180173198629397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19038293776120115465752931 28557440664180173198629397)
                  ·
                    refine ⟨1338630031133445618685753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28557440664180173198629397 1338630031133445618685753)
                    ·
                      rfl

theorem cell23_7820918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_7820918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820918 prefixEnd_7820918 := by exact prefixLift 7820918
  have htrace : WordTrace (prefixWord ++ tailWord_7820918) baseStart_7820918 baseEnd_7820918 := by
    simpa [prefixWord, tailWord_7820918, baseEnd_7820918] using wordTrace_append hprefix tailTrace_7820918
  have hstable : (prefixWord ++ tailWord_7820918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820918).length < 2 ^ (prefixWord ++ tailWord_7820918).sum := by decide
  have hdescent : baseEnd_7820918 < baseStart_7820918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820927 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 9]
def baseStart_7820927 : Nat := 118140960795 + 7820927 * 2 ^ 59
def prefixEnd_7820927 : Nat := 4983230072969 + 3 ^ 40 * 7820927 * 2
def baseEnd_7820927 : Nat := 1338631571575409106948239

theorem tailTrace_7820927 : CollatzResearch.WordTrace tailWord_7820927 prefixEnd_7820927 1338631571575409106948239 := by
  unfold tailWord_7820927
  simp only [CollatzResearch.WordTrace]
  refine ⟨285252642137124661835565035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190168428091416441223710023 285252642137124661835565035)
  ·
    refine ⟨427878963205686992753347553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285252642137124661835565035 427878963205686992753347553)
    ·
      refine ⟨320909222404265244565010665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427878963205686992753347553 320909222404265244565010665)
      ·
        refine ⟨240681916803198933423757999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320909222404265244565010665 240681916803198933423757999)
        ·
          refine ⟨361022875204798400135636999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240681916803198933423757999 361022875204798400135636999)
          ·
            refine ⟨541534312807197600203455499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361022875204798400135636999 541534312807197600203455499)
            ·
              refine ⟨812301469210796400305183249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541534312807197600203455499 812301469210796400305183249)
              ·
                refine ⟨609226101908097300228887437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812301469210796400305183249 609226101908097300228887437)
                ·
                  refine ⟨228459788215536487585832789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609226101908097300228887437 228459788215536487585832789)
                  ·
                    refine ⟨1338631571575409106948239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228459788215536487585832789 1338631571575409106948239)
                    ·
                      rfl

theorem cell23_7820927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_7820927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820927 prefixEnd_7820927 := by exact prefixLift 7820927
  have htrace : WordTrace (prefixWord ++ tailWord_7820927) baseStart_7820927 baseEnd_7820927 := by
    simpa [prefixWord, tailWord_7820927, baseEnd_7820927] using wordTrace_append hprefix tailTrace_7820927
  have hstable : (prefixWord ++ tailWord_7820927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820927).length < 2 ^ (prefixWord ++ tailWord_7820927).sum := by decide
  have hdescent : baseEnd_7820927 < baseStart_7820927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820942 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7820942 : Nat := 118140960795 + 7820942 * 2 ^ 59
def prefixEnd_7820942 : Nat := 4983230072969 + 3 ^ 40 * 7820942 * 2
def baseEnd_7820942 : Nat := 4015902416936044762157149

theorem tailTrace_7820942 : CollatzResearch.WordTrace tailWord_7820942 prefixEnd_7820942 4015902416936044762157149 := by
  unfold tailWord_7820942
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656648654008789924670135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190168792821380212931574053 35656648654008789924670135)
  ·
    refine ⟨53484972981013184887005203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35656648654008789924670135 53484972981013184887005203)
    ·
      refine ⟨80227459471519777330507805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53484972981013184887005203 80227459471519777330507805)
      ·
        refine ⟨30085297301819916498940427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80227459471519777330507805 30085297301819916498940427)
        ·
          refine ⟨45127945952729874748410641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30085297301819916498940427 45127945952729874748410641)
          ·
            refine ⟨33845959464547406061307981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45127945952729874748410641 33845959464547406061307981)
            ·
              refine ⟨12692234799205277272990493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33845959464547406061307981 12692234799205277272990493)
              ·
                refine ⟨4759588049701978977371435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12692234799205277272990493 4759588049701978977371435)
                ·
                  refine ⟨7139382074552968466057153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759588049701978977371435 7139382074552968466057153)
                  ·
                    refine ⟨5354536555914726349542865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139382074552968466057153 5354536555914726349542865)
                    ·
                      refine ⟨4015902416936044762157149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354536555914726349542865 4015902416936044762157149)
                      ·
                        rfl

theorem cell23_7820942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7820942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820942 prefixEnd_7820942 := by exact prefixLift 7820942
  have htrace : WordTrace (prefixWord ++ tailWord_7820942) baseStart_7820942 baseEnd_7820942 := by
    simpa [prefixWord, tailWord_7820942, baseEnd_7820942] using wordTrace_append hprefix tailTrace_7820942
  have hstable : (prefixWord ++ tailWord_7820942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820942).length < 2 ^ (prefixWord ++ tailWord_7820942).sum := by decide
  have hdescent : baseEnd_7820942 < baseStart_7820942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820948 : List Nat := [2, 4, 2, 2, 3, 1, 9]
def baseStart_7820948 : Nat := 118140960795 + 7820948 * 2 ^ 59
def prefixEnd_7820948 : Nat := 4983230072969 + 3 ^ 40 * 7820948 * 2
def baseEnd_7820948 : Nat := 49579080219999651094841

theorem tailTrace_7820948 : CollatzResearch.WordTrace tailWord_7820948 prefixEnd_7820948 49579080219999651094841 := by
  unfold tailWord_7820948
  simp only [CollatzResearch.WordTrace]
  refine ⟨142626704035024291211039749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190168938713365721614719665 142626704035024291211039749)
  ·
    refine ⟨26742507006567054602069953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142626704035024291211039749 26742507006567054602069953)
    ·
      refine ⟨20056880254925290951552465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26742507006567054602069953 20056880254925290951552465)
      ·
        refine ⟨15042660191193968213664349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20056880254925290951552465 15042660191193968213664349)
        ·
          refine ⟨5640997571697738080124131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15042660191193968213664349 5640997571697738080124131)
          ·
            refine ⟨8461496357546607120186197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640997571697738080124131 8461496357546607120186197)
            ·
              refine ⟨49579080219999651094841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8461496357546607120186197 49579080219999651094841)
              ·
                rfl

theorem cell23_7820948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 9].length) (baseStart_7820948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820948 prefixEnd_7820948 := by exact prefixLift 7820948
  have htrace : WordTrace (prefixWord ++ tailWord_7820948) baseStart_7820948 baseEnd_7820948 := by
    simpa [prefixWord, tailWord_7820948, baseEnd_7820948] using wordTrace_append hprefix tailTrace_7820948
  have hstable : (prefixWord ++ tailWord_7820948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820948).length < 2 ^ (prefixWord ++ tailWord_7820948).sum := by decide
  have hdescent : baseEnd_7820948 < baseStart_7820948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7820959 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7820959 : Nat := 118140960795 + 7820959 * 2 ^ 59
def prefixEnd_7820959 : Nat := 4983230072969 + 3 ^ 40 * 7820959 * 2
def baseEnd_7820959 : Nat := 4015911146107171195644571

theorem tailTrace_7820959 : CollatzResearch.WordTrace tailWord_7820959 prefixEnd_7820959 4015911146107171195644571 := by
  unfold tailWord_7820959
  simp only [CollatzResearch.WordTrace]
  refine ⟨285253809273008731300729931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190169206182005820867153287 285253809273008731300729931)
  ·
    refine ⟨427880713909513096951094897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285253809273008731300729931 427880713909513096951094897)
    ·
      refine ⟨320910535432134822713321173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427880713909513096951094897 320910535432134822713321173)
      ·
        refine ⟨7521340674190659907343465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 320910535432134822713321173 7521340674190659907343465)
        ·
          refine ⟨5641005505642994930507599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521340674190659907343465 5641005505642994930507599)
          ·
            refine ⟨8461508258464492395761399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641005505642994930507599 8461508258464492395761399)
            ·
              refine ⟨12692262387696738593642099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461508258464492395761399 12692262387696738593642099)
              ·
                refine ⟨19038393581545107890463149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692262387696738593642099 19038393581545107890463149)
                ·
                  refine ⟨7139397593079415458923681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19038393581545107890463149 7139397593079415458923681)
                  ·
                    refine ⟨5354548194809561594192761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139397593079415458923681 5354548194809561594192761)
                    ·
                      refine ⟨4015911146107171195644571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354548194809561594192761 4015911146107171195644571)
                      ·
                        rfl

theorem cell23_7820959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7820959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7820959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7820959 prefixEnd_7820959 := by exact prefixLift 7820959
  have htrace : WordTrace (prefixWord ++ tailWord_7820959) baseStart_7820959 baseEnd_7820959 := by
    simpa [prefixWord, tailWord_7820959, baseEnd_7820959] using wordTrace_append hprefix tailTrace_7820959
  have hstable : (prefixWord ++ tailWord_7820959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7820959).length < 2 ^ (prefixWord ++ tailWord_7820959).sum := by decide
  have hdescent : baseEnd_7820959 < baseStart_7820959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7820959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821002 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_7821002 : Nat := 118140960795 + 7821002 * 2 ^ 59
def prefixEnd_7821002 : Nat := 4983230072969 + 3 ^ 40 * 7821002 * 2
def baseEnd_7821002 : Nat := 4015933225775314527406873

theorem tailTrace_7821002 : CollatzResearch.WordTrace tailWord_7821002 prefixEnd_7821002 4015933225775314527406873 := by
  unfold tailWord_7821002
  simp only [CollatzResearch.WordTrace]
  refine ⟨71313844402963237411136315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190170251741235299763030173 71313844402963237411136315)
  ·
    refine ⟨106970766604444856116704473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71313844402963237411136315 106970766604444856116704473)
    ·
      refine ⟨80228074953333642087528355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106970766604444856116704473 80228074953333642087528355)
      ·
        refine ⟨120342112430000463131292533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80228074953333642087528355 120342112430000463131292533)
        ·
          refine ⟨11282073040312543418558675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120342112430000463131292533 11282073040312543418558675)
          ·
            refine ⟨16923109560468815127838013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282073040312543418558675 16923109560468815127838013)
            ·
              refine ⟨6346166085175805672939255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16923109560468815127838013 6346166085175805672939255)
              ·
                refine ⟨9519249127763708509408883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346166085175805672939255 9519249127763708509408883)
                ·
                  refine ⟨14278873691645562764113325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519249127763708509408883 14278873691645562764113325)
                  ·
                    refine ⟨5354577634367086036542497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14278873691645562764113325 5354577634367086036542497)
                    ·
                      refine ⟨4015933225775314527406873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354577634367086036542497 4015933225775314527406873)
                      ·
                        rfl

theorem cell23_7821002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_7821002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821002 prefixEnd_7821002 := by exact prefixLift 7821002
  have htrace : WordTrace (prefixWord ++ tailWord_7821002) baseStart_7821002 baseEnd_7821002 := by
    simpa [prefixWord, tailWord_7821002, baseEnd_7821002] using wordTrace_append hprefix tailTrace_7821002
  have hstable : (prefixWord ++ tailWord_7821002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821002).length < 2 ^ (prefixWord ++ tailWord_7821002).sum := by decide
  have hdescent : baseEnd_7821002 < baseStart_7821002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821015 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 2, 2, 2]
def baseStart_7821015 : Nat := 118140960795 + 7821015 * 2 ^ 59
def prefixEnd_7821015 : Nat := 4983230072969 + 3 ^ 40 * 7821015 * 2
def baseEnd_7821015 : Nat := 4015939901023822976544313

theorem tailTrace_7821015 : CollatzResearch.WordTrace tailWord_7821015 prefixEnd_7821015 4015939901023822976544313 := by
  unfold tailWord_7821015
  simp only [CollatzResearch.WordTrace]
  refine ⟨285255851760805852864768499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190170567840537235243178999 285255851760805852864768499)
  ·
    refine ⟨427883777641208779297152749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285255851760805852864768499 427883777641208779297152749)
    ·
      refine ⟨160456416615453292236432281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427883777641208779297152749 160456416615453292236432281)
      ·
        refine ⟨120342312461589969177324211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160456416615453292236432281 120342312461589969177324211)
        ·
          refine ⟨180513468692384953765986317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120342312461589969177324211 180513468692384953765986317)
          ·
            refine ⟨67692550759644357662244869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180513468692384953765986317 67692550759644357662244869)
            ·
              refine ⟨12692353267433317061670913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67692550759644357662244869 12692353267433317061670913)
              ·
                refine ⟨9519264950574987796253185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12692353267433317061670913 9519264950574987796253185)
                ·
                  refine ⟨7139448712931240847189889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9519264950574987796253185 7139448712931240847189889)
                  ·
                    refine ⟨5354586534698430635392417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139448712931240847189889 5354586534698430635392417)
                    ·
                      refine ⟨4015939901023822976544313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354586534698430635392417 4015939901023822976544313)
                      ·
                        rfl

theorem cell23_7821015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_7821015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821015 prefixEnd_7821015 := by exact prefixLift 7821015
  have htrace : WordTrace (prefixWord ++ tailWord_7821015) baseStart_7821015 baseEnd_7821015 := by
    simpa [prefixWord, tailWord_7821015, baseEnd_7821015] using wordTrace_append hprefix tailTrace_7821015
  have hstable : (prefixWord ++ tailWord_7821015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821015).length < 2 ^ (prefixWord ++ tailWord_7821015).sum := by decide
  have hdescent : baseEnd_7821015 < baseStart_7821015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821088 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7821088 : Nat := 118140960795 + 7821088 * 2 ^ 59
def prefixEnd_7821088 : Nat := 4983230072969 + 3 ^ 40 * 7821088 * 2
def baseEnd_7821088 : Nat := 4015977385111601190931477

theorem tailTrace_7821088 : CollatzResearch.WordTrace tailWord_7821088 prefixEnd_7821088 4015977385111601190931477 := by
  unfold tailWord_7821088
  simp only [CollatzResearch.WordTrace]
  refine ⟨142629257144770693166087959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190172342859694257554783945 142629257144770693166087959)
  ·
    refine ⟨213943885717156039749131939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142629257144770693166087959 213943885717156039749131939)
    ·
      refine ⟨320915828575734059623697909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213943885717156039749131939 320915828575734059623697909)
      ·
        refine ⟨30085858928975068089721679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320915828575734059623697909 30085858928975068089721679)
        ·
          refine ⟨45128788393462602134582519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30085858928975068089721679 45128788393462602134582519)
          ·
            refine ⟨67693182590193903201873779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45128788393462602134582519 67693182590193903201873779)
            ·
              refine ⟨101539773885290854802810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67693182590193903201873779 101539773885290854802810669)
              ·
                refine ⟨38077415206984070551054001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101539773885290854802810669 38077415206984070551054001)
                ·
                  refine ⟨28558061405238052913290501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38077415206984070551054001 28558061405238052913290501)
                  ·
                    refine ⟨5354636513482134921241969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28558061405238052913290501 5354636513482134921241969)
                    ·
                      refine ⟨4015977385111601190931477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354636513482134921241969 4015977385111601190931477)
                      ·
                        rfl

theorem cell23_7821088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7821088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821088 prefixEnd_7821088 := by exact prefixLift 7821088
  have htrace : WordTrace (prefixWord ++ tailWord_7821088) baseStart_7821088 baseEnd_7821088 := by
    simpa [prefixWord, tailWord_7821088, baseEnd_7821088] using wordTrace_append hprefix tailTrace_7821088
  have hstable : (prefixWord ++ tailWord_7821088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821088).length < 2 ^ (prefixWord ++ tailWord_7821088).sum := by decide
  have hdescent : baseEnd_7821088 < baseStart_7821088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821091 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3]
def baseStart_7821091 : Nat := 118140960795 + 7821091 * 2 ^ 59
def prefixEnd_7821091 : Nat := 4983230072969 + 3 ^ 40 * 7821091 * 2
def baseEnd_7821091 : Nat := 4015978925553564679193963

theorem tailTrace_7821091 : CollatzResearch.WordTrace tailWord_7821091 prefixEnd_7821091 4015978925553564679193963 := by
  unfold tailWord_7821091
  simp only [CollatzResearch.WordTrace]
  refine ⟨285258623708530517844535127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190172415805687011896356751 285258623708530517844535127)
  ·
    refine ⟨427887935562795776766802691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285258623708530517844535127 427887935562795776766802691)
    ·
      refine ⟨641831903344193665150204037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427887935562795776766802691 641831903344193665150204037)
      ·
        refine ⟨120343481877036312215663257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641831903344193665150204037 120343481877036312215663257)
        ·
          refine ⟨90257611407777234161747443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120343481877036312215663257 90257611407777234161747443)
          ·
            refine ⟨135386417111665851242621165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90257611407777234161747443 135386417111665851242621165)
            ·
              refine ⟨50769906416874694215982937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135386417111665851242621165 50769906416874694215982937)
              ·
                refine ⟨38077429812656020661987203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50769906416874694215982937 38077429812656020661987203)
                ·
                  refine ⟨57116144718984030992980805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38077429812656020661987203 57116144718984030992980805)
                  ·
                    refine ⟨10709277134809505811183901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57116144718984030992980805 10709277134809505811183901)
                    ·
                      refine ⟨4015978925553564679193963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10709277134809505811183901 4015978925553564679193963)
                      ·
                        rfl

theorem cell23_7821091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_7821091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821091 prefixEnd_7821091 := by exact prefixLift 7821091
  have htrace : WordTrace (prefixWord ++ tailWord_7821091) baseStart_7821091 baseEnd_7821091 := by
    simpa [prefixWord, tailWord_7821091, baseEnd_7821091] using wordTrace_append hprefix tailTrace_7821091
  have hstable : (prefixWord ++ tailWord_7821091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821091).length < 2 ^ (prefixWord ++ tailWord_7821091).sum := by decide
  have hdescent : baseEnd_7821091 < baseStart_7821091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821104 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_7821104 : Nat := 118140960795 + 7821104 * 2 ^ 59
def prefixEnd_7821104 : Nat := 4983230072969 + 3 ^ 40 * 7821104 * 2
def baseEnd_7821104 : Nat := 4015985600802073128331403

theorem tailTrace_7821104 : CollatzResearch.WordTrace tailWord_7821104 prefixEnd_7821104 4015985600802073128331403 := by
  unfold tailWord_7821104
  simp only [CollatzResearch.WordTrace]
  refine ⟨142629548928741710532379183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190172731904988947376505577 142629548928741710532379183)
  ·
    refine ⟨213944323393112565798568775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142629548928741710532379183 213944323393112565798568775)
    ·
      refine ⟨320916485089668848697853163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213944323393112565798568775 320916485089668848697853163)
      ·
        refine ⟨481374727634503273046779745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320916485089668848697853163 481374727634503273046779745)
        ·
          refine ⟨361031045725877454785084809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481374727634503273046779745 361031045725877454785084809)
          ·
            refine ⟨270773284294408091088813607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361031045725877454785084809 270773284294408091088813607)
            ·
              refine ⟨406159926441612136633220411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270773284294408091088813607 406159926441612136633220411)
              ·
                refine ⟨609239889662418204949830617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406159926441612136633220411 609239889662418204949830617)
                ·
                  refine ⟨456929917246813653712372963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609239889662418204949830617 456929917246813653712372963)
                  ·
                    refine ⟨685394875870220480568559445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456929917246813653712372963 685394875870220480568559445)
                    ·
                      refine ⟨4015985600802073128331403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 685394875870220480568559445 4015985600802073128331403)
                      ·
                        rfl

theorem cell23_7821104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_7821104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821104 prefixEnd_7821104 := by exact prefixLift 7821104
  have htrace : WordTrace (prefixWord ++ tailWord_7821104) baseStart_7821104 baseEnd_7821104 := by
    simpa [prefixWord, tailWord_7821104, baseEnd_7821104] using wordTrace_append hprefix tailTrace_7821104
  have hstable : (prefixWord ++ tailWord_7821104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821104).length < 2 ^ (prefixWord ++ tailWord_7821104).sum := by decide
  have hdescent : baseEnd_7821104 < baseStart_7821104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821132 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_7821132 : Nat := 118140960795 + 7821132 * 2 ^ 59
def prefixEnd_7821132 : Nat := 4983230072969 + 3 ^ 40 * 7821132 * 2
def baseEnd_7821132 : Nat := 1338666659420133006260425

theorem tailTrace_7821132 : CollatzResearch.WordTrace tailWord_7821132 prefixEnd_7821132 1338666659420133006260425 := by
  unfold tailWord_7821132
  simp only [CollatzResearch.WordTrace]
  refine ⟨142630059550690990923388825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190173412734254654564518433 142630059550690990923388825)
  ·
    refine ⟨106972544663018243192541619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142630059550690990923388825 106972544663018243192541619)
    ·
      refine ⟨160458816994527364788812429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106972544663018243192541619 160458816994527364788812429)
      ·
        refine ⟨60172056372947761795804661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160458816994527364788812429 60172056372947761795804661)
        ·
          refine ⟨5641130284963852668356687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60172056372947761795804661 5641130284963852668356687)
          ·
            refine ⟨8461695427445779002535031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641130284963852668356687 8461695427445779002535031)
            ·
              refine ⟨12692543141168668503802547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461695427445779002535031 12692543141168668503802547)
              ·
                refine ⟨19038814711753002755703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692543141168668503802547 19038814711753002755703821)
                ·
                  refine ⟨7139555516907376033388933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19038814711753002755703821 7139555516907376033388933)
                  ·
                    refine ⟨1338666659420133006260425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139555516907376033388933 1338666659420133006260425)
                    ·
                      rfl

theorem cell23_7821132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_7821132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821132 prefixEnd_7821132 := by exact prefixLift 7821132
  have htrace : WordTrace (prefixWord ++ tailWord_7821132) baseStart_7821132 baseEnd_7821132 := by
    simpa [prefixWord, tailWord_7821132, baseEnd_7821132] using wordTrace_append hprefix tailTrace_7821132
  have hstable : (prefixWord ++ tailWord_7821132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821132).length < 2 ^ (prefixWord ++ tailWord_7821132).sum := by decide
  have hdescent : baseEnd_7821132 < baseStart_7821132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821165 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_7821165 : Nat := 118140960795 + 7821165 * 2 ^ 59
def prefixEnd_7821165 : Nat := 4983230072969 + 3 ^ 40 * 7821165 * 2
def baseEnd_7821165 : Nat := 4016016923121997389668623

theorem tailTrace_7821165 : CollatzResearch.WordTrace tailWord_7821165 prefixEnd_7821165 4016016923121997389668623 := by
  unfold tailWord_7821165
  simp only [CollatzResearch.WordTrace]
  refine ⟨285261322710262428482728949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190174215140174952321819299 285261322710262428482728949)
  ·
    refine ⟨26743249004087102670255839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285261322710262428482728949 26743249004087102670255839)
    ·
      refine ⟨40114873506130654005383759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743249004087102670255839 40114873506130654005383759)
      ·
        refine ⟨60172310259195981008075639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40114873506130654005383759 60172310259195981008075639)
        ·
          refine ⟨90258465388793971512113459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60172310259195981008075639 90258465388793971512113459)
          ·
            refine ⟨135387698083190957268170189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90258465388793971512113459 135387698083190957268170189)
            ·
              refine ⟨50770386781196608975563821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135387698083190957268170189 50770386781196608975563821)
              ·
                refine ⟨19038895042948728365836433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50770386781196608975563821 19038895042948728365836433)
                ·
                  refine ⟨14279171282211546274377325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19038895042948728365836433 14279171282211546274377325)
                  ·
                    refine ⟨5354689230829329852891497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14279171282211546274377325 5354689230829329852891497)
                    ·
                      refine ⟨4016016923121997389668623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354689230829329852891497 4016016923121997389668623)
                      ·
                        rfl

theorem cell23_7821165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_7821165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821165 prefixEnd_7821165 := by exact prefixLift 7821165
  have htrace : WordTrace (prefixWord ++ tailWord_7821165) baseStart_7821165 baseEnd_7821165 := by
    simpa [prefixWord, tailWord_7821165, baseEnd_7821165] using wordTrace_append hprefix tailTrace_7821165
  have hstable : (prefixWord ++ tailWord_7821165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821165).length < 2 ^ (prefixWord ++ tailWord_7821165).sum := by decide
  have hdescent : baseEnd_7821165 < baseStart_7821165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821178 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_7821178 : Nat := 118140960795 + 7821178 * 2 ^ 59
def prefixEnd_7821178 : Nat := 4983230072969 + 3 ^ 40 * 7821178 * 2
def baseEnd_7821178 : Nat := 4016023598370505838806063

theorem tailTrace_7821178 : CollatzResearch.WordTrace tailWord_7821178 prefixEnd_7821178 4016023598370505838806063 := by
  unfold tailWord_7821178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71315449214803832925738047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190174531239476887801968125 71315449214803832925738047)
  ·
    refine ⟨106973173822205749388607071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71315449214803832925738047 106973173822205749388607071)
    ·
      refine ⟨160459760733308624082910607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106973173822205749388607071 160459760733308624082910607)
      ·
        refine ⟨240689641099962936124365911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160459760733308624082910607 240689641099962936124365911)
        ·
          refine ⟨361034461649944404186548867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240689641099962936124365911 361034461649944404186548867)
          ·
            refine ⟨541551692474916606279823301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361034461649944404186548867 541551692474916606279823301)
            ·
              refine ⟨101540942339046863677466869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541551692474916606279823301 101540942339046863677466869)
              ·
                refine ⟨9519463344285643469762519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101540942339046863677466869 9519463344285643469762519)
                ·
                  refine ⟨14279195016428465204643779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519463344285643469762519 14279195016428465204643779)
                  ·
                    refine ⟨21418792524642697806965669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14279195016428465204643779 21418792524642697806965669)
                    ·
                      refine ⟨4016023598370505838806063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21418792524642697806965669 4016023598370505838806063)
                      ·
                        rfl

theorem cell23_7821178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_7821178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821178 prefixEnd_7821178 := by exact prefixLift 7821178
  have htrace : WordTrace (prefixWord ++ tailWord_7821178) baseStart_7821178 baseEnd_7821178 := by
    simpa [prefixWord, tailWord_7821178, baseEnd_7821178] using wordTrace_append hprefix tailTrace_7821178
  have hstable : (prefixWord ++ tailWord_7821178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821178).length < 2 ^ (prefixWord ++ tailWord_7821178).sum := by decide
  have hdescent : baseEnd_7821178 < baseStart_7821178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821188 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7821188 : Nat := 118140960795 + 7821188 * 2 ^ 59
def prefixEnd_7821188 : Nat := 4983230072969 + 3 ^ 40 * 7821188 * 2
def baseEnd_7821188 : Nat := 1338676244392350266560339

theorem tailTrace_7821188 : CollatzResearch.WordTrace tailWord_7821188 prefixEnd_7821188 1338676244392350266560339 := by
  unfold tailWord_7821188
  simp only [CollatzResearch.WordTrace]
  refine ⟨142631080794589551705408109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190174774392786068940544145 142631080794589551705408109)
  ·
    refine ⟨53486655297971081889528041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142631080794589551705408109 53486655297971081889528041)
    ·
      refine ⟨40114991473478311417146031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53486655297971081889528041 40114991473478311417146031)
      ·
        refine ⟨60172487210217467125719047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40114991473478311417146031 60172487210217467125719047)
        ·
          refine ⟨90258730815326200688578571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60172487210217467125719047 90258730815326200688578571)
          ·
            refine ⟨135388096222989301032867857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90258730815326200688578571 135388096222989301032867857)
            ·
              refine ⟨101541072167241975774650893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135388096222989301032867857 101541072167241975774650893)
              ·
                refine ⟨38077902062715740915494085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101541072167241975774650893 38077902062715740915494085)
                ·
                  refine ⟨7139606636759201421655141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38077902062715740915494085 7139606636759201421655141)
                  ·
                    refine ⟨1338676244392350266560339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139606636759201421655141 1338676244392350266560339)
                    ·
                      rfl

theorem cell23_7821188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7821188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821188 prefixEnd_7821188 := by exact prefixLift 7821188
  have htrace : WordTrace (prefixWord ++ tailWord_7821188) baseStart_7821188 baseEnd_7821188 := by
    simpa [prefixWord, tailWord_7821188, baseEnd_7821188] using wordTrace_append hprefix tailTrace_7821188
  have hstable : (prefixWord ++ tailWord_7821188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821188).length < 2 ^ (prefixWord ++ tailWord_7821188).sum := by decide
  have hdescent : baseEnd_7821188 < baseStart_7821188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821195 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 3, 2, 2]
def baseStart_7821195 : Nat := 118140960795 + 7821195 * 2 ^ 59
def prefixEnd_7821195 : Nat := 4983230072969 + 3 ^ 40 * 7821195 * 2
def baseEnd_7821195 : Nat := 4016032327541632272293485

theorem tailTrace_7821195 : CollatzResearch.WordTrace tailWord_7821195 prefixEnd_7821195 4016032327541632272293485 := by
  unfold tailWord_7821195
  simp only [CollatzResearch.WordTrace]
  refine ⟨285262416900153743606321039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190174944600102495737547359 285262416900153743606321039)
  ·
    refine ⟨427893625350230615409481559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285262416900153743606321039 427893625350230615409481559)
    ·
      refine ⟨641840438025345923114222339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427893625350230615409481559 641840438025345923114222339)
      ·
        refine ⟨962760657038018884671333509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641840438025345923114222339 962760657038018884671333509)
        ·
          refine ⟨180517623194628540875875033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 962760657038018884671333509 180517623194628540875875033)
          ·
            refine ⟨135388217395971405656906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180517623194628540875875033 135388217395971405656906275)
            ·
              refine ⟨203082326093957108485359413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135388217395971405656906275 203082326093957108485359413)
              ·
                refine ⟨19038968071308478920502445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203082326093957108485359413 19038968071308478920502445)
                ·
                  refine ⟨7139613026740679595188417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19038968071308478920502445 7139613026740679595188417)
                  ·
                    refine ⟨5354709770055509696391313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139613026740679595188417 5354709770055509696391313)
                    ·
                      refine ⟨4016032327541632272293485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354709770055509696391313 4016032327541632272293485)
                      ·
                        rfl

theorem cell23_7821195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2, 2].length) (baseStart_7821195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821195 prefixEnd_7821195 := by exact prefixLift 7821195
  have htrace : WordTrace (prefixWord ++ tailWord_7821195) baseStart_7821195 baseEnd_7821195 := by
    simpa [prefixWord, tailWord_7821195, baseEnd_7821195] using wordTrace_append hprefix tailTrace_7821195
  have hstable : (prefixWord ++ tailWord_7821195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821195).length < 2 ^ (prefixWord ++ tailWord_7821195).sum := by decide
  have hdescent : baseEnd_7821195 < baseStart_7821195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821201 : List Nat := [1, 2, 2, 1, 1, 1, 7, 8]
def baseStart_7821201 : Nat := 118140960795 + 7821201 * 2 ^ 59
def prefixEnd_7821201 : Nat := 4983230072969 + 3 ^ 40 * 7821201 * 2
def baseEnd_7821201 : Nat := 148742052163909601808091

theorem tailTrace_7821201 : CollatzResearch.WordTrace tailWord_7821201 prefixEnd_7821201 148742052163909601808091 := by
  unfold tailWord_7821201
  simp only [CollatzResearch.WordTrace]
  refine ⟨285262635738132006631039457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190175090492088004420692971 285262635738132006631039457)
  ·
    refine ⟨213946976803599004973279593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285262635738132006631039457 213946976803599004973279593)
    ·
      refine ⟨160460232602699253729959695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213946976803599004973279593 160460232602699253729959695)
      ·
        refine ⟨240690348904048880594939543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160460232602699253729959695 240690348904048880594939543)
        ·
          refine ⟨361035523356073320892409315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240690348904048880594939543 361035523356073320892409315)
          ·
            refine ⟨541553285034109981338613973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361035523356073320892409315 541553285034109981338613973)
            ·
              refine ⟨12692655117986952687623765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 541553285034109981338613973 12692655117986952687623765)
              ·
                refine ⟨148742052163909601808091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12692655117986952687623765 148742052163909601808091)
                ·
                  rfl

theorem cell23_7821201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 8].length) (baseStart_7821201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821201 prefixEnd_7821201 := by exact prefixLift 7821201
  have htrace : WordTrace (prefixWord ++ tailWord_7821201) baseStart_7821201 baseEnd_7821201 := by
    simpa [prefixWord, tailWord_7821201, baseEnd_7821201] using wordTrace_append hprefix tailTrace_7821201
  have hstable : (prefixWord ++ tailWord_7821201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821201).length < 2 ^ (prefixWord ++ tailWord_7821201).sum := by decide
  have hdescent : baseEnd_7821201 < baseStart_7821201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821206 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7821206 : Nat := 118140960795 + 7821206 * 2 ^ 59
def prefixEnd_7821206 : Nat := 4983230072969 + 3 ^ 40 * 7821206 * 2
def baseEnd_7821206 : Nat := 4016037975828831729255935

theorem tailTrace_7821206 : CollatzResearch.WordTrace tailWord_7821206 prefixEnd_7821206 4016037975828831729255935 := by
  unfold tailWord_7821206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828926131444618280310717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190175212068742594989980981 17828926131444618280310717)
  ·
    refine ⟨6685847299291731855116519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17828926131444618280310717 6685847299291731855116519)
    ·
      refine ⟨10028770948937597782674779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6685847299291731855116519 10028770948937597782674779)
      ·
        refine ⟨15043156423406396674012169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10028770948937597782674779 15043156423406396674012169)
        ·
          refine ⟨11282367317554797505509127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15043156423406396674012169 11282367317554797505509127)
          ·
            refine ⟨16923550976332196258263691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282367317554797505509127 16923550976332196258263691)
            ·
              refine ⟨25385326464498294387395537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923550976332196258263691 25385326464498294387395537)
              ·
                refine ⟨19038994848373720790546653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25385326464498294387395537 19038994848373720790546653)
                ·
                  refine ⟨7139623068140145296454995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19038994848373720790546653 7139623068140145296454995)
                  ·
                    refine ⟨10709434602210217944682493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7139623068140145296454995 10709434602210217944682493)
                    ·
                      refine ⟨4016037975828831729255935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10709434602210217944682493 4016037975828831729255935)
                      ·
                        rfl

theorem cell23_7821206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7821206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821206 prefixEnd_7821206 := by exact prefixLift 7821206
  have htrace : WordTrace (prefixWord ++ tailWord_7821206) baseStart_7821206 baseEnd_7821206 := by
    simpa [prefixWord, tailWord_7821206, baseEnd_7821206] using wordTrace_append hprefix tailTrace_7821206
  have hstable : (prefixWord ++ tailWord_7821206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821206).length < 2 ^ (prefixWord ++ tailWord_7821206).sum := by decide
  have hdescent : baseEnd_7821206 < baseStart_7821206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821212 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7821212 : Nat := 118140960795 + 7821212 * 2 ^ 59
def prefixEnd_7821212 : Nat := 4983230072969 + 3 ^ 40 * 7821212 * 2
def baseEnd_7821212 : Nat := 4016041056712758705780907

theorem tailTrace_7821212 : CollatzResearch.WordTrace tailWord_7821212 prefixEnd_7821212 4016041056712758705780907 := by
  unfold tailWord_7821212
  simp only [CollatzResearch.WordTrace]
  refine ⟨142631518470546077754844945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190175357960728103673126593 142631518470546077754844945)
  ·
    refine ⟨106973638852909558316133709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142631518470546077754844945 106973638852909558316133709)
    ·
      refine ⟨40115114569841084368550141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106973638852909558316133709 40115114569841084368550141)
      ·
        refine ⟨15043167963690406638206303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40115114569841084368550141 15043167963690406638206303)
        ·
          refine ⟨22564751945535609957309455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15043167963690406638206303 22564751945535609957309455)
          ·
            refine ⟨33847127918303414935964183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22564751945535609957309455 33847127918303414935964183)
            ·
              refine ⟨50770691877455122403946275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33847127918303414935964183 50770691877455122403946275)
              ·
                refine ⟨76156037816182683605919413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50770691877455122403946275 76156037816182683605919413)
                ·
                  refine ⟨7139628545267126588054945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76156037816182683605919413 7139628545267126588054945)
                  ·
                    refine ⟨5354721408950344941041209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139628545267126588054945 5354721408950344941041209)
                    ·
                      refine ⟨4016041056712758705780907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354721408950344941041209 4016041056712758705780907)
                      ·
                        rfl

theorem cell23_7821212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7821212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821212 prefixEnd_7821212 := by exact prefixLift 7821212
  have htrace : WordTrace (prefixWord ++ tailWord_7821212) baseStart_7821212 baseEnd_7821212 := by
    simpa [prefixWord, tailWord_7821212, baseEnd_7821212] using wordTrace_append hprefix tailTrace_7821212
  have hstable : (prefixWord ++ tailWord_7821212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821212).length < 2 ^ (prefixWord ++ tailWord_7821212).sum := by decide
  have hdescent : baseEnd_7821212 < baseStart_7821212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821272 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_7821272 : Nat := 118140960795 + 7821272 * 2 ^ 59
def prefixEnd_7821272 : Nat := 4983230072969 + 3 ^ 40 * 7821272 * 2
def baseEnd_7821272 : Nat := 4016071865552028471030631

theorem tailTrace_7821272 : CollatzResearch.WordTrace tailWord_7821272 prefixEnd_7821272 4016071865552028471030631 := by
  unfold tailWord_7821272
  simp only [CollatzResearch.WordTrace]
  refine ⟨142632612660437392878437035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190176816880583190504582713 142632612660437392878437035)
  ·
    refine ⟨213948918990656089317655553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142632612660437392878437035 213948918990656089317655553)
    ·
      refine ⟨160461689242992066988241665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213948918990656089317655553 160461689242992066988241665)
      ·
        refine ⟨120346266932244050241181249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160461689242992066988241665 120346266932244050241181249)
        ·
          refine ⟨90259700199183037680885937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120346266932244050241181249 90259700199183037680885937)
          ·
            refine ⟨67694775149387278260664453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90259700199183037680885937 67694775149387278260664453)
            ·
              refine ⟨12692770340510114673874585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67694775149387278260664453 12692770340510114673874585)
              ·
                refine ⟨9519577755382586005405939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12692770340510114673874585 9519577755382586005405939)
                ·
                  refine ⟨14279366633073879008108909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519577755382586005405939 14279366633073879008108909)
                  ·
                    refine ⟨5354762487402704628040841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14279366633073879008108909 5354762487402704628040841)
                    ·
                      refine ⟨4016071865552028471030631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354762487402704628040841 4016071865552028471030631)
                      ·
                        rfl

theorem cell23_7821272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_7821272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821272 prefixEnd_7821272 := by exact prefixLift 7821272
  have htrace : WordTrace (prefixWord ++ tailWord_7821272) baseStart_7821272 baseEnd_7821272 := by
    simpa [prefixWord, tailWord_7821272, baseEnd_7821272] using wordTrace_append hprefix tailTrace_7821272
  have hstable : (prefixWord ++ tailWord_7821272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821272).length < 2 ^ (prefixWord ++ tailWord_7821272).sum := by decide
  have hdescent : baseEnd_7821272 < baseStart_7821272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7821288 : Nat := 118140960795 + 7821288 * 2 ^ 59
def prefixEnd_7821288 : Nat := 4983230072969 + 3 ^ 40 * 7821288 * 2
def baseEnd_7821288 : Nat := 4016080081242500408430557

theorem tailTrace_7821288 : CollatzResearch.WordTrace tailWord_7821288 prefixEnd_7821288 4016080081242500408430557 := by
  unfold tailWord_7821288
  simp only [CollatzResearch.WordTrace]
  refine ⟨142632904444408410244728259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190177205925877880326304345 142632904444408410244728259)
  ·
    refine ⟨213949356666612615367092389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142632904444408410244728259 213949356666612615367092389)
    ·
      refine ⟨40115504374989865381329823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213949356666612615367092389 40115504374989865381329823)
      ·
        refine ⟨60173256562484798071994735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40115504374989865381329823 60173256562484798071994735)
        ·
          refine ⟨90259884843727197107992103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60173256562484798071994735 90259884843727197107992103)
          ·
            refine ⟨135389827265590795661988155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90259884843727197107992103 135389827265590795661988155)
            ·
              refine ⟨203084740898386193492982233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135389827265590795661988155 203084740898386193492982233)
              ·
                refine ⟨152313555673789645119736675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203084740898386193492982233 152313555673789645119736675)
                ·
                  refine ⟨228470333510684467679605013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152313555673789645119736675 228470333510684467679605013)
                  ·
                    refine ⟨10709546883313334422481485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228470333510684467679605013 10709546883313334422481485)
                    ·
                      refine ⟨4016080081242500408430557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10709546883313334422481485 4016080081242500408430557)
                      ·
                        rfl

theorem cell23_7821288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7821288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821288 prefixEnd_7821288 := by exact prefixLift 7821288
  have htrace : WordTrace (prefixWord ++ tailWord_7821288) baseStart_7821288 baseEnd_7821288 := by
    simpa [prefixWord, tailWord_7821288, baseEnd_7821288] using wordTrace_append hprefix tailTrace_7821288
  have hstable : (prefixWord ++ tailWord_7821288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821288).length < 2 ^ (prefixWord ++ tailWord_7821288).sum := by decide
  have hdescent : baseEnd_7821288 < baseStart_7821288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821291 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 9]
def baseStart_7821291 : Nat := 118140960795 + 7821291 * 2 ^ 59
def prefixEnd_7821291 : Nat := 4983230072969 + 3 ^ 40 * 7821291 * 2
def baseEnd_7821291 : Nat := 446231291298273766299227

theorem tailTrace_7821291 : CollatzResearch.WordTrace tailWord_7821291 prefixEnd_7821291 446231291298273766299227 := by
  unfold tailWord_7821291
  simp only [CollatzResearch.WordTrace]
  refine ⟨285265918307805952001815727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190177278871870634667877151 285265918307805952001815727)
  ·
    refine ⟨427898877461708928002723591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285265918307805952001815727 427898877461708928002723591)
    ·
      refine ⟨641848316192563392004085387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427898877461708928002723591 641848316192563392004085387)
      ·
        refine ⟨962772474288845088006128081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641848316192563392004085387 962772474288845088006128081)
        ·
          refine ⟨722079355716633816004596061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962772474288845088006128081 722079355716633816004596061)
          ·
            refine ⟨270779758393737681001723523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722079355716633816004596061 270779758393737681001723523)
            ·
              refine ⟨406169637590606521502585285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270779758393737681001723523 406169637590606521502585285)
              ·
                refine ⟨76156807048238722781734741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406169637590606521502585285 76156807048238722781734741)
                ·
                  refine ⟨446231291298273766299227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76156807048238722781734741 446231291298273766299227)
                  ·
                    rfl

theorem cell23_7821291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_7821291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821291 prefixEnd_7821291 := by exact prefixLift 7821291
  have htrace : WordTrace (prefixWord ++ tailWord_7821291) baseStart_7821291 baseEnd_7821291 := by
    simpa [prefixWord, tailWord_7821291, baseEnd_7821291] using wordTrace_append hprefix tailTrace_7821291
  have hstable : (prefixWord ++ tailWord_7821291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821291).length < 2 ^ (prefixWord ++ tailWord_7821291).sum := by decide
  have hdescent : baseEnd_7821291 < baseStart_7821291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821319 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7821319 : Nat := 118140960795 + 7821319 * 2 ^ 59
def prefixEnd_7821319 : Nat := 4983230072969 + 3 ^ 40 * 7821319 * 2
def baseEnd_7821319 : Nat := 4016095999142789787142915

theorem tailTrace_7821319 : CollatzResearch.WordTrace tailWord_7821319 prefixEnd_7821319 4016095999142789787142915 := by
  unfold tailWord_7821319
  simp only [CollatzResearch.WordTrace]
  refine ⟨285266939551704512783835011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190177959701136341855890007 285266939551704512783835011)
  ·
    refine ⟨427900409327556769175752517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285266939551704512783835011 427900409327556769175752517)
    ·
      refine ⟨80231326748916894220453597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427900409327556769175752517 80231326748916894220453597)
      ·
        refine ⟨30086747530843835332670099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80231326748916894220453597 30086747530843835332670099)
        ·
          refine ⟨45130121296265752999005149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30086747530843835332670099 45130121296265752999005149)
          ·
            refine ⟨16923795486099657374626931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45130121296265752999005149 16923795486099657374626931)
            ·
              refine ⟨25385693229149486061940397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923795486099657374626931 25385693229149486061940397)
              ·
                refine ⟨9519634960931057273227649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25385693229149486061940397 9519634960931057273227649)
                ·
                  refine ⟨7139726220698292954920737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9519634960931057273227649 7139726220698292954920737)
                  ·
                    refine ⟨5354794665523719716190553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139726220698292954920737 5354794665523719716190553)
                    ·
                      refine ⟨4016095999142789787142915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354794665523719716190553 4016095999142789787142915)
                      ·
                        rfl

theorem cell23_7821319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7821319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821319 prefixEnd_7821319 := by exact prefixLift 7821319
  have htrace : WordTrace (prefixWord ++ tailWord_7821319) baseStart_7821319 baseEnd_7821319 := by
    simpa [prefixWord, tailWord_7821319, baseEnd_7821319] using wordTrace_append hprefix tailTrace_7821319
  have hstable : (prefixWord ++ tailWord_7821319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821319).length < 2 ^ (prefixWord ++ tailWord_7821319).sum := by decide
  have hdescent : baseEnd_7821319 < baseStart_7821319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821375 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 6, 2]
def baseStart_7821375 : Nat := 118140960795 + 7821375 * 2 ^ 59
def prefixEnd_7821375 : Nat := 4983230072969 + 3 ^ 40 * 7821375 * 2
def baseEnd_7821375 : Nat := 4016124754059441568042657

theorem tailTrace_7821375 : CollatzResearch.WordTrace tailWord_7821375 prefixEnd_7821375 4016124754059441568042657 := by
  unfold tailWord_7821375
  simp only [CollatzResearch.WordTrace]
  refine ⟨285268982039501634347873579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190179321359667756231915719 285268982039501634347873579)
  ·
    refine ⟨427903473059252451521810369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285268982039501634347873579 427903473059252451521810369)
    ·
      refine ⟨320927604794439338641357777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427903473059252451521810369 320927604794439338641357777)
      ·
        refine ⟨240695703595829503981018333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320927604794439338641357777 240695703595829503981018333)
        ·
          refine ⟨90260888848436063992881875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240695703595829503981018333 90260888848436063992881875)
          ·
            refine ⟨135391333272654095989322813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90260888848436063992881875 135391333272654095989322813)
            ·
              refine ⟨50771749977245285995996055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135391333272654095989322813 50771749977245285995996055)
              ·
                refine ⟨76157624965867928993994083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50771749977245285995996055 76157624965867928993994083)
                ·
                  refine ⟨114236437448801893490991125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76157624965867928993994083 114236437448801893490991125)
                  ·
                    refine ⟨5354833005412588757390209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114236437448801893490991125 5354833005412588757390209)
                    ·
                      refine ⟨4016124754059441568042657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354833005412588757390209 4016124754059441568042657)
                      ·
                        rfl

theorem cell23_7821375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_7821375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821375 prefixEnd_7821375 := by exact prefixLift 7821375
  have htrace : WordTrace (prefixWord ++ tailWord_7821375) baseStart_7821375 baseEnd_7821375 := by
    simpa [prefixWord, tailWord_7821375, baseEnd_7821375] using wordTrace_append hprefix tailTrace_7821375
  have hstable : (prefixWord ++ tailWord_7821375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821375).length < 2 ^ (prefixWord ++ tailWord_7821375).sum := by decide
  have hdescent : baseEnd_7821375 < baseStart_7821375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821385 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_7821385 : Nat := 118140960795 + 7821385 * 2 ^ 59
def prefixEnd_7821385 : Nat := 4983230072969 + 3 ^ 40 * 7821385 * 2
def baseEnd_7821385 : Nat := 1338709962955328842972537

theorem tailTrace_7821385 : CollatzResearch.WordTrace tailWord_7821385 prefixEnd_7821385 1338709962955328842972537 := by
  unfold tailWord_7821385
  simp only [CollatzResearch.WordTrace]
  refine ⟨285269346769465406055737609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190179564512976937370491739 285269346769465406055737609)
  ·
    refine ⟨213952010077099054541803207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285269346769465406055737609 213952010077099054541803207)
    ·
      refine ⟨320928015115648581812704811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213952010077099054541803207 320928015115648581812704811)
      ·
        refine ⟨481392022673472872719057217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320928015115648581812704811 481392022673472872719057217)
        ·
          refine ⟨361044017005104654539292913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481392022673472872719057217 361044017005104654539292913)
          ·
            refine ⟨270783012753828490904469685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361044017005104654539292913 270783012753828490904469685)
            ·
              refine ⟨25385907445671421022294033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270783012753828490904469685 25385907445671421022294033)
              ·
                refine ⟨19039430584253565766720525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25385907445671421022294033 19039430584253565766720525)
                ·
                  refine ⟨7139786469095087162520197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19039430584253565766720525 7139786469095087162520197)
                  ·
                    refine ⟨1338709962955328842972537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139786469095087162520197 1338709962955328842972537)
                    ·
                      rfl

theorem cell23_7821385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_7821385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821385 prefixEnd_7821385 := by exact prefixLift 7821385
  have htrace : WordTrace (prefixWord ++ tailWord_7821385) baseStart_7821385 baseEnd_7821385 := by
    simpa [prefixWord, tailWord_7821385, baseEnd_7821385] using wordTrace_append hprefix tailTrace_7821385
  have hstable : (prefixWord ++ tailWord_7821385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821385).length < 2 ^ (prefixWord ++ tailWord_7821385).sum := by decide
  have hdescent : baseEnd_7821385 < baseStart_7821385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821469 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7821469 : Nat := 118140960795 + 7821469 * 2 ^ 59
def prefixEnd_7821469 : Nat := 4983230072969 + 3 ^ 40 * 7821469 * 2
def baseEnd_7821469 : Nat := 4016173021240964200267225

theorem tailTrace_7821469 : CollatzResearch.WordTrace tailWord_7821469 prefixEnd_7821469 4016173021240964200267225 := by
  unfold tailWord_7821469
  simp only [CollatzResearch.WordTrace]
  refine ⟨285272410501161088401795461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190181607000774058934530307 285272410501161088401795461)
  ·
    refine ⟨53488576968967704075336649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285272410501161088401795461 53488576968967704075336649)
    ·
      refine ⟨40116432726725778056502487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53488576968967704075336649 40116432726725778056502487)
      ·
        refine ⟨60174649090088667084753731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40116432726725778056502487 60174649090088667084753731)
        ·
          refine ⟨90261973635133000627130597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60174649090088667084753731 90261973635133000627130597)
          ·
            refine ⟨16924120056587437617586987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90261973635133000627130597 16924120056587437617586987)
            ·
              refine ⟨25386180084881156426380481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16924120056587437617586987 25386180084881156426380481)
              ·
                refine ⟨19039635063660867319785361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25386180084881156426380481 19039635063660867319785361)
                ·
                  refine ⟨14279726297745650489839021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19039635063660867319785361 14279726297745650489839021)
                  ·
                    refine ⟨5354897361654618933689633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14279726297745650489839021 5354897361654618933689633)
                    ·
                      refine ⟨4016173021240964200267225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354897361654618933689633 4016173021240964200267225)
                      ·
                        rfl

theorem cell23_7821469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7821469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821469 prefixEnd_7821469 := by exact prefixLift 7821469
  have htrace : WordTrace (prefixWord ++ tailWord_7821469) baseStart_7821469 baseEnd_7821469 := by
    simpa [prefixWord, tailWord_7821469, baseEnd_7821469] using wordTrace_append hprefix tailTrace_7821469
  have hstable : (prefixWord ++ tailWord_7821469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821469).length < 2 ^ (prefixWord ++ tailWord_7821469).sum := by decide
  have hdescent : baseEnd_7821469 < baseStart_7821469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821476 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_7821476 : Nat := 118140960795 + 7821476 * 2 ^ 59
def prefixEnd_7821476 : Nat := 4983230072969 + 3 ^ 40 * 7821476 * 2
def baseEnd_7821476 : Nat := 4016176615605545672879693

theorem tailTrace_7821476 : CollatzResearch.WordTrace tailWord_7821476 prefixEnd_7821476 4016176615605545672879693 := by
  unfold tailWord_7821476
  simp only [CollatzResearch.WordTrace]
  refine ⟨142636332906067864298650141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190181777208090485731533521 142636332906067864298650141)
  ·
    refine ⟨53488624839775449111993803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142636332906067864298650141 53488624839775449111993803)
    ·
      refine ⟨80232937259663173667990705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53488624839775449111993803 80232937259663173667990705)
      ·
        refine ⟨60174702944747380250993029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80232937259663173667990705 60174702944747380250993029)
        ·
          refine ⟨11282756802140133797061193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60174702944747380250993029 11282756802140133797061193)
          ·
            refine ⟨8462067601605100347795895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11282756802140133797061193 8462067601605100347795895)
            ·
              refine ⟨12693101402407650521693843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462067601605100347795895 12693101402407650521693843)
              ·
                refine ⟨19039652103611475782540765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693101402407650521693843 19039652103611475782540765)
                ·
                  refine ⟨7139869538854303418452787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19039652103611475782540765 7139869538854303418452787)
                  ·
                    refine ⟨10709804308281455127679181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7139869538854303418452787 10709804308281455127679181)
                    ·
                      refine ⟨4016176615605545672879693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10709804308281455127679181 4016176615605545672879693)
                      ·
                        rfl

theorem cell23_7821476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_7821476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821476 prefixEnd_7821476 := by exact prefixLift 7821476
  have htrace : WordTrace (prefixWord ++ tailWord_7821476) baseStart_7821476 baseEnd_7821476 := by
    simpa [prefixWord, tailWord_7821476, baseEnd_7821476] using wordTrace_append hprefix tailTrace_7821476
  have hstable : (prefixWord ++ tailWord_7821476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821476).length < 2 ^ (prefixWord ++ tailWord_7821476).sum := by decide
  have hdescent : baseEnd_7821476 < baseStart_7821476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821495 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_7821495 : Nat := 118140960795 + 7821495 * 2 ^ 59
def prefixEnd_7821495 : Nat := 4983230072969 + 3 ^ 40 * 7821495 * 2
def baseEnd_7821495 : Nat := 4016186371737981098542105

theorem tailTrace_7821495 : CollatzResearch.WordTrace tailWord_7821495 prefixEnd_7821495 4016186371737981098542105 := by
  unfold tailWord_7821495
  simp only [CollatzResearch.WordTrace]
  refine ⟨285273358799066894842241939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190182239199377929894827959 285273358799066894842241939)
  ·
    refine ⟨427910038198600342263362909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285273358799066894842241939 427910038198600342263362909)
    ·
      refine ⟨160466264324475128348761091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427910038198600342263362909 160466264324475128348761091)
      ·
        refine ⟨240699396486712692523141637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160466264324475128348761091 240699396486712692523141637)
        ·
          refine ⟨45131136841258629848089057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240699396486712692523141637 45131136841258629848089057)
          ·
            refine ⟨33848352630943972386066793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45131136841258629848089057 33848352630943972386066793)
            ·
              refine ⟨25386264473207979289550095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33848352630943972386066793 25386264473207979289550095)
              ·
                refine ⟨38079396709811968934325143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25386264473207979289550095 38079396709811968934325143)
                ·
                  refine ⟨57119095064717953401487715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38079396709811968934325143 57119095064717953401487715)
                  ·
                    refine ⟨85678642597076930102231573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57119095064717953401487715 85678642597076930102231573)
                    ·
                      refine ⟨4016186371737981098542105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85678642597076930102231573 4016186371737981098542105)
                      ·
                        rfl

theorem cell23_7821495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_7821495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821495 prefixEnd_7821495 := by exact prefixLift 7821495
  have htrace : WordTrace (prefixWord ++ tailWord_7821495) baseStart_7821495 baseEnd_7821495 := by
    simpa [prefixWord, tailWord_7821495, baseEnd_7821495] using wordTrace_append hprefix tailTrace_7821495
  have hstable : (prefixWord ++ tailWord_7821495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821495).length < 2 ^ (prefixWord ++ tailWord_7821495).sum := by decide
  have hdescent : baseEnd_7821495 < baseStart_7821495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821519 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 1, 2, 3]
def baseStart_7821519 : Nat := 118140960795 + 7821519 * 2 ^ 59
def prefixEnd_7821519 : Nat := 4983230072969 + 3 ^ 40 * 7821519 * 2
def baseEnd_7821519 : Nat := 4016198695273689004641995

theorem tailTrace_7821519 : CollatzResearch.WordTrace tailWord_7821519 prefixEnd_7821519 4016198695273689004641995 := by
  unfold tailWord_7821519
  simp only [CollatzResearch.WordTrace]
  refine ⟨285274234150979946941115611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190182822767319964627410407 285274234150979946941115611)
  ·
    refine ⟨427911351226469920411673417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285274234150979946941115611 427911351226469920411673417)
    ·
      refine ⟨320933513419852440308755063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427911351226469920411673417 320933513419852440308755063)
      ·
        refine ⟨481400270129778660463132595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320933513419852440308755063 481400270129778660463132595)
        ·
          refine ⟨722100405194667990694698893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481400270129778660463132595 722100405194667990694698893)
          ·
            refine ⟨270787651948000496510512085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722100405194667990694698893 270787651948000496510512085)
            ·
              refine ⟨6346585592531261636965127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270787651948000496510512085 6346585592531261636965127)
              ·
                refine ⟨9519878388796892455447691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346585592531261636965127 9519878388796892455447691)
                ·
                  refine ⟨14279817583195338683171537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519878388796892455447691 14279817583195338683171537)
                  ·
                    refine ⟨10709863187396504012378653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14279817583195338683171537 10709863187396504012378653)
                    ·
                      refine ⟨4016198695273689004641995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10709863187396504012378653 4016198695273689004641995)
                      ·
                        rfl

theorem cell23_7821519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 2, 3].length) (baseStart_7821519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821519 prefixEnd_7821519 := by exact prefixLift 7821519
  have htrace : WordTrace (prefixWord ++ tailWord_7821519) baseStart_7821519 baseEnd_7821519 := by
    simpa [prefixWord, tailWord_7821519, baseEnd_7821519] using wordTrace_append hprefix tailTrace_7821519
  have hstable : (prefixWord ++ tailWord_7821519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821519).length < 2 ^ (prefixWord ++ tailWord_7821519).sum := by decide
  have hdescent : baseEnd_7821519 < baseStart_7821519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821526 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7821526 : Nat := 118140960795 + 7821526 * 2 ^ 59
def prefixEnd_7821526 : Nat := 4983230072969 + 3 ^ 40 * 7821526 * 2
def baseEnd_7821526 : Nat := 1338734096546090159084821

theorem tailTrace_7821526 : CollatzResearch.WordTrace tailWord_7821526 prefixEnd_7821526 1338734096546090159084821 := by
  unfold tailWord_7821526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829655591372161696038777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190182992974636391424413621 17829655591372161696038777)
  ·
    refine ⟨13372241693529121272029083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17829655591372161696038777 13372241693529121272029083)
    ·
      refine ⟨20058362540293681908043625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13372241693529121272029083 20058362540293681908043625)
      ·
        refine ⟨15043771905220261431032719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20058362540293681908043625 15043771905220261431032719)
        ·
          refine ⟨22565657857830392146549079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15043771905220261431032719 22565657857830392146549079)
          ·
            refine ⟨33848486786745588219823619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22565657857830392146549079 33848486786745588219823619)
            ·
              refine ⟨50772730180118382329735429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33848486786745588219823619 50772730180118382329735429)
              ·
                refine ⟨9519886908772196686825393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50772730180118382329735429 9519886908772196686825393)
                ·
                  refine ⟨7139915181579147515119045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9519886908772196686825393 7139915181579147515119045)
                  ·
                    refine ⟨1338734096546090159084821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139915181579147515119045 1338734096546090159084821)
                    ·
                      rfl

theorem cell23_7821526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7821526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821526 prefixEnd_7821526 := by exact prefixLift 7821526
  have htrace : WordTrace (prefixWord ++ tailWord_7821526) baseStart_7821526 baseEnd_7821526 := by
    simpa [prefixWord, tailWord_7821526, baseEnd_7821526] using wordTrace_append hprefix tailTrace_7821526
  have hstable : (prefixWord ++ tailWord_7821526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821526).length < 2 ^ (prefixWord ++ tailWord_7821526).sum := by decide
  have hdescent : baseEnd_7821526 < baseStart_7821526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821539 : List Nat := [1, 1, 1, 8, 1, 2, 1, 8]
def baseStart_7821539 : Nat := 118140960795 + 7821539 * 2 ^ 59
def prefixEnd_7821539 : Nat := 4983230072969 + 3 ^ 40 * 7821539 * 2
def baseEnd_7821539 : Nat := 148748480180991812088589

theorem tailTrace_7821539 : CollatzResearch.WordTrace tailWord_7821539 prefixEnd_7821539 148748480180991812088589 := by
  unfold tailWord_7821539
  simp only [CollatzResearch.WordTrace]
  refine ⟨285274963610907490356843671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190183309073938326904562447 285274963610907490356843671)
  ·
    refine ⟨427912445416361235535265507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285274963610907490356843671 427912445416361235535265507)
    ·
      refine ⟨641868668124541853302898261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427912445416361235535265507 641868668124541853302898261)
      ·
        refine ⟨7521898454584474843393339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 641868668124541853302898261 7521898454584474843393339)
        ·
          refine ⟨11282847681876712265090009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7521898454584474843393339 11282847681876712265090009)
          ·
            refine ⟨8462135761407534198817507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11282847681876712265090009 8462135761407534198817507)
            ·
              refine ⟨12693203642111301298226261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462135761407534198817507 12693203642111301298226261)
              ·
                refine ⟨148748480180991812088589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12693203642111301298226261 148748480180991812088589)
                ·
                  rfl

theorem cell23_7821539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 8].length) (baseStart_7821539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821539 prefixEnd_7821539 := by exact prefixLift 7821539
  have htrace : WordTrace (prefixWord ++ tailWord_7821539) baseStart_7821539 baseEnd_7821539 := by
    simpa [prefixWord, tailWord_7821539, baseEnd_7821539] using wordTrace_append hprefix tailTrace_7821539
  have hstable : (prefixWord ++ tailWord_7821539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821539).length < 2 ^ (prefixWord ++ tailWord_7821539).sum := by decide
  have hdescent : baseEnd_7821539 < baseStart_7821539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821555 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_7821555 : Nat := 118140960795 + 7821555 * 2 ^ 59
def prefixEnd_7821555 : Nat := 4983230072969 + 3 ^ 40 * 7821555 * 2
def baseEnd_7821555 : Nat := 4016217180577250863791829

theorem tailTrace_7821555 : CollatzResearch.WordTrace tailWord_7821555 prefixEnd_7821555 4016217180577250863791829 := by
  unfold tailWord_7821555
  simp only [CollatzResearch.WordTrace]
  refine ⟨285275547178849525089426119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190183698119233016726284079 285275547178849525089426119)
  ·
    refine ⟨427913320768274287634139179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285275547178849525089426119 427913320768274287634139179)
    ·
      refine ⟨641869981152411431451208769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427913320768274287634139179 641869981152411431451208769)
      ·
        refine ⟨481402485864308573588406577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641869981152411431451208769 481402485864308573588406577)
        ·
          refine ⟨361051864398231430191304933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481402485864308573588406577 361051864398231430191304933)
          ·
            refine ⟨67697224574668393160869675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361051864398231430191304933 67697224574668393160869675)
            ·
              refine ⟨101545836862002589741304513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67697224574668393160869675 101545836862002589741304513)
              ·
                refine ⟨76159377646501942305978385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101545836862002589741304513 76159377646501942305978385)
                ·
                  refine ⟨57119533234876456729483789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76159377646501942305978385 57119533234876456729483789)
                  ·
                    refine ⟨21419824963078671273556421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57119533234876456729483789 21419824963078671273556421)
                    ·
                      refine ⟨4016217180577250863791829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21419824963078671273556421 4016217180577250863791829)
                      ·
                        rfl

theorem cell23_7821555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_7821555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821555 prefixEnd_7821555 := by exact prefixLift 7821555
  have htrace : WordTrace (prefixWord ++ tailWord_7821555) baseStart_7821555 baseEnd_7821555 := by
    simpa [prefixWord, tailWord_7821555, baseEnd_7821555] using wordTrace_append hprefix tailTrace_7821555
  have hstable : (prefixWord ++ tailWord_7821555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821555).length < 2 ^ (prefixWord ++ tailWord_7821555).sum := by decide
  have hdescent : baseEnd_7821555 < baseStart_7821555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821576 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_7821576 : Nat := 118140960795 + 7821576 * 2 ^ 59
def prefixEnd_7821576 : Nat := 4983230072969 + 3 ^ 40 * 7821576 * 2
def baseEnd_7821576 : Nat := 4016227963670995281629233

theorem tailTrace_7821576 : CollatzResearch.WordTrace tailWord_7821576 prefixEnd_7821576 4016227963670995281629233 := by
  unfold tailWord_7821576
  simp only [CollatzResearch.WordTrace]
  refine ⟨142638156555886722837970291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190184208741182297117293721 142638156555886722837970291)
  ·
    refine ⟨213957234833830084256955437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142638156555886722837970291 213957234833830084256955437)
    ·
      refine ⟨80233963062686281596358289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213957234833830084256955437 80233963062686281596358289)
      ·
        refine ⟨60175472297014711197268717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80233963062686281596358289 60175472297014711197268717)
        ·
          refine ⟨22565802111380516698975769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60175472297014711197268717 22565802111380516698975769)
          ·
            refine ⟨16924351583535387524231827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22565802111380516698975769 16924351583535387524231827)
            ·
              refine ⟨25386527375303081286347741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16924351583535387524231827 25386527375303081286347741)
              ·
                refine ⟨9519947765738655482380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25386527375303081286347741 9519947765738655482380403)
                ·
                  refine ⟨14279921648607983223570605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519947765738655482380403 14279921648607983223570605)
                  ·
                    refine ⟨5354970618227993708838977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14279921648607983223570605 5354970618227993708838977)
                    ·
                      refine ⟨4016227963670995281629233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5354970618227993708838977 4016227963670995281629233)
                      ·
                        rfl

theorem cell23_7821576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_7821576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821576 prefixEnd_7821576 := by exact prefixLift 7821576
  have htrace : WordTrace (prefixWord ++ tailWord_7821576) baseStart_7821576 baseEnd_7821576 := by
    simpa [prefixWord, tailWord_7821576, baseEnd_7821576] using wordTrace_append hprefix tailTrace_7821576
  have hstable : (prefixWord ++ tailWord_7821576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821576).length < 2 ^ (prefixWord ++ tailWord_7821576).sum := by decide
  have hdescent : baseEnd_7821576 < baseStart_7821576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821595 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 7]
def baseStart_7821595 : Nat := 118140960795 + 7821595 * 2 ^ 59
def prefixEnd_7821595 : Nat := 4983230072969 + 3 ^ 40 * 7821595 * 2
def baseEnd_7821595 : Nat := 446248635533714523032405

theorem tailTrace_7821595 : CollatzResearch.WordTrace tailWord_7821595 prefixEnd_7821595 446248635533714523032405 := by
  unfold tailWord_7821595
  simp only [CollatzResearch.WordTrace]
  refine ⟨285277006098704611920882239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190184670732469741280588159 285277006098704611920882239)
  ·
    refine ⟨427915509148056917881323359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285277006098704611920882239 427915509148056917881323359)
    ·
      refine ⟨641873263722085376821985039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427915509148056917881323359 641873263722085376821985039)
      ·
        refine ⟨962809895583128065232977559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641873263722085376821985039 962809895583128065232977559)
        ·
          refine ⟨1444214843374692097849466339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962809895583128065232977559 1444214843374692097849466339)
          ·
            refine ⟨2166322265062038146774199509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444214843374692097849466339 2166322265062038146774199509)
            ·
              refine ⟨50773178087391519065020301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2166322265062038146774199509 50773178087391519065020301)
              ·
                refine ⟨19039941782771819649382613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50773178087391519065020301 19039941782771819649382613)
                ·
                  refine ⟨446248635533714523032405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19039941782771819649382613 446248635533714523032405)
                  ·
                    rfl

theorem cell23_7821595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 7].length) (baseStart_7821595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821595 prefixEnd_7821595 := by exact prefixLift 7821595
  have htrace : WordTrace (prefixWord ++ tailWord_7821595) baseStart_7821595 baseEnd_7821595 := by
    simpa [prefixWord, tailWord_7821595, baseEnd_7821595] using wordTrace_append hprefix tailTrace_7821595
  have hstable : (prefixWord ++ tailWord_7821595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821595).length < 2 ^ (prefixWord ++ tailWord_7821595).sum := by decide
  have hdescent : baseEnd_7821595 < baseStart_7821595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821652 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_7821652 : Nat := 118140960795 + 7821652 * 2 ^ 59
def prefixEnd_7821652 : Nat := 4983230072969 + 3 ^ 40 * 7821652 * 2
def baseEnd_7821652 : Nat := 4016266988200736984278883

theorem tailTrace_7821652 : CollatzResearch.WordTrace tailWord_7821652 prefixEnd_7821652 4016266988200736984278883 := by
  unfold tailWord_7821652
  simp only [CollatzResearch.WordTrace]
  refine ⟨142639542529749055327853605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190186056706332073770471473 142639542529749055327853605)
  ·
    refine ⟨26744914224327947873972551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142639542529749055327853605 26744914224327947873972551)
    ·
      refine ⟨40117371336491921810958827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26744914224327947873972551 40117371336491921810958827)
      ·
        refine ⟨60176057004737882716438241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40117371336491921810958827 60176057004737882716438241)
        ·
          refine ⟨45132042753553412037328681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60176057004737882716438241 45132042753553412037328681)
          ·
            refine ⟨33849032065165059027996511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45132042753553412037328681 33849032065165059027996511)
            ·
              refine ⟨50773548097747588541994767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33849032065165059027996511 50773548097747588541994767)
              ·
                refine ⟨76160322146621382812992151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50773548097747588541994767 76160322146621382812992151)
                ·
                  refine ⟨114240483219932074219488227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76160322146621382812992151 114240483219932074219488227)
                  ·
                    refine ⟨171360724829898111329232341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114240483219932074219488227 171360724829898111329232341)
                    ·
                      refine ⟨4016266988200736984278883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171360724829898111329232341 4016266988200736984278883)
                      ·
                        rfl

theorem cell23_7821652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_7821652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821652 prefixEnd_7821652 := by exact prefixLift 7821652
  have htrace : WordTrace (prefixWord ++ tailWord_7821652) baseStart_7821652 baseEnd_7821652 := by
    simpa [prefixWord, tailWord_7821652, baseEnd_7821652] using wordTrace_append hprefix tailTrace_7821652
  have hstable : (prefixWord ++ tailWord_7821652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821652).length < 2 ^ (prefixWord ++ tailWord_7821652).sum := by decide
  have hdescent : baseEnd_7821652 < baseStart_7821652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821786 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_7821786 : Nat := 118140960795 + 7821786 * 2 ^ 59
def prefixEnd_7821786 : Nat := 4983230072969 + 3 ^ 40 * 7821786 * 2
def baseEnd_7821786 : Nat := 4016335794608439460003267

theorem tailTrace_7821786 : CollatzResearch.WordTrace tailWord_7821786 prefixEnd_7821786 4016335794608439460003267 := by
  unfold tailWord_7821786
  simp only [CollatzResearch.WordTrace]
  refine ⟨71320993110253162885271303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190189314960675101027390141 71320993110253162885271303)
  ·
    refine ⟨106981489665379744327906955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71320993110253162885271303 106981489665379744327906955)
    ·
      refine ⟨160472234498069616491860433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106981489665379744327906955 160472234498069616491860433)
      ·
        refine ⟨120354175873552212368895325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160472234498069616491860433 120354175873552212368895325)
        ·
          refine ⟨45132815952582079638335747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120354175873552212368895325 45132815952582079638335747)
          ·
            refine ⟨67699223928873119457503621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45132815952582079638335747 67699223928873119457503621)
            ·
              refine ⟨12693604486663709898281929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67699223928873119457503621 12693604486663709898281929)
              ·
                refine ⟨9520203364997782423711447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12693604486663709898281929 9520203364997782423711447)
                ·
                  refine ⟨14280305047496673635567171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520203364997782423711447 14280305047496673635567171)
                  ·
                    refine ⟨21420457571245010453350757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14280305047496673635567171 21420457571245010453350757)
                    ·
                      refine ⟨4016335794608439460003267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21420457571245010453350757 4016335794608439460003267)
                      ·
                        rfl

theorem cell23_7821786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_7821786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821786 prefixEnd_7821786 := by exact prefixLift 7821786
  have htrace : WordTrace (prefixWord ++ tailWord_7821786) baseStart_7821786 baseEnd_7821786 := by
    simpa [prefixWord, tailWord_7821786, baseEnd_7821786] using wordTrace_append hprefix tailTrace_7821786
  have hstable : (prefixWord ++ tailWord_7821786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821786).length < 2 ^ (prefixWord ++ tailWord_7821786).sum := by decide
  have hdescent : baseEnd_7821786 < baseStart_7821786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821789 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7821789 : Nat := 118140960795 + 7821789 * 2 ^ 59
def prefixEnd_7821789 : Nat := 4983230072969 + 3 ^ 40 * 7821789 * 2
def baseEnd_7821789 : Nat := 4016337335050402948265753

theorem tailTrace_7821789 : CollatzResearch.WordTrace tailWord_7821789 prefixEnd_7821789 4016337335050402948265753 := by
  unfold tailWord_7821789
  simp only [CollatzResearch.WordTrace]
  refine ⟨285284081860001783053444421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190189387906667855368962947 285284081860001783053444421)
  ·
    refine ⟨53490765348750334322520829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285284081860001783053444421 53490765348750334322520829)
    ·
      refine ⟨20059037005781375370945311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53490765348750334322520829 20059037005781375370945311)
      ·
        refine ⟨30088555508672063056417967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20059037005781375370945311 30088555508672063056417967)
        ·
          refine ⟨45132833263008094584626951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30088555508672063056417967 45132833263008094584626951)
          ·
            refine ⟨67699249894512141876940427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45132833263008094584626951 67699249894512141876940427)
            ·
              refine ⟨101548874841768212815410641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67699249894512141876940427 101548874841768212815410641)
              ·
                refine ⟨76161656131326159611557981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101548874841768212815410641 76161656131326159611557981)
                ·
                  refine ⟨28560621049247309854334243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76161656131326159611557981 28560621049247309854334243)
                  ·
                    refine ⟨42840931573870964781501365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28560621049247309854334243 42840931573870964781501365)
                    ·
                      refine ⟨4016337335050402948265753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42840931573870964781501365 4016337335050402948265753)
                      ·
                        rfl

theorem cell23_7821789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7821789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821789 prefixEnd_7821789 := by exact prefixLift 7821789
  have htrace : WordTrace (prefixWord ++ tailWord_7821789) baseStart_7821789 baseEnd_7821789 := by
    simpa [prefixWord, tailWord_7821789, baseEnd_7821789] using wordTrace_append hprefix tailTrace_7821789
  have hstable : (prefixWord ++ tailWord_7821789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821789).length < 2 ^ (prefixWord ++ tailWord_7821789).sum := by decide
  have hdescent : baseEnd_7821789 < baseStart_7821789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821792 : List Nat := [2, 1, 1, 3, 1, 1, 5, 9]
def baseStart_7821792 : Nat := 118140960795 + 7821792 * 2 ^ 59
def prefixEnd_7821792 : Nat := 4983230072969 + 3 ^ 40 * 7821792 * 2
def baseEnd_7821792 : Nat := 148753291684902460612157

theorem tailTrace_7821792 : CollatzResearch.WordTrace tailWord_7821792 prefixEnd_7821792 148753291684902460612157 := by
  unfold tailWord_7821792
  simp only [CollatzResearch.WordTrace]
  refine ⟨142642095639495457282901815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190189460852660609710535753 142642095639495457282901815)
  ·
    refine ⟨213963143459243185924352723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142642095639495457282901815 213963143459243185924352723)
    ·
      refine ⟨320944715188864778886529085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213963143459243185924352723 320944715188864778886529085)
      ·
        refine ⟨120354268195824292082448407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320944715188864778886529085 120354268195824292082448407)
        ·
          refine ⟨180531402293736438123672611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120354268195824292082448407 180531402293736438123672611)
          ·
            refine ⟨270797103440604657185508917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180531402293736438123672611 270797103440604657185508917)
            ·
              refine ⟨25387228447556686611141461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270797103440604657185508917 25387228447556686611141461)
              ·
                refine ⟨148753291684902460612157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25387228447556686611141461 148753291684902460612157)
                ·
                  rfl

theorem cell23_7821792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 9].length) (baseStart_7821792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821792 prefixEnd_7821792 := by exact prefixLift 7821792
  have htrace : WordTrace (prefixWord ++ tailWord_7821792) baseStart_7821792 baseEnd_7821792 := by
    simpa [prefixWord, tailWord_7821792, baseEnd_7821792] using wordTrace_append hprefix tailTrace_7821792
  have hstable : (prefixWord ++ tailWord_7821792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821792).length < 2 ^ (prefixWord ++ tailWord_7821792).sum := by decide
  have hdescent : baseEnd_7821792 < baseStart_7821792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821797 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7821797 : Nat := 118140960795 + 7821797 * 2 ^ 59
def prefixEnd_7821797 : Nat := 4983230072969 + 3 ^ 40 * 7821797 * 2
def baseEnd_7821797 : Nat := 4016341442895638916965717

theorem tailTrace_7821797 : CollatzResearch.WordTrace tailWord_7821797 prefixEnd_7821797 4016341442895638916965717 := by
  unfold tailWord_7821797
  simp only [CollatzResearch.WordTrace]
  refine ⟨285284373643972800419735645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190189582429315200279823763 285284373643972800419735645)
  ·
    refine ⟨106981640116489800157400867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285284373643972800419735645 106981640116489800157400867)
    ·
      refine ⟨160472460174734700236101301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106981640116489800157400867 160472460174734700236101301)
      ·
        refine ⟨15044293141381378147134497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160472460174734700236101301 15044293141381378147134497)
        ·
          refine ⟨11283219856036033610350873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15044293141381378147134497 11283219856036033610350873)
          ·
            refine ⟨8462414892027025207763155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283219856036033610350873 8462414892027025207763155)
            ·
              refine ⟨12693622338040537811644733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462414892027025207763155 12693622338040537811644733)
              ·
                refine ⟨4760108376765201679366775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12693622338040537811644733 4760108376765201679366775)
                ·
                  refine ⟨7140162565147802519050163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760108376765201679366775 7140162565147802519050163)
                  ·
                    refine ⟨10710243847721703778575245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140162565147802519050163 10710243847721703778575245)
                    ·
                      refine ⟨4016341442895638916965717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10710243847721703778575245 4016341442895638916965717)
                      ·
                        rfl

theorem cell23_7821797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7821797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821797 prefixEnd_7821797 := by exact prefixLift 7821797
  have htrace : WordTrace (prefixWord ++ tailWord_7821797) baseStart_7821797 baseEnd_7821797 := by
    simpa [prefixWord, tailWord_7821797, baseEnd_7821797] using wordTrace_append hprefix tailTrace_7821797
  have hstable : (prefixWord ++ tailWord_7821797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821797).length < 2 ^ (prefixWord ++ tailWord_7821797).sum := by decide
  have hdescent : baseEnd_7821797 < baseStart_7821797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821799 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7821799 : Nat := 118140960795 + 7821799 * 2 ^ 59
def prefixEnd_7821799 : Nat := 4983230072969 + 3 ^ 40 * 7821799 * 2
def baseEnd_7821799 : Nat := 4016342469856947909140707

theorem tailTrace_7821799 : CollatzResearch.WordTrace tailWord_7821799 prefixEnd_7821799 4016342469856947909140707 := by
  unfold tailWord_7821799
  simp only [CollatzResearch.WordTrace]
  refine ⟨285284446589965554761308451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190189631059977036507538967 285284446589965554761308451)
  ·
    refine ⟨427926669884948332141962677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285284446589965554761308451 427926669884948332141962677)
    ·
      refine ⟨40118125301713906138309001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427926669884948332141962677 40118125301713906138309001)
      ·
        refine ⟨30088593976285429603731751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40118125301713906138309001 30088593976285429603731751)
        ·
          refine ⟨45132890964428144405597627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30088593976285429603731751 45132890964428144405597627)
          ·
            refine ⟨67699336446642216608396441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45132890964428144405597627 67699336446642216608396441)
            ·
              refine ⟨50774502334981662456297331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67699336446642216608396441 50774502334981662456297331)
              ·
                refine ⟨76161753502472493684445997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50774502334981662456297331 76161753502472493684445997)
                ·
                  refine ⟨28560657563427185131667249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76161753502472493684445997 28560657563427185131667249)
                  ·
                    refine ⟨21420493172570388848750437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28560657563427185131667249 21420493172570388848750437)
                    ·
                      refine ⟨4016342469856947909140707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21420493172570388848750437 4016342469856947909140707)
                      ·
                        rfl

theorem cell23_7821799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7821799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821799 prefixEnd_7821799 := by exact prefixLift 7821799
  have htrace : WordTrace (prefixWord ++ tailWord_7821799) baseStart_7821799 baseEnd_7821799 := by
    simpa [prefixWord, tailWord_7821799, baseEnd_7821799] using wordTrace_append hprefix tailTrace_7821799
  have hstable : (prefixWord ++ tailWord_7821799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821799).length < 2 ^ (prefixWord ++ tailWord_7821799).sum := by decide
  have hdescent : baseEnd_7821799 < baseStart_7821799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821806 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_7821806 : Nat := 118140960795 + 7821806 * 2 ^ 59
def prefixEnd_7821806 : Nat := 4983230072969 + 3 ^ 40 * 7821806 * 2
def baseEnd_7821806 : Nat := 4016346064221529381753175

theorem tailTrace_7821806 : CollatzResearch.WordTrace tailWord_7821806 prefixEnd_7821806 4016346064221529381753175 := by
  unfold tailWord_7821806
  simp only [CollatzResearch.WordTrace]
  refine ⟨35660587737617524369601659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190189801267293463304542181 35660587737617524369601659)
  ·
    refine ⟨53490881606426286554402489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35660587737617524369601659 53490881606426286554402489)
    ·
      refine ⟨40118161204819714915801867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53490881606426286554402489 40118161204819714915801867)
      ·
        refine ⟨60177241807229572373702801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40118161204819714915801867 60177241807229572373702801)
        ·
          refine ⟨45132931355422179280277101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60177241807229572373702801 45132931355422179280277101)
          ·
            refine ⟨16924849258283317230103913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45132931355422179280277101 16924849258283317230103913)
            ·
              refine ⟨12693636943712487922577935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16924849258283317230103913 12693636943712487922577935)
              ·
                refine ⟨19040455415568731883866903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693636943712487922577935 19040455415568731883866903)
                ·
                  refine ⟨28560683123353097825800355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19040455415568731883866903 28560683123353097825800355)
                  ·
                    refine ⟨42841024685029646738700533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28560683123353097825800355 42841024685029646738700533)
                    ·
                      refine ⟨4016346064221529381753175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42841024685029646738700533 4016346064221529381753175)
                      ·
                        rfl

theorem cell23_7821806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_7821806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821806 prefixEnd_7821806 := by exact prefixLift 7821806
  have htrace : WordTrace (prefixWord ++ tailWord_7821806) baseStart_7821806 baseEnd_7821806 := by
    simpa [prefixWord, tailWord_7821806, baseEnd_7821806] using wordTrace_append hprefix tailTrace_7821806
  have hstable : (prefixWord ++ tailWord_7821806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821806).length < 2 ^ (prefixWord ++ tailWord_7821806).sum := by decide
  have hdescent : baseEnd_7821806 < baseStart_7821806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821837 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7821837 : Nat := 118140960795 + 7821837 * 2 ^ 59
def prefixEnd_7821837 : Nat := 4983230072969 + 3 ^ 40 * 7821837 * 2
def baseEnd_7821837 : Nat := 4016361982121818760465533

theorem tailTrace_7821837 : CollatzResearch.WordTrace tailWord_7821837 prefixEnd_7821837 4016361982121818760465533 := by
  unfold tailWord_7821837
  simp only [CollatzResearch.WordTrace]
  refine ⟨285285832563827887251191765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190190555042551924834127843 285285832563827887251191765)
  ·
    refine ⟨6686386700714716107449807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 285285832563827887251191765 6686386700714716107449807)
    ·
      refine ⟨10029580051072074161174711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686386700714716107449807 10029580051072074161174711)
      ·
        refine ⟨15044370076608111241762067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029580051072074161174711 15044370076608111241762067)
        ·
          refine ⟨22566555114912166862643101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15044370076608111241762067 22566555114912166862643101)
          ·
            refine ⟨8462458168092062573491163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22566555114912166862643101 8462458168092062573491163)
            ·
              refine ⟨12693687252138093860236745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462458168092062573491163 12693687252138093860236745)
              ·
                refine ⟨9520265439103570395177559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12693687252138093860236745 9520265439103570395177559)
                ·
                  refine ⟨14280398158655355592766339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520265439103570395177559 14280398158655355592766339)
                  ·
                    refine ⟨21420597237983033389149509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14280398158655355592766339 21420597237983033389149509)
                    ·
                      refine ⟨4016361982121818760465533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21420597237983033389149509 4016361982121818760465533)
                      ·
                        rfl

theorem cell23_7821837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7821837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821837 prefixEnd_7821837 := by exact prefixLift 7821837
  have htrace : WordTrace (prefixWord ++ tailWord_7821837) baseStart_7821837 baseEnd_7821837 := by
    simpa [prefixWord, tailWord_7821837, baseEnd_7821837] using wordTrace_append hprefix tailTrace_7821837
  have hstable : (prefixWord ++ tailWord_7821837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821837).length < 2 ^ (prefixWord ++ tailWord_7821837).sum := by decide
  have hdescent : baseEnd_7821837 < baseStart_7821837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821879 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_7821879 : Nat := 118140960795 + 7821879 * 2 ^ 59
def prefixEnd_7821879 : Nat := 4983230072969 + 3 ^ 40 * 7821879 * 2
def baseEnd_7821879 : Nat := 4016383548309307596140339

theorem tailTrace_7821879 : CollatzResearch.WordTrace tailWord_7821879 prefixEnd_7821879 4016383548309307596140339 := by
  unfold tailWord_7821879
  simp only [CollatzResearch.WordTrace]
  refine ⟨285287364429675728424220691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190191576286450485616147127 285287364429675728424220691)
  ·
    refine ⟨427931046644513592636331037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285287364429675728424220691 427931046644513592636331037)
    ·
      refine ⟨160474142491692597238624139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427931046644513592636331037 160474142491692597238624139)
      ·
        refine ⟨240711213737538895857936209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160474142491692597238624139 240711213737538895857936209)
        ·
          refine ⟨180533410303154171893452157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240711213737538895857936209 180533410303154171893452157)
          ·
            refine ⟨67700028863682814460044559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180533410303154171893452157 67700028863682814460044559)
            ·
              refine ⟨101550043295524221690066839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67700028863682814460044559 101550043295524221690066839)
              ·
                refine ⟨152325064943286332535100259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101550043295524221690066839 152325064943286332535100259)
                ·
                  refine ⟨228487597414929498802650389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152325064943286332535100259 228487597414929498802650389)
                  ·
                    refine ⟨10710356128824820256374237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228487597414929498802650389 10710356128824820256374237)
                    ·
                      refine ⟨4016383548309307596140339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10710356128824820256374237 4016383548309307596140339)
                      ·
                        rfl

theorem cell23_7821879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_7821879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821879 prefixEnd_7821879 := by exact prefixLift 7821879
  have htrace : WordTrace (prefixWord ++ tailWord_7821879) baseStart_7821879 baseEnd_7821879 := by
    simpa [prefixWord, tailWord_7821879, baseEnd_7821879] using wordTrace_append hprefix tailTrace_7821879
  have hstable : (prefixWord ++ tailWord_7821879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821879).length < 2 ^ (prefixWord ++ tailWord_7821879).sum := by decide
  have hdescent : baseEnd_7821879 < baseStart_7821879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821893 : List Nat := [1, 3, 1, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_7821893 : Nat := 118140960795 + 7821893 * 2 ^ 59
def prefixEnd_7821893 : Nat := 4983230072969 + 3 ^ 40 * 7821893 * 2
def baseEnd_7821893 : Nat := 4016390737038470541365275

theorem tailTrace_7821893 : CollatzResearch.WordTrace tailWord_7821893 prefixEnd_7821893 4016390737038470541365275 := by
  unfold tailWord_7821893
  simp only [CollatzResearch.WordTrace]
  refine ⟨285287875051625008815230333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190191916701083339210153555 285287875051625008815230333)
  ·
    refine ⟨106982953144359378305711375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285287875051625008815230333 106982953144359378305711375)
    ·
      refine ⟨160474429716539067458567063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106982953144359378305711375 160474429716539067458567063)
      ·
        refine ⟨240711644574808601187850595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160474429716539067458567063 240711644574808601187850595)
        ·
          refine ⟨361067466862212901781775893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240711644574808601187850595 361067466862212901781775893)
          ·
            refine ⟨16925037509166229771020745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361067466862212901781775893 16925037509166229771020745)
            ·
              refine ⟨12693778131874672328265559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16925037509166229771020745 12693778131874672328265559)
              ·
                refine ⟨19040667197812008492398339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693778131874672328265559 19040667197812008492398339)
                ·
                  refine ⟨28561000796718012738597509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19040667197812008492398339 28561000796718012738597509)
                  ·
                    refine ⟨5355187649384627388487033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28561000796718012738597509 5355187649384627388487033)
                    ·
                      refine ⟨4016390737038470541365275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355187649384627388487033 4016390737038470541365275)
                      ·
                        rfl

theorem cell23_7821893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_7821893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821893 prefixEnd_7821893 := by exact prefixLift 7821893
  have htrace : WordTrace (prefixWord ++ tailWord_7821893) baseStart_7821893 baseEnd_7821893 := by
    simpa [prefixWord, tailWord_7821893, baseEnd_7821893] using wordTrace_append hprefix tailTrace_7821893
  have hstable : (prefixWord ++ tailWord_7821893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821893).length < 2 ^ (prefixWord ++ tailWord_7821893).sum := by decide
  have hdescent : baseEnd_7821893 < baseStart_7821893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821929 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_7821929 : Nat := 118140960795 + 7821929 * 2 ^ 59
def prefixEnd_7821929 : Nat := 4983230072969 + 3 ^ 40 * 7821929 * 2
def baseEnd_7821929 : Nat := 1338803074114010800171703

theorem tailTrace_7821929 : CollatzResearch.WordTrace tailWord_7821929 prefixEnd_7821929 1338803074114010800171703 := by
  unfold tailWord_7821929
  simp only [CollatzResearch.WordTrace]
  refine ⟨285289188079494586963540841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190192792052996391309027227 285289188079494586963540841)
  ·
    refine ⟨213966891059620940222655631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285289188079494586963540841 213966891059620940222655631)
    ·
      refine ⟨320950336589431410333983447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213966891059620940222655631 320950336589431410333983447)
      ·
        refine ⟨481425504884147115500975171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320950336589431410333983447 481425504884147115500975171)
        ·
          refine ⟨722138257326220673251462757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481425504884147115500975171 722138257326220673251462757)
          ·
            refine ⟨135400923248666376234649267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 722138257326220673251462757 135400923248666376234649267)
            ·
              refine ⟨203101384872999564351973901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135400923248666376234649267 203101384872999564351973901)
              ·
                refine ⟨76163019327374836631990213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203101384872999564351973901 76163019327374836631990213)
                ·
                  refine ⟨14280566123882781868498165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76163019327374836631990213 14280566123882781868498165)
                  ·
                    refine ⟨1338803074114010800171703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14280566123882781868498165 1338803074114010800171703)
                    ·
                      rfl

theorem cell23_7821929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_7821929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821929 prefixEnd_7821929 := by exact prefixLift 7821929
  have htrace : WordTrace (prefixWord ++ tailWord_7821929) baseStart_7821929 baseEnd_7821929 := by
    simpa [prefixWord, tailWord_7821929, baseEnd_7821929] using wordTrace_append hprefix tailTrace_7821929
  have hstable : (prefixWord ++ tailWord_7821929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821929).length < 2 ^ (prefixWord ++ tailWord_7821929).sum := by decide
  have hdescent : baseEnd_7821929 < baseStart_7821929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821933 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 5]
def baseStart_7821933 : Nat := 118140960795 + 7821933 * 2 ^ 59
def prefixEnd_7821933 : Nat := 4983230072969 + 3 ^ 40 * 7821933 * 2
def baseEnd_7821933 : Nat := 446267919584961153873899

theorem tailTrace_7821933 : CollatzResearch.WordTrace tailWord_7821933 prefixEnd_7821933 446267919584961153873899 := by
  unfold tailWord_7821933
  simp only [CollatzResearch.WordTrace]
  refine ⟨285289333971480095646686453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190192889314320063764457635 285289333971480095646686453)
  ·
    refine ⟨26745875059826258966876855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285289333971480095646686453 26745875059826258966876855)
    ·
      refine ⟨40118812589739388450315283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26745875059826258966876855 40118812589739388450315283)
      ·
        refine ⟨60178218884609082675472925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40118812589739388450315283 60178218884609082675472925)
        ·
          refine ⟨22566832081728406003302347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60178218884609082675472925 22566832081728406003302347)
          ·
            refine ⟨33850248122592609004953521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22566832081728406003302347 33850248122592609004953521)
            ·
              refine ⟨25387686091944456753715141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33850248122592609004953521 25387686091944456753715141)
              ·
                refine ⟨4760191142239585641321589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25387686091944456753715141 4760191142239585641321589)
                ·
                  refine ⟨446267919584961153873899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4760191142239585641321589 446267919584961153873899)
                  ·
                    rfl

theorem cell23_7821933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_7821933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821933 prefixEnd_7821933 := by exact prefixLift 7821933
  have htrace : WordTrace (prefixWord ++ tailWord_7821933) baseStart_7821933 baseEnd_7821933 := by
    simpa [prefixWord, tailWord_7821933, baseEnd_7821933] using wordTrace_append hprefix tailTrace_7821933
  have hstable : (prefixWord ++ tailWord_7821933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821933).length < 2 ^ (prefixWord ++ tailWord_7821933).sum := by decide
  have hdescent : baseEnd_7821933 < baseStart_7821933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821959 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 8]
def baseStart_7821959 : Nat := 118140960795 + 7821959 * 2 ^ 59
def prefixEnd_7821959 : Nat := 4983230072969 + 3 ^ 40 * 7821959 * 2
def baseEnd_7821959 : Nat := 1338808208920555761046657

theorem tailTrace_7821959 : CollatzResearch.WordTrace tailWord_7821959 prefixEnd_7821959 1338808208920555761046657 := by
  unfold tailWord_7821959
  simp only [CollatzResearch.WordTrace]
  refine ⟨285290282269385902087132931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190193521512923934724755287 285290282269385902087132931)
  ·
    refine ⟨427935423404078853130699397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285290282269385902087132931 427935423404078853130699397)
    ·
      refine ⟨80237891888264784962006137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427935423404078853130699397 80237891888264784962006137)
      ·
        refine ⟨60178418916198588721504603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80237891888264784962006137 60178418916198588721504603)
        ·
          refine ⟨90267628374297883082256905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60178418916198588721504603 90267628374297883082256905)
          ·
            refine ⟨67700721280723412311692679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90267628374297883082256905 67700721280723412311692679)
            ·
              refine ⟨101551081921085118467539019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67700721280723412311692679 101551081921085118467539019)
              ·
                refine ⟨152326622881627677701308529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101551081921085118467539019 152326622881627677701308529)
                ·
                  refine ⟨114244967161220758275981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152326622881627677701308529 114244967161220758275981397)
                  ·
                    refine ⟨1338808208920555761046657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114244967161220758275981397 1338808208920555761046657)
                    ·
                      rfl

theorem cell23_7821959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_7821959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821959 prefixEnd_7821959 := by exact prefixLift 7821959
  have htrace : WordTrace (prefixWord ++ tailWord_7821959) baseStart_7821959 baseEnd_7821959 := by
    simpa [prefixWord, tailWord_7821959, baseEnd_7821959] using wordTrace_append hprefix tailTrace_7821959
  have hstable : (prefixWord ++ tailWord_7821959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821959).length < 2 ^ (prefixWord ++ tailWord_7821959).sum := by decide
  have hdescent : baseEnd_7821959 < baseStart_7821959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7821966 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7821966 : Nat := 118140960795 + 7821966 * 2 ^ 59
def prefixEnd_7821966 : Nat := 4983230072969 + 3 ^ 40 * 7821966 * 2
def baseEnd_7821966 : Nat := 4016428221126248755752439

theorem tailTrace_7821966 : CollatzResearch.WordTrace tailWord_7821966 prefixEnd_7821966 4016428221126248755752439 := by
  unfold tailWord_7821966
  simp only [CollatzResearch.WordTrace]
  refine ⟨35661317197545067785329719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190193691720240361521758501 35661317197545067785329719)
  ·
    refine ⟨53491975796317601677994579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35661317197545067785329719 53491975796317601677994579)
    ·
      refine ⟨80237963694476402516991869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53491975796317601677994579 80237963694476402516991869)
      ·
        refine ⟨30089236385428650943871951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80237963694476402516991869 30089236385428650943871951)
        ·
          refine ⟨45133854578142976415807927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30089236385428650943871951 45133854578142976415807927)
          ·
            refine ⟨67700781867214464623711891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45133854578142976415807927 67700781867214464623711891)
            ·
              refine ⟨101551172800821696935567837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67700781867214464623711891 101551172800821696935567837)
              ·
                refine ⟨38081689800308136350837939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101551172800821696935567837 38081689800308136350837939)
                ·
                  refine ⟨57122534700462204526256909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38081689800308136350837939 57122534700462204526256909)
                  ·
                    refine ⟨21420950512673326697346341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57122534700462204526256909 21420950512673326697346341)
                    ·
                      refine ⟨4016428221126248755752439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21420950512673326697346341 4016428221126248755752439)
                      ·
                        rfl

theorem cell23_7821966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7821966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7821966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7821966 prefixEnd_7821966 := by exact prefixLift 7821966
  have htrace : WordTrace (prefixWord ++ tailWord_7821966) baseStart_7821966 baseEnd_7821966 := by
    simpa [prefixWord, tailWord_7821966, baseEnd_7821966] using wordTrace_append hprefix tailTrace_7821966
  have hstable : (prefixWord ++ tailWord_7821966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7821966).length < 2 ^ (prefixWord ++ tailWord_7821966).sum := by decide
  have hdescent : baseEnd_7821966 < baseStart_7821966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7821966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822017 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7822017 : Nat := 118140960795 + 7822017 * 2 ^ 59
def prefixEnd_7822017 : Nat := 4983230072969 + 3 ^ 40 * 7822017 * 2
def baseEnd_7822017 : Nat := 4016454408639628056214705

theorem tailTrace_7822017 : CollatzResearch.WordTrace tailWord_7822017 prefixEnd_7822017 4016454408639628056214705 := by
  unfold tailWord_7822017
  simp only [CollatzResearch.WordTrace]
  refine ⟨285292397703175777992744305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190194931802117185328496203 285292397703175777992744305)
  ·
    refine ⟨213969298277381833494558229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285292397703175777992744305 213969298277381833494558229)
    ·
      refine ⟨10029810856752273445057417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213969298277381833494558229 10029810856752273445057417)
      ·
        refine ⟨7522358142564205083793063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029810856752273445057417 7522358142564205083793063)
        ·
          refine ⟨11283537213846307625689595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522358142564205083793063 11283537213846307625689595)
          ·
            refine ⟨16925305820769461438534393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11283537213846307625689595 16925305820769461438534393)
            ·
              refine ⟨12693979365577096078900795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16925305820769461438534393 12693979365577096078900795)
              ·
                refine ⟨19040969048365644118351193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693979365577096078900795 19040969048365644118351193)
                ·
                  refine ⟨14280726786274233088763395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19040969048365644118351193 14280726786274233088763395)
                  ·
                    refine ⟨21421090179411349633145093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14280726786274233088763395 21421090179411349633145093)
                    ·
                      refine ⟨4016454408639628056214705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21421090179411349633145093 4016454408639628056214705)
                      ·
                        rfl

theorem cell23_7822017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7822017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822017 prefixEnd_7822017 := by exact prefixLift 7822017
  have htrace : WordTrace (prefixWord ++ tailWord_7822017) baseStart_7822017 baseEnd_7822017 := by
    simpa [prefixWord, tailWord_7822017, baseEnd_7822017] using wordTrace_append hprefix tailTrace_7822017
  have hstable : (prefixWord ++ tailWord_7822017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822017).length < 2 ^ (prefixWord ++ tailWord_7822017).sum := by decide
  have hdescent : baseEnd_7822017 < baseStart_7822017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822020 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7822020 : Nat := 118140960795 + 7822020 * 2 ^ 59
def prefixEnd_7822020 : Nat := 4983230072969 + 3 ^ 40 * 7822020 * 2
def baseEnd_7822020 : Nat := 4016455949081591544477191

theorem tailTrace_7822020 : CollatzResearch.WordTrace tailWord_7822020 prefixEnd_7822020 4016455949081591544477191 := by
  unfold tailWord_7822020
  simp only [CollatzResearch.WordTrace]
  refine ⟨142646253561082454752551757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190195004748109939670069009 142646253561082454752551757)
  ·
    refine ⟨53492345085405920532206909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142646253561082454752551757 53492345085405920532206909)
    ·
      refine ⟨20059629407027220199577591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53492345085405920532206909 20059629407027220199577591)
      ·
        refine ⟨30089444110540830299366387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20059629407027220199577591 30089444110540830299366387)
        ·
          refine ⟨45134166165811245449049581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30089444110540830299366387 45134166165811245449049581)
          ·
            refine ⟨16925312312179217043393593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45134166165811245449049581 16925312312179217043393593)
            ·
              refine ⟨12693984234134412782545195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16925312312179217043393593 12693984234134412782545195)
              ·
                refine ⟨19040976351201619173817793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693984234134412782545195 19040976351201619173817793)
                ·
                  refine ⟨14280732263401214380363345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19040976351201619173817793 14280732263401214380363345)
                  ·
                    refine ⟨10710549197550910785272509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14280732263401214380363345 10710549197550910785272509)
                    ·
                      refine ⟨4016455949081591544477191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10710549197550910785272509 4016455949081591544477191)
                      ·
                        rfl

theorem cell23_7822020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7822020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822020 prefixEnd_7822020 := by exact prefixLift 7822020
  have htrace : WordTrace (prefixWord ++ tailWord_7822020) baseStart_7822020 baseEnd_7822020 := by
    simpa [prefixWord, tailWord_7822020, baseEnd_7822020] using wordTrace_append hprefix tailTrace_7822020
  have hstable : (prefixWord ++ tailWord_7822020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822020).length < 2 ^ (prefixWord ++ tailWord_7822020).sum := by decide
  have hdescent : baseEnd_7822020 < baseStart_7822020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822044 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7822044 : Nat := 118140960795 + 7822044 * 2 ^ 59
def prefixEnd_7822044 : Nat := 4983230072969 + 3 ^ 40 * 7822044 * 2
def baseEnd_7822044 : Nat := 1338822757539099816859027

theorem tailTrace_7822044 : CollatzResearch.WordTrace tailWord_7822044 prefixEnd_7822044 1338822757539099816859027 := by
  unfold tailWord_7822044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142646691237038980801988593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190195588316051974402651457 142646691237038980801988593)
  ·
    refine ⟨106985018427779235601491445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142646691237038980801988593 106985018427779235601491445)
    ·
      refine ⟨10029845477604303337639823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106985018427779235601491445 10029845477604303337639823)
      ·
        refine ⟨15044768216406455006459735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029845477604303337639823 15044768216406455006459735)
        ·
          refine ⟨22567152324609682509689603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15044768216406455006459735 22567152324609682509689603)
          ·
            refine ⟨33850728486914523764534405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22567152324609682509689603 33850728486914523764534405)
            ·
              refine ⟨6347011591296473205850201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33850728486914523764534405 6347011591296473205850201)
              ·
                refine ⟨4760258693472354904387651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347011591296473205850201 4760258693472354904387651)
                ·
                  refine ⟨7140388040208532356581477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760258693472354904387651 7140388040208532356581477)
                  ·
                    refine ⟨1338822757539099816859027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140388040208532356581477 1338822757539099816859027)
                    ·
                      rfl

theorem cell23_7822044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7822044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822044 prefixEnd_7822044 := by exact prefixLift 7822044
  have htrace : WordTrace (prefixWord ++ tailWord_7822044) baseStart_7822044 baseEnd_7822044 := by
    simpa [prefixWord, tailWord_7822044, baseEnd_7822044] using wordTrace_append hprefix tailTrace_7822044
  have hstable : (prefixWord ++ tailWord_7822044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822044).length < 2 ^ (prefixWord ++ tailWord_7822044).sum := by decide
  have hdescent : baseEnd_7822044 < baseStart_7822044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822087 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 1, 5]
def baseStart_7822087 : Nat := 118140960795 + 7822087 * 2 ^ 59
def prefixEnd_7822087 : Nat := 4983230072969 + 3 ^ 40 * 7822087 * 2
def baseEnd_7822087 : Nat := 1338830117428480927446461

theorem tailTrace_7822087 : CollatzResearch.WordTrace tailWord_7822087 prefixEnd_7822087 1338830117428480927446461 := by
  unfold tailWord_7822087
  simp only [CollatzResearch.WordTrace]
  refine ⟨285294950812922179947792515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190196633875281453298528343 285294950812922179947792515)
  ·
    refine ⟨427942426219383269921688773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285294950812922179947792515 427942426219383269921688773)
    ·
      refine ⟨80239204916134363110316645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427942426219383269921688773 80239204916134363110316645)
      ·
        refine ⟨15044850921775193083184371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80239204916134363110316645 15044850921775193083184371)
        ·
          refine ⟨22567276382662789624776557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15044850921775193083184371 22567276382662789624776557)
          ·
            refine ⟨8462728643498546109291209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22567276382662789624776557 8462728643498546109291209)
            ·
              refine ⟨6347046482623909581968407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462728643498546109291209 6347046482623909581968407)
              ·
                refine ⟨9520569723935864372952611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347046482623909581968407 9520569723935864372952611)
                ·
                  refine ⟨14280854585903796559428917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520569723935864372952611 14280854585903796559428917)
                  ·
                    refine ⟨1338830117428480927446461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14280854585903796559428917 1338830117428480927446461)
                    ·
                      rfl

theorem cell23_7822087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_7822087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822087 prefixEnd_7822087 := by exact prefixLift 7822087
  have htrace : WordTrace (prefixWord ++ tailWord_7822087) baseStart_7822087 baseEnd_7822087 := by
    simpa [prefixWord, tailWord_7822087, baseEnd_7822087] using wordTrace_append hprefix tailTrace_7822087
  have hstable : (prefixWord ++ tailWord_7822087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822087).length < 2 ^ (prefixWord ++ tailWord_7822087).sum := by decide
  have hdescent : baseEnd_7822087 < baseStart_7822087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822090 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_7822090 : Nat := 118140960795 + 7822090 * 2 ^ 59
def prefixEnd_7822090 : Nat := 4983230072969 + 3 ^ 40 * 7822090 * 2
def baseEnd_7822090 : Nat := 4016491892727406270601869

theorem tailTrace_7822090 : CollatzResearch.WordTrace tailWord_7822090 prefixEnd_7822090 4016491892727406270601869 := by
  unfold tailWord_7822090
  simp only [CollatzResearch.WordTrace]
  refine ⟨71323765057977827865037931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190196706821274207640101149 71323765057977827865037931)
  ·
    refine ⟨106985647586966741797556897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71323765057977827865037931 106985647586966741797556897)
    ·
      refine ⟨80239235690225056348167673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106985647586966741797556897 80239235690225056348167673)
      ·
        refine ⟨60179426767668792261125755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80239235690225056348167673 60179426767668792261125755)
        ·
          refine ⟨90269140151503188391688633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60179426767668792261125755 90269140151503188391688633)
          ·
            refine ⟨67701855113627391293766475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90269140151503188391688633 67701855113627391293766475)
            ·
              refine ⟨101552782670441086940649713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67701855113627391293766475 101552782670441086940649713)
              ·
                refine ⟨76164587002830815205487285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101552782670441086940649713 76164587002830815205487285)
                ·
                  refine ⟨7140430031515388925514433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76164587002830815205487285 7140430031515388925514433)
                  ·
                    refine ⟨5355322523636541694135825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7140430031515388925514433 5355322523636541694135825)
                    ·
                      refine ⟨4016491892727406270601869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355322523636541694135825 4016491892727406270601869)
                      ·
                        rfl

theorem cell23_7822090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_7822090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822090 prefixEnd_7822090 := by exact prefixLift 7822090
  have htrace : WordTrace (prefixWord ++ tailWord_7822090) baseStart_7822090 baseEnd_7822090 := by
    simpa [prefixWord, tailWord_7822090, baseEnd_7822090] using wordTrace_append hprefix tailTrace_7822090
  have hstable : (prefixWord ++ tailWord_7822090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822090).length < 2 ^ (prefixWord ++ tailWord_7822090).sum := by decide
  have hdescent : baseEnd_7822090 < baseStart_7822090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822123 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 3]
def baseStart_7822123 : Nat := 118140960795 + 7822123 * 2 ^ 59
def prefixEnd_7822123 : Nat := 4983230072969 + 3 ^ 40 * 7822123 * 2
def baseEnd_7822123 : Nat := 4016508837589004641489217

theorem tailTrace_7822123 : CollatzResearch.WordTrace tailWord_7822123 prefixEnd_7822123 4016508837589004641489217 := by
  unfold tailWord_7822123
  simp only [CollatzResearch.WordTrace]
  refine ⟨285296263840791758096103023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190197509227194505397402015 285296263840791758096103023)
  ·
    refine ⟨427944395761187637144154535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285296263840791758096103023 427944395761187637144154535)
    ·
      refine ⟨641916593641781455716231803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427944395761187637144154535 641916593641781455716231803)
      ·
        refine ⟨962874890462672183574347705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641916593641781455716231803 962874890462672183574347705)
        ·
          refine ⟨722156167847004137680760779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962874890462672183574347705 722156167847004137680760779)
          ·
            refine ⟨1083234251770506206521141169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722156167847004137680760779 1083234251770506206521141169)
            ·
              refine ⟨812425688827879654890855877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083234251770506206521141169 812425688827879654890855877)
              ·
                refine ⟨152329816655227435292035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 812425688827879654890855877 152329816655227435292035477)
                ·
                  refine ⟨7140460155713786029314163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152329816655227435292035477 7140460155713786029314163)
                  ·
                    refine ⟨10710690233570679043971245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140460155713786029314163 10710690233570679043971245)
                    ·
                      refine ⟨4016508837589004641489217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10710690233570679043971245 4016508837589004641489217)
                      ·
                        rfl

theorem cell23_7822123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 3].length) (baseStart_7822123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822123 prefixEnd_7822123 := by exact prefixLift 7822123
  have htrace : WordTrace (prefixWord ++ tailWord_7822123) baseStart_7822123 baseEnd_7822123 := by
    simpa [prefixWord, tailWord_7822123, baseEnd_7822123] using wordTrace_append hprefix tailTrace_7822123
  have hstable : (prefixWord ++ tailWord_7822123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822123).length < 2 ^ (prefixWord ++ tailWord_7822123).sum := by decide
  have hdescent : baseEnd_7822123 < baseStart_7822123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822136 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_7822136 : Nat := 118140960795 + 7822136 * 2 ^ 59
def prefixEnd_7822136 : Nat := 4983230072969 + 3 ^ 40 * 7822136 * 2
def baseEnd_7822136 : Nat := 4016515512837513090626657

theorem tailTrace_7822136 : CollatzResearch.WordTrace tailWord_7822136 prefixEnd_7822136 4016515512837513090626657 := by
  unfold tailWord_7822136
  simp only [CollatzResearch.WordTrace]
  refine ⟨142648368994872330658163131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190197825326496440877550841 142648368994872330658163131)
  ·
    refine ⟨213972553492308495987244697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142648368994872330658163131 213972553492308495987244697)
    ·
      refine ⟨160479415119231371990433523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213972553492308495987244697 160479415119231371990433523)
      ·
        refine ⟨240719122678847057985650285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160479415119231371990433523 240719122678847057985650285)
        ·
          refine ⟨90269671004567646744618857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240719122678847057985650285 90269671004567646744618857)
          ·
            refine ⟨67702253253425735058464143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90269671004567646744618857 67702253253425735058464143)
            ·
              refine ⟨101553379880138602587696215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67702253253425735058464143 101553379880138602587696215)
              ·
                refine ⟨152330069820207903881544323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101553379880138602587696215 152330069820207903881544323)
                ·
                  refine ⟨228495104730311855822316485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152330069820207903881544323 228495104730311855822316485)
                  ·
                    refine ⟨42842832136933472966684341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228495104730311855822316485 42842832136933472966684341)
                    ·
                      refine ⟨4016515512837513090626657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42842832136933472966684341 4016515512837513090626657)
                      ·
                        rfl

theorem cell23_7822136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_7822136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822136 prefixEnd_7822136 := by exact prefixLift 7822136
  have htrace : WordTrace (prefixWord ++ tailWord_7822136) baseStart_7822136 baseEnd_7822136 := by
    simpa [prefixWord, tailWord_7822136, baseEnd_7822136] using wordTrace_append hprefix tailTrace_7822136
  have hstable : (prefixWord ++ tailWord_7822136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822136).length < 2 ^ (prefixWord ++ tailWord_7822136).sum := by decide
  have hdescent : baseEnd_7822136 < baseStart_7822136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822183 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_7822183 : Nat := 118140960795 + 7822183 * 2 ^ 59
def prefixEnd_7822183 : Nat := 4983230072969 + 3 ^ 40 * 7822183 * 2
def baseEnd_7822183 : Nat := 4016539646428274406738941

theorem tailTrace_7822183 : CollatzResearch.WordTrace tailWord_7822183 prefixEnd_7822183 4016539646428274406738941 := by
  unfold tailWord_7822183
  simp only [CollatzResearch.WordTrace]
  refine ⟨285298452220574388343287203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190198968147049592228858135 285298452220574388343287203)
  ·
    refine ⟨427947678330861582514930805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285298452220574388343287203 427947678330861582514930805)
    ·
      refine ⟨40120094843518273360774763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427947678330861582514930805 40120094843518273360774763)
      ·
        refine ⟨60180142265277410041162145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40120094843518273360774763 60180142265277410041162145)
        ·
          refine ⟨45135106698958057530871609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60180142265277410041162145 45135106698958057530871609)
          ·
            refine ⟨33851330024218543148153707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45135106698958057530871609 33851330024218543148153707)
            ·
              refine ⟨50776995036327814722230561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33851330024218543148153707 50776995036327814722230561)
              ·
                refine ⟨38082746277245861041672921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50776995036327814722230561 38082746277245861041672921)
                ·
                  refine ⟨28562059707934395781254691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38082746277245861041672921 28562059707934395781254691)
                  ·
                    refine ⟨42843089561901593671882037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28562059707934395781254691 42843089561901593671882037)
                    ·
                      refine ⟨4016539646428274406738941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42843089561901593671882037 4016539646428274406738941)
                      ·
                        rfl

theorem cell23_7822183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_7822183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822183 prefixEnd_7822183 := by exact prefixLift 7822183
  have htrace : WordTrace (prefixWord ++ tailWord_7822183) baseStart_7822183 baseEnd_7822183 := by
    simpa [prefixWord, tailWord_7822183, baseEnd_7822183] using wordTrace_append hprefix tailTrace_7822183
  have hstable : (prefixWord ++ tailWord_7822183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822183).length < 2 ^ (prefixWord ++ tailWord_7822183).sum := by decide
  have hdescent : baseEnd_7822183 < baseStart_7822183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822184 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7822184 : Nat := 118140960795 + 7822184 * 2 ^ 59
def prefixEnd_7822184 : Nat := 4983230072969 + 3 ^ 40 * 7822184 * 2
def baseEnd_7822184 : Nat := 4016540159908928902826437

theorem tailTrace_7822184 : CollatzResearch.WordTrace tailWord_7822184 prefixEnd_7822184 4016540159908928902826437 := by
  unfold tailWord_7822184
  simp only [CollatzResearch.WordTrace]
  refine ⟨142649244346785382757036803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190198992462380510342715737 142649244346785382757036803)
  ·
    refine ⟨213973866520178074135555205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142649244346785382757036803 213973866520178074135555205)
    ·
      refine ⟨40120099972533388900416601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213973866520178074135555205 40120099972533388900416601)
      ·
        refine ⟨30090074979400041675312451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40120099972533388900416601 30090074979400041675312451)
        ·
          refine ⟨45135112469100062512968677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30090074979400041675312451 45135112469100062512968677)
          ·
            refine ⟨8462833587956261721181627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45135112469100062512968677 8462833587956261721181627)
            ·
              refine ⟨12694250381934392581772441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462833587956261721181627 12694250381934392581772441)
              ·
                refine ⟨9520687786450794436329331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12694250381934392581772441 9520687786450794436329331)
                ·
                  refine ⟨14281031679676191654493997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520687786450794436329331 14281031679676191654493997)
                  ·
                    refine ⟨5355386879878571870435249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14281031679676191654493997 5355386879878571870435249)
                    ·
                      refine ⟨4016540159908928902826437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355386879878571870435249 4016540159908928902826437)
                      ·
                        rfl

theorem cell23_7822184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7822184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822184 prefixEnd_7822184 := by exact prefixLift 7822184
  have htrace : WordTrace (prefixWord ++ tailWord_7822184) baseStart_7822184 baseEnd_7822184 := by
    simpa [prefixWord, tailWord_7822184, baseEnd_7822184] using wordTrace_append hprefix tailTrace_7822184
  have hstable : (prefixWord ++ tailWord_7822184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822184).length < 2 ^ (prefixWord ++ tailWord_7822184).sum := by decide
  have hdescent : baseEnd_7822184 < baseStart_7822184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822197 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7822197 : Nat := 118140960795 + 7822197 * 2 ^ 59
def prefixEnd_7822197 : Nat := 4983230072969 + 3 ^ 40 * 7822197 * 2
def baseEnd_7822197 : Nat := 4016546835157437351963877

theorem tailTrace_7822197 : CollatzResearch.WordTrace tailWord_7822197 prefixEnd_7822197 4016546835157437351963877 := by
  unfold tailWord_7822197
  simp only [CollatzResearch.WordTrace]
  refine ⟨285298962842523668734296845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190199308561682445822864563 285298962842523668734296845)
  ·
    refine ⟨106987111065946375775361317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285298962842523668734296845 106987111065946375775361317)
    ·
      refine ⟨20060083324864945457880247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106987111065946375775361317 20060083324864945457880247)
      ·
        refine ⟨30090124987297418186820371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20060083324864945457880247 30090124987297418186820371)
        ·
          refine ⟨45135187480946127280230557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30090124987297418186820371 45135187480946127280230557)
          ·
            refine ⟨16925695305354797730086459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45135187480946127280230557 16925695305354797730086459)
            ·
              refine ⟨25388542958032196595129689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16925695305354797730086459 25388542958032196595129689)
              ·
                refine ⟨19041407218524147446347267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25388542958032196595129689 19041407218524147446347267)
                ·
                  refine ⟨28562110827786221169520901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19041407218524147446347267 28562110827786221169520901)
                  ·
                    refine ⟨5355395780209916469285169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28562110827786221169520901 5355395780209916469285169)
                    ·
                      refine ⟨4016546835157437351963877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355395780209916469285169 4016546835157437351963877)
                      ·
                        rfl

theorem cell23_7822197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7822197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822197 prefixEnd_7822197 := by exact prefixLift 7822197
  have htrace : WordTrace (prefixWord ++ tailWord_7822197) baseStart_7822197 baseEnd_7822197 := by
    simpa [prefixWord, tailWord_7822197, baseEnd_7822197] using wordTrace_append hprefix tailTrace_7822197
  have hstable : (prefixWord ++ tailWord_7822197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822197).length < 2 ^ (prefixWord ++ tailWord_7822197).sum := by decide
  have hdescent : baseEnd_7822197 < baseStart_7822197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822270 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7822270 : Nat := 118140960795 + 7822270 * 2 ^ 59
def prefixEnd_7822270 : Nat := 4983230072969 + 3 ^ 40 * 7822270 * 2
def baseEnd_7822270 : Nat := 4016584319245215566351041

theorem tailTrace_7822270 : CollatzResearch.WordTrace tailWord_7822270 prefixEnd_7822270 4016584319245215566351041 := by
  unfold tailWord_7822270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662703171407400275213033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190201083580839468134469509 35662703171407400275213033)
  ·
    refine ⟨26747027378555550206409775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35662703171407400275213033 26747027378555550206409775)
    ·
      refine ⟨40120541067833325309614663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26747027378555550206409775 40120541067833325309614663)
      ·
        refine ⟨60180811601749987964421995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40120541067833325309614663 60180811601749987964421995)
        ·
          refine ⟨90271217402624981946632993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60180811601749987964421995 90271217402624981946632993)
          ·
            refine ⟨67703413051968736459974745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90271217402624981946632993 67703413051968736459974745)
            ·
              refine ⟨50777559788976552344981059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67703413051968736459974745 50777559788976552344981059)
              ·
                refine ⟨76166339683464828517471589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50777559788976552344981059 76166339683464828517471589)
                ·
                  refine ⟨14281188690649655347025923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76166339683464828517471589 14281188690649655347025923)
                  ·
                    refine ⟨21421783035974483020538885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14281188690649655347025923 21421783035974483020538885)
                    ·
                      refine ⟨4016584319245215566351041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21421783035974483020538885 4016584319245215566351041)
                      ·
                        rfl

theorem cell23_7822270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7822270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822270 prefixEnd_7822270 := by exact prefixLift 7822270
  have htrace : WordTrace (prefixWord ++ tailWord_7822270) baseStart_7822270 baseEnd_7822270 := by
    simpa [prefixWord, tailWord_7822270, baseEnd_7822270] using wordTrace_append hprefix tailTrace_7822270
  have hstable : (prefixWord ++ tailWord_7822270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822270).length < 2 ^ (prefixWord ++ tailWord_7822270).sum := by decide
  have hdescent : baseEnd_7822270 < baseStart_7822270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822314 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_7822314 : Nat := 118140960795 + 7822314 * 2 ^ 59
def prefixEnd_7822314 : Nat := 4983230072969 + 3 ^ 40 * 7822314 * 2
def baseEnd_7822314 : Nat := 1338868970798004464733613

theorem tailTrace_7822314 : CollatzResearch.WordTrace tailWord_7822314 prefixEnd_7822314 1338868970798004464733613 := by
  unfold tailWord_7822314
  simp only [CollatzResearch.WordTrace]
  refine ⟨71325807545774949429076499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190202153455399865144203997 71325807545774949429076499)
  ·
    refine ⟨106988711318662424143614749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71325807545774949429076499 106988711318662424143614749)
    ·
      refine ⟨40120766744498409053855531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106988711318662424143614749 40120766744498409053855531)
      ·
        refine ⟨60181150116747613580783297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40120766744498409053855531 60181150116747613580783297)
        ·
          refine ⟨45135862587560710185587473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60181150116747613580783297 45135862587560710185587473)
          ·
            refine ⟨33851896940670532639190605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45135862587560710185587473 33851896940670532639190605)
            ·
              refine ⟨12694461352751449739696477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33851896940670532639190605 12694461352751449739696477)
              ·
                refine ⟨4760423007281793652386179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12694461352751449739696477 4760423007281793652386179)
                ·
                  refine ⟨7140634510922690478579269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760423007281793652386179 7140634510922690478579269)
                  ·
                    refine ⟨1338868970798004464733613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140634510922690478579269 1338868970798004464733613)
                    ·
                      rfl

theorem cell23_7822314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_7822314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822314 prefixEnd_7822314 := by exact prefixLift 7822314
  have htrace : WordTrace (prefixWord ++ tailWord_7822314) baseStart_7822314 baseEnd_7822314 := by
    simpa [prefixWord, tailWord_7822314, baseEnd_7822314] using wordTrace_append hprefix tailTrace_7822314
  have hstable : (prefixWord ++ tailWord_7822314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822314).length < 2 ^ (prefixWord ++ tailWord_7822314).sum := by decide
  have hdescent : baseEnd_7822314 < baseStart_7822314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822323 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 7, 5]
def baseStart_7822323 : Nat := 118140960795 + 7822323 * 2 ^ 59
def prefixEnd_7822323 : Nat := 4983230072969 + 3 ^ 40 * 7822323 * 2
def baseEnd_7822323 : Nat := 1338870511239967952996099

theorem tailTrace_7822323 : CollatzResearch.WordTrace tailWord_7822323 prefixEnd_7822323 1338870511239967952996099 := by
  unfold tailWord_7822323
  simp only [CollatzResearch.WordTrace]
  refine ⟨285303558440067192253383623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190202372293378128168922415 285303558440067192253383623)
  ·
    refine ⟨427955337660100788380075435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285303558440067192253383623 427955337660100788380075435)
    ·
      refine ⟨641933006490151182570113153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427955337660100788380075435 641933006490151182570113153)
      ·
        refine ⟨481449754867613386927584865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641933006490151182570113153 481449754867613386927584865)
        ·
          refine ⟨361087316150710040195688649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481449754867613386927584865 361087316150710040195688649)
          ·
            refine ⟨270815487113032530146766487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361087316150710040195688649 270815487113032530146766487)
            ·
              refine ⟨406223230669548795220149731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270815487113032530146766487 406223230669548795220149731)
              ·
                refine ⟨609334846004323192830224597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406223230669548795220149731 609334846004323192830224597)
                ·
                  refine ⟨14281285453226324831958389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 609334846004323192830224597 14281285453226324831958389)
                  ·
                    refine ⟨1338870511239967952996099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14281285453226324831958389 1338870511239967952996099)
                    ·
                      rfl

theorem cell23_7822323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].length) (baseStart_7822323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822323 prefixEnd_7822323 := by exact prefixLift 7822323
  have htrace : WordTrace (prefixWord ++ tailWord_7822323) baseStart_7822323 baseEnd_7822323 := by
    simpa [prefixWord, tailWord_7822323, baseEnd_7822323] using wordTrace_append hprefix tailTrace_7822323
  have hstable : (prefixWord ++ tailWord_7822323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822323).length < 2 ^ (prefixWord ++ tailWord_7822323).sum := by decide
  have hdescent : baseEnd_7822323 < baseStart_7822323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822333 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7822333 : Nat := 118140960795 + 7822333 * 2 ^ 59
def prefixEnd_7822333 : Nat := 4983230072969 + 3 ^ 40 * 7822333 * 2
def baseEnd_7822333 : Nat := 4016616668526448819863251

theorem tailTrace_7822333 : CollatzResearch.WordTrace tailWord_7822333 prefixEnd_7822333 4016616668526448819863251 := by
  unfold tailWord_7822333
  simp only [CollatzResearch.WordTrace]
  refine ⟨285303923170030963961247653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190202615446687309307498435 285303923170030963961247653)
  ·
    refine ⟨53494485594380805742733935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285303923170030963961247653 53494485594380805742733935)
    ·
      refine ⟨80241728391571208614100903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53494485594380805742733935 80241728391571208614100903)
      ·
        refine ⟨120362592587356812921151355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80241728391571208614100903 120362592587356812921151355)
        ·
          refine ⟨180543888881035219381727033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120362592587356812921151355 180543888881035219381727033)
          ·
            refine ⟨135407916660776414536295275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180543888881035219381727033 135407916660776414536295275)
            ·
              refine ⟨203111874991164621804442913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135407916660776414536295275 203111874991164621804442913)
              ·
                refine ⟨152333906243373466353332185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203111874991164621804442913 152333906243373466353332185)
                ·
                  refine ⟨114250429682530099764999139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152333906243373466353332185 114250429682530099764999139)
                  ·
                    refine ⟨171375644523795149647498709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114250429682530099764999139 171375644523795149647498709)
                    ·
                      refine ⟨4016616668526448819863251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171375644523795149647498709 4016616668526448819863251)
                      ·
                        rfl

theorem cell23_7822333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7822333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822333 prefixEnd_7822333 := by exact prefixLift 7822333
  have htrace : WordTrace (prefixWord ++ tailWord_7822333) baseStart_7822333 baseEnd_7822333 := by
    simpa [prefixWord, tailWord_7822333, baseEnd_7822333] using wordTrace_append hprefix tailTrace_7822333
  have hstable : (prefixWord ++ tailWord_7822333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822333).length < 2 ^ (prefixWord ++ tailWord_7822333).sum := by decide
  have hdescent : baseEnd_7822333 < baseStart_7822333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822353 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_7822353 : Nat := 118140960795 + 7822353 * 2 ^ 59
def prefixEnd_7822353 : Nat := 4983230072969 + 3 ^ 40 * 7822353 * 2
def baseEnd_7822353 : Nat := 1338875646046512913871053

theorem tailTrace_7822353 : CollatzResearch.WordTrace tailWord_7822353 prefixEnd_7822353 1338875646046512913871053 := by
  unfold tailWord_7822353
  simp only [CollatzResearch.WordTrace]
  refine ⟨285304652629958507376975713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190203101753305671584650475 285304652629958507376975713)
  ·
    refine ⟨213978489472468880532731785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285304652629958507376975713 213978489472468880532731785)
    ·
      refine ⟨160483867104351660399548839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213978489472468880532731785 160483867104351660399548839)
      ·
        refine ⟨240725800656527490599323259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160483867104351660399548839 240725800656527490599323259)
        ·
          refine ⟨361088700984791235898984889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240725800656527490599323259 361088700984791235898984889)
          ·
            refine ⟨270816525738593426924238667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361088700984791235898984889 270816525738593426924238667)
            ·
              refine ⟨406224788607890140386358001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270816525738593426924238667 406224788607890140386358001)
              ·
                refine ⟨304668591455917605289768501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406224788607890140386358001 304668591455917605289768501)
                ·
                  refine ⟨28562680448992275495915797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304668591455917605289768501 28562680448992275495915797)
                  ·
                    refine ⟨1338875646046512913871053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28562680448992275495915797 1338875646046512913871053)
                    ·
                      rfl

theorem cell23_7822353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_7822353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822353 prefixEnd_7822353 := by exact prefixLift 7822353
  have htrace : WordTrace (prefixWord ++ tailWord_7822353) baseStart_7822353 baseEnd_7822353 := by
    simpa [prefixWord, tailWord_7822353, baseEnd_7822353] using wordTrace_append hprefix tailTrace_7822353
  have hstable : (prefixWord ++ tailWord_7822353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822353).length < 2 ^ (prefixWord ++ tailWord_7822353).sum := by decide
  have hdescent : baseEnd_7822353 < baseStart_7822353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822357 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_7822357 : Nat := 118140960795 + 7822357 * 2 ^ 59
def prefixEnd_7822357 : Nat := 4983230072969 + 3 ^ 40 * 7822357 * 2
def baseEnd_7822357 : Nat := 1338876330687385575321047

theorem tailTrace_7822357 : CollatzResearch.WordTrace tailWord_7822357 prefixEnd_7822357 1338876330687385575321047 := by
  unfold tailWord_7822357
  simp only [CollatzResearch.WordTrace]
  refine ⟨285304798521944016060121325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190203199014629344040080883 285304798521944016060121325)
  ·
    refine ⟨106989299445729006022545497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285304798521944016060121325 106989299445729006022545497)
    ·
      refine ⟨80241974584296754516909123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106989299445729006022545497 80241974584296754516909123)
      ·
        refine ⟨120362961876445131775363685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80241974584296754516909123 120362961876445131775363685)
        ·
          refine ⟨22568055351833462207880691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120362961876445131775363685 22568055351833462207880691)
          ·
            refine ⟨33852083027750193311821037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22568055351833462207880691 33852083027750193311821037)
            ·
              refine ⟨12694531135406322491932889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33852083027750193311821037 12694531135406322491932889)
              ·
                refine ⟨9520898351554741868949667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12694531135406322491932889 9520898351554741868949667)
                ·
                  refine ⟨14281347527332112803424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520898351554741868949667 14281347527332112803424501)
                  ·
                    refine ⟨1338876330687385575321047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14281347527332112803424501 1338876330687385575321047)
                    ·
                      rfl

theorem cell23_7822357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_7822357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822357 prefixEnd_7822357 := by exact prefixLift 7822357
  have htrace : WordTrace (prefixWord ++ tailWord_7822357) baseStart_7822357 baseEnd_7822357 := by
    simpa [prefixWord, tailWord_7822357, baseEnd_7822357] using wordTrace_append hprefix tailTrace_7822357
  have hstable : (prefixWord ++ tailWord_7822357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822357).length < 2 ^ (prefixWord ++ tailWord_7822357).sum := by decide
  have hdescent : baseEnd_7822357 < baseStart_7822357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822370 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7822370 : Nat := 118140960795 + 7822370 * 2 ^ 59
def prefixEnd_7822370 : Nat := 4983230072969 + 3 ^ 40 * 7822370 * 2
def baseEnd_7822370 : Nat := 1338878555770221725033527

theorem tailTrace_7822370 : CollatzResearch.WordTrace tailWord_7822370 prefixEnd_7822370 1338878555770221725033527 := by
  unfold tailWord_7822370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71326318167724229820086141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190203515113931279520229709 71326318167724229820086141)
  ·
    refine ⟨26747369312896586182532303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71326318167724229820086141 26747369312896586182532303)
    ·
      refine ⟨40121053969344879273798455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26747369312896586182532303 40121053969344879273798455)
      ·
        refine ⟨60181580954017318910697683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40121053969344879273798455 60181580954017318910697683)
        ·
          refine ⟨90272371431025978366046525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60181580954017318910697683 90272371431025978366046525)
          ·
            refine ⟨33852139286634741887267447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90272371431025978366046525 33852139286634741887267447)
            ·
              refine ⟨50778208929952112830901171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33852139286634741887267447 50778208929952112830901171)
              ·
                refine ⟨76167313394928169246351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50778208929952112830901171 76167313394928169246351757)
                ·
                  refine ⟨28562742523098063467381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76167313394928169246351757 28562742523098063467381909)
                  ·
                    refine ⟨1338878555770221725033527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28562742523098063467381909 1338878555770221725033527)
                    ·
                      rfl

theorem cell23_7822370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7822370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822370 prefixEnd_7822370 := by exact prefixLift 7822370
  have htrace : WordTrace (prefixWord ++ tailWord_7822370) baseStart_7822370 baseEnd_7822370 := by
    simpa [prefixWord, tailWord_7822370, baseEnd_7822370] using wordTrace_append hprefix tailTrace_7822370
  have hstable : (prefixWord ++ tailWord_7822370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822370).length < 2 ^ (prefixWord ++ tailWord_7822370).sum := by decide
  have hdescent : baseEnd_7822370 < baseStart_7822370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822388 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7822388 : Nat := 118140960795 + 7822388 * 2 ^ 59
def prefixEnd_7822388 : Nat := 4983230072969 + 3 ^ 40 * 7822388 * 2
def baseEnd_7822388 : Nat := 4016644909962446104675499

theorem tailTrace_7822388 : CollatzResearch.WordTrace tailWord_7822388 prefixEnd_7822388 4016644909962446104675499 := by
  unfold tailWord_7822388
  simp only [CollatzResearch.WordTrace]
  refine ⟨142652964592415854177249909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190203952789887805569666545 142652964592415854177249909)
  ·
    refine ⟨13373715430538986329117179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142652964592415854177249909 13373715430538986329117179)
    ·
      refine ⟨20060573145808479493675769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13373715430538986329117179 20060573145808479493675769)
      ·
        refine ⟨15045429859356359620256827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20060573145808479493675769 15045429859356359620256827)
        ·
          refine ⟨22568144789034539430385241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15045429859356359620256827 22568144789034539430385241)
          ·
            refine ⟨16926108591775904572788931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22568144789034539430385241 16926108591775904572788931)
            ·
              refine ⟨25389162887663856859183397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926108591775904572788931 25389162887663856859183397)
              ·
                refine ⟨4760468041436973161096887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25389162887663856859183397 4760468041436973161096887)
                ·
                  refine ⟨7140702062155459741645331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760468041436973161096887 7140702062155459741645331)
                  ·
                    refine ⟨10711053093233189612467997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140702062155459741645331 10711053093233189612467997)
                    ·
                      refine ⟨4016644909962446104675499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711053093233189612467997 4016644909962446104675499)
                      ·
                        rfl

theorem cell23_7822388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7822388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822388 prefixEnd_7822388 := by exact prefixLift 7822388
  have htrace : WordTrace (prefixWord ++ tailWord_7822388) baseStart_7822388 baseEnd_7822388 := by
    simpa [prefixWord, tailWord_7822388, baseEnd_7822388] using wordTrace_append hprefix tailTrace_7822388
  have hstable : (prefixWord ++ tailWord_7822388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822388).length < 2 ^ (prefixWord ++ tailWord_7822388).sum := by decide
  have hdescent : baseEnd_7822388 < baseStart_7822388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822397 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7822397 : Nat := 118140960795 + 7822397 * 2 ^ 59
def prefixEnd_7822397 : Nat := 4983230072969 + 3 ^ 40 * 7822397 * 2
def baseEnd_7822397 : Nat := 4016649531288336569462957

theorem tailTrace_7822397 : CollatzResearch.WordTrace tailWord_7822397 prefixEnd_7822397 4016649531288336569462957 := by
  unfold tailWord_7822397
  simp only [CollatzResearch.WordTrace]
  refine ⟨285306257441799102891577445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190204171627866068594384963 285306257441799102891577445)
  ·
    refine ⟨53494923270337331792170771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285306257441799102891577445 53494923270337331792170771)
    ·
      refine ⟨80242384905505997688256157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53494923270337331792170771 80242384905505997688256157)
      ·
        refine ⟨30090894339564749133096059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80242384905505997688256157 30090894339564749133096059)
        ·
          refine ⟨45136341509347123699644089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30090894339564749133096059 45136341509347123699644089)
          ·
            refine ⟨33852256132010342774733067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45136341509347123699644089 33852256132010342774733067)
            ·
              refine ⟨50778384198015514162099601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33852256132010342774733067 50778384198015514162099601)
              ·
                refine ⟨38083788148511635621574701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50778384198015514162099601 38083788148511635621574701)
                ·
                  refine ⟨14281420555691863358090513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38083788148511635621574701 14281420555691863358090513)
                  ·
                    refine ⟨10711065416768897518567885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14281420555691863358090513 10711065416768897518567885)
                    ·
                      refine ⟨4016649531288336569462957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711065416768897518567885 4016649531288336569462957)
                      ·
                        rfl

theorem cell23_7822397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7822397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822397 prefixEnd_7822397 := by exact prefixLift 7822397
  have htrace : WordTrace (prefixWord ++ tailWord_7822397) baseStart_7822397 baseEnd_7822397 := by
    simpa [prefixWord, tailWord_7822397, baseEnd_7822397] using wordTrace_append hprefix tailTrace_7822397
  have hstable : (prefixWord ++ tailWord_7822397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822397).length < 2 ^ (prefixWord ++ tailWord_7822397).sum := by decide
  have hdescent : baseEnd_7822397 < baseStart_7822397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822407 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_7822407 : Nat := 118140960795 + 7822407 * 2 ^ 59
def prefixEnd_7822407 : Nat := 4983230072969 + 3 ^ 40 * 7822407 * 2
def baseEnd_7822407 : Nat := 4016654666094881530337911

theorem tailTrace_7822407 : CollatzResearch.WordTrace tailWord_7822407 prefixEnd_7822407 4016654666094881530337911 := by
  unfold tailWord_7822407
  simp only [CollatzResearch.WordTrace]
  refine ⟨285306622171762874599441475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190204414781175249732960983 285306622171762874599441475)
  ·
    refine ⟨427959933257644311899162213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285306622171762874599441475 427959933257644311899162213)
    ·
      refine ⟨80242487485808308481092915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427959933257644311899162213 80242487485808308481092915)
      ·
        refine ⟨120363731228712462721639373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80242487485808308481092915 120363731228712462721639373)
        ·
          refine ⟨45136399210767173520614765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120363731228712462721639373 45136399210767173520614765)
          ·
            refine ⟨16926149704037690070230537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45136399210767173520614765 16926149704037690070230537)
            ·
              refine ⟨12694612278028267552672903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16926149704037690070230537 12694612278028267552672903)
              ·
                refine ⟨19041918417042401329009355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694612278028267552672903 19041918417042401329009355)
                ·
                  refine ⟨28562877625563601993514033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19041918417042401329009355 28562877625563601993514033)
                  ·
                    refine ⟨21422158219172701495135525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28562877625563601993514033 21422158219172701495135525)
                    ·
                      refine ⟨4016654666094881530337911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21422158219172701495135525 4016654666094881530337911)
                      ·
                        rfl

theorem cell23_7822407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_7822407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822407 prefixEnd_7822407 := by exact prefixLift 7822407
  have htrace : WordTrace (prefixWord ++ tailWord_7822407) baseStart_7822407 baseEnd_7822407 := by
    simpa [prefixWord, tailWord_7822407, baseEnd_7822407] using wordTrace_append hprefix tailTrace_7822407
  have hstable : (prefixWord ++ tailWord_7822407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822407).length < 2 ^ (prefixWord ++ tailWord_7822407).sum := by decide
  have hdescent : baseEnd_7822407 < baseStart_7822407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822428 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7822428 : Nat := 118140960795 + 7822428 * 2 ^ 59
def prefixEnd_7822428 : Nat := 4983230072969 + 3 ^ 40 * 7822428 * 2
def baseEnd_7822428 : Nat := 4016665449188625948175315

theorem tailTrace_7822428 : CollatzResearch.WordTrace tailWord_7822428 prefixEnd_7822428 4016665449188625948175315 := by
  unfold tailWord_7822428
  simp only [CollatzResearch.WordTrace]
  refine ⟨142653694052343397592977969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190204925403124530123970625 142653694052343397592977969)
  ·
    refine ⟨106990270539257548194733477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142653694052343397592977969 106990270539257548194733477)
    ·
      refine ⟨20060675726110790286512527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106990270539257548194733477 20060675726110790286512527)
      ·
        refine ⟨30091013589166185429768791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20060675726110790286512527 30091013589166185429768791)
        ·
          refine ⟨45136520383749278144653187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30091013589166185429768791 45136520383749278144653187)
          ·
            refine ⟨67704780575623917216979781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45136520383749278144653187 67704780575623917216979781)
            ·
              refine ⟨12694646357929484478183709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67704780575623917216979781 12694646357929484478183709)
              ·
                refine ⟨4760492384223556679318891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12694646357929484478183709 4760492384223556679318891)
                ·
                  refine ⟨7140738576335335018978337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760492384223556679318891 7140738576335335018978337)
                  ·
                    refine ⟨5355553932251501264233753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7140738576335335018978337 5355553932251501264233753)
                    ·
                      refine ⟨4016665449188625948175315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355553932251501264233753 4016665449188625948175315)
                      ·
                        rfl

theorem cell23_7822428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7822428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822428 prefixEnd_7822428 := by exact prefixLift 7822428
  have htrace : WordTrace (prefixWord ++ tailWord_7822428) baseStart_7822428 baseEnd_7822428 := by
    simpa [prefixWord, tailWord_7822428, baseEnd_7822428] using wordTrace_append hprefix tailTrace_7822428
  have hstable : (prefixWord ++ tailWord_7822428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822428).length < 2 ^ (prefixWord ++ tailWord_7822428).sum := by decide
  have hdescent : baseEnd_7822428 < baseStart_7822428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822460 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_7822460 : Nat := 118140960795 + 7822460 * 2 ^ 59
def prefixEnd_7822460 : Nat := 4983230072969 + 3 ^ 40 * 7822460 * 2
def baseEnd_7822460 : Nat := 1338893960189856607658389

theorem tailTrace_7822460 : CollatzResearch.WordTrace tailWord_7822460 prefixEnd_7822460 1338893960189856607658389 := by
  unfold tailWord_7822460
  simp only [CollatzResearch.WordTrace]
  refine ⟨142654277620285432325560417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190205703493713909767413889 142654277620285432325560417)
  ·
    refine ⟨106990708215214074244170313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142654277620285432325560417 106990708215214074244170313)
    ·
      refine ⟨80243031161410555683127735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106990708215214074244170313 80243031161410555683127735)
      ·
        refine ⟨120364546742115833524691603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80243031161410555683127735 120364546742115833524691603)
        ·
          refine ⟨180546820113173750287037405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120364546742115833524691603 180546820113173750287037405)
          ·
            refine ⟨67705057542440156357639027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180546820113173750287037405 67705057542440156357639027)
            ·
              refine ⟨101557586313660234536458541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67705057542440156357639027 101557586313660234536458541)
              ·
                refine ⟨38084094867622587951171953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101557586313660234536458541 38084094867622587951171953)
                ·
                  refine ⟨28563071150716940963378965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38084094867622587951171953 28563071150716940963378965)
                  ·
                    refine ⟨1338893960189856607658389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28563071150716940963378965 1338893960189856607658389)
                    ·
                      rfl

theorem cell23_7822460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_7822460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822460 prefixEnd_7822460 := by exact prefixLift 7822460
  have htrace : WordTrace (prefixWord ++ tailWord_7822460) baseStart_7822460 baseEnd_7822460 := by
    simpa [prefixWord, tailWord_7822460, baseEnd_7822460] using wordTrace_append hprefix tailTrace_7822460
  have hstable : (prefixWord ++ tailWord_7822460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822460).length < 2 ^ (prefixWord ++ tailWord_7822460).sum := by decide
  have hdescent : baseEnd_7822460 < baseStart_7822460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822461 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_7822461 : Nat := 118140960795 + 7822461 * 2 ^ 59
def prefixEnd_7822461 : Nat := 4983230072969 + 3 ^ 40 * 7822461 * 2
def baseEnd_7822461 : Nat := 4016682394050224319062663

theorem tailTrace_7822461 : CollatzResearch.WordTrace tailWord_7822461 prefixEnd_7822461 4016682394050224319062663 := by
  unfold tailWord_7822461
  simp only [CollatzResearch.WordTrace]
  refine ⟨285308591713567241821907237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190205727809044827881271491 285308591713567241821907237)
  ·
    refine ⟨53495360946293857841607607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285308591713567241821907237 53495360946293857841607607)
    ·
      refine ⟨80243041419440786762411411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53495360946293857841607607 80243041419440786762411411)
      ·
        refine ⟨120364562129161180143617117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80243041419440786762411411 120364562129161180143617117)
        ·
          refine ⟨45136710798435442553856419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120364562129161180143617117 45136710798435442553856419)
          ·
            refine ⟨67705066197653163830784629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45136710798435442553856419 67705066197653163830784629)
            ·
              refine ⟨6347349956029984109136059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67705066197653163830784629 6347349956029984109136059)
              ·
                refine ⟨9521024934044976163704089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347349956029984109136059 9521024934044976163704089)
                ·
                  refine ⟨7140768700533732122778067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9521024934044976163704089 7140768700533732122778067)
                  ·
                    refine ⟨10711153050800598184167101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140768700533732122778067 10711153050800598184167101)
                    ·
                      refine ⟨4016682394050224319062663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711153050800598184167101 4016682394050224319062663)
                      ·
                        rfl

theorem cell23_7822461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_7822461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822461 prefixEnd_7822461 := by exact prefixLift 7822461
  have htrace : WordTrace (prefixWord ++ tailWord_7822461) baseStart_7822461 baseEnd_7822461 := by
    simpa [prefixWord, tailWord_7822461, baseEnd_7822461] using wordTrace_append hprefix tailTrace_7822461
  have hstable : (prefixWord ++ tailWord_7822461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822461).length < 2 ^ (prefixWord ++ tailWord_7822461).sum := by decide
  have hdescent : baseEnd_7822461 < baseStart_7822461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822480 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_7822480 : Nat := 118140960795 + 7822480 * 2 ^ 59
def prefixEnd_7822480 : Nat := 4983230072969 + 3 ^ 40 * 7822480 * 2
def baseEnd_7822480 : Nat := 4016692150182659744725075

theorem tailTrace_7822480 : CollatzResearch.WordTrace tailWord_7822480 prefixEnd_7822480 4016692150182659744725075 := by
  unfold tailWord_7822480
  simp only [CollatzResearch.WordTrace]
  refine ⟨142654642350249204033424447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190206189800332272044565929 142654642350249204033424447)
  ·
    refine ⟨213981963525373806050136671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142654642350249204033424447 213981963525373806050136671)
    ·
      refine ⟨320972945288060709075205007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213981963525373806050136671 320972945288060709075205007)
      ·
        refine ⟨481459417932091063612807511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320972945288060709075205007 481459417932091063612807511)
        ·
          refine ⟨722189126898136595419211267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481459417932091063612807511 722189126898136595419211267)
          ·
            refine ⟨1083283690347204893128816901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722189126898136595419211267 1083283690347204893128816901)
            ·
              refine ⟨203115691940100917461653169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1083283690347204893128816901 203115691940100917461653169)
              ·
                refine ⟨152336768955075688096239877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203115691940100917461653169 152336768955075688096239877)
                ·
                  refine ⟨28563144179076691518044977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152336768955075688096239877 28563144179076691518044977)
                  ·
                    refine ⟨21422358134307518638533733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28563144179076691518044977 21422358134307518638533733)
                    ·
                      refine ⟨4016692150182659744725075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21422358134307518638533733 4016692150182659744725075)
                      ·
                        rfl

theorem cell23_7822480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_7822480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822480 prefixEnd_7822480 := by exact prefixLift 7822480
  have htrace : WordTrace (prefixWord ++ tailWord_7822480) baseStart_7822480 baseEnd_7822480 := by
    simpa [prefixWord, tailWord_7822480, baseEnd_7822480] using wordTrace_append hprefix tailTrace_7822480
  have hstable : (prefixWord ++ tailWord_7822480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822480).length < 2 ^ (prefixWord ++ tailWord_7822480).sum := by decide
  have hdescent : baseEnd_7822480 < baseStart_7822480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822487 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7822487 : Nat := 118140960795 + 7822487 * 2 ^ 59
def prefixEnd_7822487 : Nat := 4983230072969 + 3 ^ 40 * 7822487 * 2
def baseEnd_7822487 : Nat := 4016695744547241217337543

theorem tailTrace_7822487 : CollatzResearch.WordTrace tailWord_7822487 prefixEnd_7822487 4016695744547241217337543 := by
  unfold tailWord_7822487
  simp only [CollatzResearch.WordTrace]
  refine ⟨285309540011473048262353715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190206360007648698841569143 285309540011473048262353715)
  ·
    refine ⟨427964310017209572393530573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285309540011473048262353715 427964310017209572393530573)
    ·
      refine ⟨160486616256453589647573965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427964310017209572393530573 160486616256453589647573965)
      ·
        refine ⟨60182481096170096117840237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160486616256453589647573965 60182481096170096117840237)
        ·
          refine ⟨22568430411063786044190089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60182481096170096117840237 22568430411063786044190089)
          ·
            refine ⟨16926322808297839533142567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22568430411063786044190089 16926322808297839533142567)
            ·
              refine ⟨25389484212446759299713851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926322808297839533142567 25389484212446759299713851)
              ·
                refine ⟨38084226318670138949570777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25389484212446759299713851 38084226318670138949570777)
                ·
                  refine ⟨28563169739002604212178083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38084226318670138949570777 28563169739002604212178083)
                  ·
                    refine ⟨42844754608503906318267125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28563169739002604212178083 42844754608503906318267125)
                    ·
                      refine ⟨4016695744547241217337543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42844754608503906318267125 4016695744547241217337543)
                      ·
                        rfl

theorem cell23_7822487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7822487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822487 prefixEnd_7822487 := by exact prefixLift 7822487
  have htrace : WordTrace (prefixWord ++ tailWord_7822487) baseStart_7822487 baseEnd_7822487 := by
    simpa [prefixWord, tailWord_7822487, baseEnd_7822487] using wordTrace_append hprefix tailTrace_7822487
  have hstable : (prefixWord ++ tailWord_7822487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822487).length < 2 ^ (prefixWord ++ tailWord_7822487).sum := by decide
  have hdescent : baseEnd_7822487 < baseStart_7822487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822520 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_7822520 : Nat := 118140960795 + 7822520 * 2 ^ 59
def prefixEnd_7822520 : Nat := 4983230072969 + 3 ^ 40 * 7822520 * 2
def baseEnd_7822520 : Nat := 1338904229802946529408297

theorem tailTrace_7822520 : CollatzResearch.WordTrace tailWord_7822520 prefixEnd_7822520 1338904229802946529408297 := by
  unfold tailWord_7822520
  simp only [CollatzResearch.WordTrace]
  refine ⟨142655371810176747449152507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190207162413568996598870009 142655371810176747449152507)
  ·
    refine ⟨213983057715265121173728761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142655371810176747449152507 213983057715265121173728761)
    ·
      refine ⟨160487293286448840880296571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213983057715265121173728761 160487293286448840880296571)
      ·
        refine ⟨240730939929673261320444857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160487293286448840880296571 240730939929673261320444857)
        ·
          refine ⟨180548204947254945990333643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240730939929673261320444857 180548204947254945990333643)
          ·
            refine ⟨270822307420882418985500465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180548204947254945990333643 270822307420882418985500465)
            ·
              refine ⟨203116730565661814239125349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270822307420882418985500465 203116730565661814239125349)
              ·
                refine ⟨38084386981061590169836003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203116730565661814239125349 38084386981061590169836003)
                ·
                  refine ⟨57126580471592385254754005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38084386981061590169836003 57126580471592385254754005)
                  ·
                    refine ⟨1338904229802946529408297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57126580471592385254754005 1338904229802946529408297)
                    ·
                      rfl

theorem cell23_7822520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_7822520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822520 prefixEnd_7822520 := by exact prefixLift 7822520
  have htrace : WordTrace (prefixWord ++ tailWord_7822520) baseStart_7822520 baseEnd_7822520 := by
    simpa [prefixWord, tailWord_7822520, baseEnd_7822520] using wordTrace_append hprefix tailTrace_7822520
  have hstable : (prefixWord ++ tailWord_7822520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822520).length < 2 ^ (prefixWord ++ tailWord_7822520).sum := by decide
  have hdescent : baseEnd_7822520 < baseStart_7822520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822574 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_7822574 : Nat := 118140960795 + 7822574 * 2 ^ 59
def prefixEnd_7822574 : Nat := 4983230072969 + 3 ^ 40 * 7822574 * 2
def baseEnd_7822574 : Nat := 4016740417364182376949643

theorem tailTrace_7822574 : CollatzResearch.WordTrace tailWord_7822574 prefixEnd_7822574 4016740417364182376949643 := by
  unfold tailWord_7822574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35664089145269732765096347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190208475441438574747180517 35664089145269732765096347)
  ·
    refine ⟨53496133717904599147644521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35664089145269732765096347 53496133717904599147644521)
    ·
      refine ⟨40122100288428449360733391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53496133717904599147644521 40122100288428449360733391)
      ·
        refine ⟨60183150432642674041100087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40122100288428449360733391 60183150432642674041100087)
        ·
          refine ⟨90274725648964011061650131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60183150432642674041100087 90274725648964011061650131)
          ·
            refine ⟨135412088473446016592475197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90274725648964011061650131 135412088473446016592475197)
            ·
              refine ⟨50779533177542256222178199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135412088473446016592475197 50779533177542256222178199)
              ·
                refine ⟨76169299766313384333267299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50779533177542256222178199 76169299766313384333267299)
                ·
                  refine ⟨114253949649470076499900949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76169299766313384333267299 114253949649470076499900949)
                  ·
                    refine ⟨5355653889818909835932857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114253949649470076499900949 5355653889818909835932857)
                    ·
                      refine ⟨4016740417364182376949643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355653889818909835932857 4016740417364182376949643)
                      ·
                        rfl

theorem cell23_7822574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_7822574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822574 prefixEnd_7822574 := by exact prefixLift 7822574
  have htrace : WordTrace (prefixWord ++ tailWord_7822574) baseStart_7822574 baseEnd_7822574 := by
    simpa [prefixWord, tailWord_7822574, baseEnd_7822574] using wordTrace_append hprefix tailTrace_7822574
  have hstable : (prefixWord ++ tailWord_7822574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822574).length < 2 ^ (prefixWord ++ tailWord_7822574).sum := by decide
  have hdescent : baseEnd_7822574 < baseStart_7822574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822577 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_7822577 : Nat := 118140960795 + 7822577 * 2 ^ 59
def prefixEnd_7822577 : Nat := 4983230072969 + 3 ^ 40 * 7822577 * 2
def baseEnd_7822577 : Nat := 4016741957806145865212129

theorem tailTrace_7822577 : CollatzResearch.WordTrace tailWord_7822577 prefixEnd_7822577 4016741957806145865212129 := by
  unfold tailWord_7822577
  simp only [CollatzResearch.WordTrace]
  refine ⟨285312822581146993633129985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190208548387431329088753323 285312822581146993633129985)
  ·
    refine ⟨213984616935860245224847489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285312822581146993633129985 213984616935860245224847489)
    ·
      refine ⟨160488462701895183918635617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213984616935860245224847489 160488462701895183918635617)
      ·
        refine ⟨120366347026421387938976713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160488462701895183918635617 120366347026421387938976713)
        ·
          refine ⟨90274760269816040954232535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120366347026421387938976713 90274760269816040954232535)
          ·
            refine ⟨135412140404724061431348803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90274760269816040954232535 135412140404724061431348803)
            ·
              refine ⟨203118210607086092147023205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135412140404724061431348803 203118210607086092147023205)
              ·
                refine ⟨38084664488828642277566851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203118210607086092147023205 38084664488828642277566851)
                ·
                  refine ⟨57126996733242963416350277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38084664488828642277566851 57126996733242963416350277)
                  ·
                    refine ⟨10711311887483055640565677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57126996733242963416350277 10711311887483055640565677)
                    ·
                      refine ⟨4016741957806145865212129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711311887483055640565677 4016741957806145865212129)
                      ·
                        rfl

theorem cell23_7822577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_7822577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822577 prefixEnd_7822577 := by exact prefixLift 7822577
  have htrace : WordTrace (prefixWord ++ tailWord_7822577) baseStart_7822577 baseEnd_7822577 := by
    simpa [prefixWord, tailWord_7822577, baseEnd_7822577] using wordTrace_append hprefix tailTrace_7822577
  have hstable : (prefixWord ++ tailWord_7822577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822577).length < 2 ^ (prefixWord ++ tailWord_7822577).sum := by decide
  have hdescent : baseEnd_7822577 < baseStart_7822577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822601 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 1, 4]
def baseStart_7822601 : Nat := 118140960795 + 7822601 * 2 ^ 59
def prefixEnd_7822601 : Nat := 4983230072969 + 3 ^ 40 * 7822601 * 2
def baseEnd_7822601 : Nat := 1338918093780617923770673

theorem tailTrace_7822601 : CollatzResearch.WordTrace tailWord_7822601 prefixEnd_7822601 1338918093780617923770673 := by
  unfold tailWord_7822601
  simp only [CollatzResearch.WordTrace]
  refine ⟨285313697933060045732003657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190209131955373363821335771 285313697933060045732003657)
  ·
    refine ⟨213985273449795034299002743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285313697933060045732003657 213985273449795034299002743)
    ·
      refine ⟨320977910174692551448504115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213985273449795034299002743 320977910174692551448504115)
      ·
        refine ⟨481466865262038827172756173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320977910174692551448504115 481466865262038827172756173)
        ·
          refine ⟨180550074473264560189783565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481466865262038827172756173 180550074473264560189783565)
          ·
            refine ⟨67706277927474210071168837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180550074473264560189783565 67706277927474210071168837)
            ·
              refine ⟨12694927111401414388344157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67706277927474210071168837 12694927111401414388344157)
              ·
                refine ⟨4760597666775530395629059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12694927111401414388344157 4760597666775530395629059)
                ·
                  refine ⟨7140896500163295593443589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760597666775530395629059 7140896500163295593443589)
                  ·
                    refine ⟨1338918093780617923770673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140896500163295593443589 1338918093780617923770673)
                    ·
                      rfl

theorem cell23_7822601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_7822601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822601 prefixEnd_7822601 := by exact prefixLift 7822601
  have htrace : WordTrace (prefixWord ++ tailWord_7822601) baseStart_7822601 baseEnd_7822601 := by
    simpa [prefixWord, tailWord_7822601, baseEnd_7822601] using wordTrace_append hprefix tailTrace_7822601
  have hstable : (prefixWord ++ tailWord_7822601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822601).length < 2 ^ (prefixWord ++ tailWord_7822601).sum := by decide
  have hdescent : baseEnd_7822601 < baseStart_7822601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822641 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_7822641 : Nat := 118140960795 + 7822641 * 2 ^ 59
def prefixEnd_7822641 : Nat := 4983230072969 + 3 ^ 40 * 7822641 * 2
def baseEnd_7822641 : Nat := 4016774820568033614811835

theorem tailTrace_7822641 : CollatzResearch.WordTrace tailWord_7822641 prefixEnd_7822641 4016774820568033614811835 := by
  unfold tailWord_7822641
  simp only [CollatzResearch.WordTrace]
  refine ⟨285315156852915132563459777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190210104568610088375639851 285315156852915132563459777)
  ·
    refine ⟨213986367639686349422594833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285315156852915132563459777 213986367639686349422594833)
    ·
      refine ⟨160489775729764762066946125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213986367639686349422594833 160489775729764762066946125)
      ·
        refine ⟨60183665898661785775104797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160489775729764762066946125 60183665898661785775104797)
        ·
          refine ⟨22568874711998169665664299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60183665898661785775104797 22568874711998169665664299)
          ·
            refine ⟨33853312067997254498496449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22568874711998169665664299 33853312067997254498496449)
            ·
              refine ⟨25389984050997940873872337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33853312067997254498496449 25389984050997940873872337)
              ·
                refine ⟨19042488038248455655404253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25389984050997940873872337 19042488038248455655404253)
                ·
                  refine ⟨7140933014343170870776595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19042488038248455655404253 7140933014343170870776595)
                  ·
                    refine ⟨10711399521514756306164893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140933014343170870776595 10711399521514756306164893)
                    ·
                      refine ⟨4016774820568033614811835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711399521514756306164893 4016774820568033614811835)
                      ·
                        rfl

theorem cell23_7822641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_7822641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822641 prefixEnd_7822641 := by exact prefixLift 7822641
  have htrace : WordTrace (prefixWord ++ tailWord_7822641) baseStart_7822641 baseEnd_7822641 := by
    simpa [prefixWord, tailWord_7822641, baseEnd_7822641] using wordTrace_append hprefix tailTrace_7822641
  have hstable : (prefixWord ++ tailWord_7822641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822641).length < 2 ^ (prefixWord ++ tailWord_7822641).sum := by decide
  have hdescent : baseEnd_7822641 < baseStart_7822641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822667 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3]
def baseStart_7822667 : Nat := 118140960795 + 7822667 * 2 ^ 59
def prefixEnd_7822667 : Nat := 4983230072969 + 3 ^ 40 * 7822667 * 2
def baseEnd_7822667 : Nat := 4016788171065050513086715

theorem tailTrace_7822667 : CollatzResearch.WordTrace tailWord_7822667 prefixEnd_7822667 4016788171065050513086715 := by
  unfold tailWord_7822667
  simp only [CollatzResearch.WordTrace]
  refine ⟨285316105150820939003906255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190210736767213959335937503 285316105150820939003906255)
  ·
    refine ⟨427974157726231408505859383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285316105150820939003906255 427974157726231408505859383)
    ·
      refine ⟨641961236589347112758789075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427974157726231408505859383 641961236589347112758789075)
      ·
        refine ⟨962941854884020669138183613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641961236589347112758789075 962941854884020669138183613)
        ·
          refine ⟨361103195581507750926818855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962941854884020669138183613 361103195581507750926818855)
          ·
            refine ⟨541654793372261626390228283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361103195581507750926818855 541654793372261626390228283)
            ·
              refine ⟨812482190058392439585342425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541654793372261626390228283 812482190058392439585342425)
              ·
                refine ⟨609361642543794329689006819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812482190058392439585342425 609361642543794329689006819)
                ·
                  refine ⟨914042463815691494533510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609361642543794329689006819 914042463815691494533510229)
                  ·
                    refine ⟨10711435122840134701564573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 914042463815691494533510229 10711435122840134701564573)
                    ·
                      refine ⟨4016788171065050513086715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711435122840134701564573 4016788171065050513086715)
                      ·
                        rfl

theorem cell23_7822667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].length) (baseStart_7822667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822667 prefixEnd_7822667 := by exact prefixLift 7822667
  have htrace : WordTrace (prefixWord ++ tailWord_7822667) baseStart_7822667 baseEnd_7822667 := by
    simpa [prefixWord, tailWord_7822667, baseEnd_7822667] using wordTrace_append hprefix tailTrace_7822667
  have hstable : (prefixWord ++ tailWord_7822667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822667).length < 2 ^ (prefixWord ++ tailWord_7822667).sum := by decide
  have hdescent : baseEnd_7822667 < baseStart_7822667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822691 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 2, 4]
def baseStart_7822691 : Nat := 118140960795 + 7822691 * 2 ^ 59
def prefixEnd_7822691 : Nat := 4983230072969 + 3 ^ 40 * 7822691 * 2
def baseEnd_7822691 : Nat := 1338933498200252806395535

theorem tailTrace_7822691 : CollatzResearch.WordTrace tailWord_7822691 prefixEnd_7822691 1338933498200252806395535 := by
  unfold tailWord_7822691
  simp only [CollatzResearch.WordTrace]
  refine ⟨285316980502733991102779927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190211320335155994068519951 285316980502733991102779927)
  ·
    refine ⟨427975470754100986654169891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285316980502733991102779927 427975470754100986654169891)
    ·
      refine ⟨641963206131151479981254837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427975470754100986654169891 641963206131151479981254837)
      ·
        refine ⟨60184050574795451248242641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 641963206131151479981254837 60184050574795451248242641)
        ·
          refine ⟨45138037931096588436181981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60184050574795451248242641 45138037931096588436181981)
          ·
            refine ⟨16926764224161220663568243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45138037931096588436181981 16926764224161220663568243)
            ·
              refine ⟨25390146336241830995352365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926764224161220663568243 25390146336241830995352365)
              ·
                refine ⟨9521304876090686623257137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25390146336241830995352365 9521304876090686623257137)
                ·
                  refine ⟨7140978657068014967442853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9521304876090686623257137 7140978657068014967442853)
                  ·
                    refine ⟨1338933498200252806395535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140978657068014967442853 1338933498200252806395535)
                    ·
                      rfl

theorem cell23_7822691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 4].length) (baseStart_7822691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822691 prefixEnd_7822691 := by exact prefixLift 7822691
  have htrace : WordTrace (prefixWord ++ tailWord_7822691) baseStart_7822691 baseEnd_7822691 := by
    simpa [prefixWord, tailWord_7822691, baseEnd_7822691] using wordTrace_append hprefix tailTrace_7822691
  have hstable : (prefixWord ++ tailWord_7822691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822691).length < 2 ^ (prefixWord ++ tailWord_7822691).sum := by decide
  have hdescent : baseEnd_7822691 < baseStart_7822691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822701 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_7822701 : Nat := 118140960795 + 7822701 * 2 ^ 59
def prefixEnd_7822701 : Nat := 4983230072969 + 3 ^ 40 * 7822701 * 2
def baseEnd_7822701 : Nat := 4016805629407303380061559

theorem tailTrace_7822701 : CollatzResearch.WordTrace tailWord_7822701 prefixEnd_7822701 4016805629407303380061559 := by
  unfold tailWord_7822701
  simp only [CollatzResearch.WordTrace]
  refine ⟨285317345232697762810643957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190211563488465175207095971 285317345232697762810643957)
  ·
    refine ⟨26748501115565415263497871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285317345232697762810643957 26748501115565415263497871)
    ·
      refine ⟨40122751673348122895246807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26748501115565415263497871 40122751673348122895246807)
      ·
        refine ⟨60184127510022184342870211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40122751673348122895246807 60184127510022184342870211)
        ·
          refine ⟨90276191265033276514305317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60184127510022184342870211 90276191265033276514305317)
          ·
            refine ⟨16926785862193739346432247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90276191265033276514305317 16926785862193739346432247)
            ·
              refine ⟨25390178793290609019648371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926785862193739346432247 25390178793290609019648371)
              ·
                refine ⟨38085268189935913529472557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25390178793290609019648371 38085268189935913529472557)
                ·
                  refine ⟨14281975571225967573552209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38085268189935913529472557 14281975571225967573552209)
                  ·
                    refine ⟨10711481678419475680164157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14281975571225967573552209 10711481678419475680164157)
                    ·
                      refine ⟨4016805629407303380061559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711481678419475680164157 4016805629407303380061559)
                      ·
                        rfl

theorem cell23_7822701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_7822701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822701 prefixEnd_7822701 := by exact prefixLift 7822701
  have htrace : WordTrace (prefixWord ++ tailWord_7822701) baseStart_7822701 baseEnd_7822701 := by
    simpa [prefixWord, tailWord_7822701, baseEnd_7822701] using wordTrace_append hprefix tailTrace_7822701
  have hstable : (prefixWord ++ tailWord_7822701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822701).length < 2 ^ (prefixWord ++ tailWord_7822701).sum := by decide
  have hdescent : baseEnd_7822701 < baseStart_7822701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822714 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_7822714 : Nat := 118140960795 + 7822714 * 2 ^ 59
def prefixEnd_7822714 : Nat := 4983230072969 + 3 ^ 40 * 7822714 * 2
def baseEnd_7822714 : Nat := 4016812304655811829198999

theorem tailTrace_7822714 : CollatzResearch.WordTrace tailWord_7822714 prefixEnd_7822714 4016812304655811829198999 := by
  unfold tailWord_7822714
  simp only [CollatzResearch.WordTrace]
  refine ⟨71329454845412666507716799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190211879587767110687244797 71329454845412666507716799)
  ·
    refine ⟨106994182268118999761575199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71329454845412666507716799 106994182268118999761575199)
    ·
      refine ⟨160491273402178499642362799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106994182268118999761575199 160491273402178499642362799)
      ·
        refine ⟨240736910103267749463544199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160491273402178499642362799 240736910103267749463544199)
        ·
          refine ⟨361105365154901624195316299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240736910103267749463544199 361105365154901624195316299)
          ·
            refine ⟨541658047732352436292974449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361105365154901624195316299 541658047732352436292974449)
            ·
              refine ⟨406243535799264327219730837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541658047732352436292974449 406243535799264327219730837)
              ·
                refine ⟨19042665740590515338424883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406243535799264327219730837 19042665740590515338424883)
                ·
                  refine ⟨28563998610885773007637325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19042665740590515338424883 28563998610885773007637325)
                  ·
                    refine ⟨10711499479082164877863997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28563998610885773007637325 10711499479082164877863997)
                    ·
                      refine ⟨4016812304655811829198999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711499479082164877863997 4016812304655811829198999)
                      ·
                        rfl

theorem cell23_7822714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_7822714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822714 prefixEnd_7822714 := by exact prefixLift 7822714
  have htrace : WordTrace (prefixWord ++ tailWord_7822714) baseStart_7822714 baseEnd_7822714 := by
    simpa [prefixWord, tailWord_7822714, baseEnd_7822714] using wordTrace_append hprefix tailTrace_7822714
  have hstable : (prefixWord ++ tailWord_7822714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822714).length < 2 ^ (prefixWord ++ tailWord_7822714).sum := by decide
  have hdescent : baseEnd_7822714 < baseStart_7822714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822738 : List Nat := [3, 2, 3, 3, 1, 2, 1, 8]
def baseStart_7822738 : Nat := 118140960795 + 7822738 * 2 ^ 59
def prefixEnd_7822738 : Nat := 4983230072969 + 3 ^ 40 * 7822738 * 2
def baseEnd_7822738 : Nat := 148771282525611842048107

theorem tailTrace_7822738 : CollatzResearch.WordTrace tailWord_7822738 prefixEnd_7822738 148771282525611842048107 := by
  unfold tailWord_7822738
  simp only [CollatzResearch.WordTrace]
  refine ⟨71329673683390929532435217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190212463155709145419827245 71329673683390929532435217)
  ·
    refine ⟨53497255262543197149326413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71329673683390929532435217 53497255262543197149326413)
    ·
      refine ⟨20061470723453698930997405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53497255262543197149326413 20061470723453698930997405)
      ·
        refine ⟨7523051521295137099124027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20061470723453698930997405 7523051521295137099124027)
        ·
          refine ⟨11284577281942705648686041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523051521295137099124027 11284577281942705648686041)
          ·
            refine ⟨8463432961457029236514531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284577281942705648686041 8463432961457029236514531)
            ·
              refine ⟨12695149442185543854771797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463432961457029236514531 12695149442185543854771797)
              ·
                refine ⟨148771282525611842048107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12695149442185543854771797 148771282525611842048107)
                ·
                  rfl

theorem cell23_7822738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_7822738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822738 prefixEnd_7822738 := by exact prefixLift 7822738
  have htrace : WordTrace (prefixWord ++ tailWord_7822738) baseStart_7822738 baseEnd_7822738 := by
    simpa [prefixWord, tailWord_7822738, baseEnd_7822738] using wordTrace_append hprefix tailTrace_7822738
  have hstable : (prefixWord ++ tailWord_7822738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822738).length < 2 ^ (prefixWord ++ tailWord_7822738).sum := by decide
  have hdescent : baseEnd_7822738 < baseStart_7822738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822741 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_7822741 : Nat := 118140960795 + 7822741 * 2 ^ 59
def prefixEnd_7822741 : Nat := 4983230072969 + 3 ^ 40 * 7822741 * 2
def baseEnd_7822741 : Nat := 4016826168633483223561375

theorem tailTrace_7822741 : CollatzResearch.WordTrace tailWord_7822741 prefixEnd_7822741 4016826168633483223561375 := by
  unfold tailWord_7822741
  simp only [CollatzResearch.WordTrace]
  refine ⟨285318804152552849642100077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190212536101701899761400051 285318804152552849642100077)
  ·
    refine ⟨106994551557207318615787529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285318804152552849642100077 106994551557207318615787529)
    ·
      refine ⟨80245913667905488961840647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106994551557207318615787529 80245913667905488961840647)
      ·
        refine ⟨120368870501858233442760971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80245913667905488961840647 120368870501858233442760971)
        ·
          refine ⟨180553305752787350164141457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120368870501858233442760971 180553305752787350164141457)
          ·
            refine ⟨135414979314590512623106093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180553305752787350164141457 135414979314590512623106093)
            ·
              refine ⟨50780617242971442233664785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135414979314590512623106093 50780617242971442233664785)
              ·
                refine ⟨38085462932228581675248589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50780617242971442233664785 38085462932228581675248589)
                ·
                  refine ⟨14282048599585718128218221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38085462932228581675248589 14282048599585718128218221)
                  ·
                    refine ⟨5355768224844644298081833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14282048599585718128218221 5355768224844644298081833)
                    ·
                      refine ⟨4016826168633483223561375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355768224844644298081833 4016826168633483223561375)
                      ·
                        rfl

theorem cell23_7822741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_7822741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822741 prefixEnd_7822741 := by exact prefixLift 7822741
  have htrace : WordTrace (prefixWord ++ tailWord_7822741) baseStart_7822741 baseEnd_7822741 := by
    simpa [prefixWord, tailWord_7822741, baseEnd_7822741] using wordTrace_append hprefix tailTrace_7822741
  have hstable : (prefixWord ++ tailWord_7822741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822741).length < 2 ^ (prefixWord ++ tailWord_7822741).sum := by decide
  have hdescent : baseEnd_7822741 < baseStart_7822741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822747 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 6]
def baseStart_7822747 : Nat := 118140960795 + 7822747 * 2 ^ 59
def prefixEnd_7822747 : Nat := 4983230072969 + 3 ^ 40 * 7822747 * 2
def baseEnd_7822747 : Nat := 1338943083172470066695449

theorem tailTrace_7822747 : CollatzResearch.WordTrace tailWord_7822747 prefixEnd_7822747 1338943083172470066695449 := by
  unfold tailWord_7822747
  simp only [CollatzResearch.WordTrace]
  refine ⟨285319022990531112666818495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190212681993687408444545663 285319022990531112666818495)
  ·
    refine ⟨427978534485796669000227743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285319022990531112666818495 427978534485796669000227743)
    ·
      refine ⟨641967801728695003500341615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427978534485796669000227743 641967801728695003500341615)
      ·
        refine ⟨962951702593042505250512423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641967801728695003500341615 962951702593042505250512423)
        ·
          refine ⟨1444427553889563757875768635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962951702593042505250512423 1444427553889563757875768635)
          ·
            refine ⟨2166641330834345636813652953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444427553889563757875768635 2166641330834345636813652953)
            ·
              refine ⟨1624980998125759227610239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166641330834345636813652953 1624980998125759227610239715)
              ·
                refine ⟨2437471497188638841415359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624980998125759227610239715 2437471497188638841415359573)
                ·
                  refine ⟨28564119107679361422836245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2437471497188638841415359573 28564119107679361422836245)
                  ·
                    refine ⟨1338943083172470066695449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28564119107679361422836245 1338943083172470066695449)
                    ·
                      rfl

theorem cell23_7822747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_7822747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822747 prefixEnd_7822747 := by exact prefixLift 7822747
  have htrace : WordTrace (prefixWord ++ tailWord_7822747) baseStart_7822747 baseEnd_7822747 := by
    simpa [prefixWord, tailWord_7822747, baseEnd_7822747] using wordTrace_append hprefix tailTrace_7822747
  have hstable : (prefixWord ++ tailWord_7822747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822747).length < 2 ^ (prefixWord ++ tailWord_7822747).sum := by decide
  have hdescent : baseEnd_7822747 < baseStart_7822747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822784 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_7822784 : Nat := 118140960795 + 7822784 * 2 ^ 59
def prefixEnd_7822784 : Nat := 4983230072969 + 3 ^ 40 * 7822784 * 2
def baseEnd_7822784 : Nat := 4016848248301626555323677

theorem tailTrace_7822784 : CollatzResearch.WordTrace tailWord_7822784 prefixEnd_7822784 4016848248301626555323677 := by
  unfold tailWord_7822784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142660186245698533992957703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190213581660931378657276937 142660186245698533992957703)
  ·
    refine ⟨213990279368547800989436555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142660186245698533992957703 213990279368547800989436555)
    ·
      refine ⟨320985419052821701484154833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213990279368547800989436555 320985419052821701484154833)
      ·
        refine ⟨240739064289616276113116125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320985419052821701484154833 240739064289616276113116125)
        ·
          refine ⟨90277149108606103542418547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240739064289616276113116125 90277149108606103542418547)
          ·
            refine ⟨135415723662909155313627821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90277149108606103542418547 135415723662909155313627821)
            ·
              refine ⟨50780896373590933242610433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135415723662909155313627821 50780896373590933242610433)
              ·
                refine ⟨38085672280193199931957825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50780896373590933242610433 38085672280193199931957825)
                ·
                  refine ⟨28564254210144899948968369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38085672280193199931957825 28564254210144899948968369)
                  ·
                    refine ⟨21423190657608674961726277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28564254210144899948968369 21423190657608674961726277)
                    ·
                      refine ⟨4016848248301626555323677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21423190657608674961726277 4016848248301626555323677)
                      ·
                        rfl

theorem cell23_7822784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_7822784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822784 prefixEnd_7822784 := by exact prefixLift 7822784
  have htrace : WordTrace (prefixWord ++ tailWord_7822784) baseStart_7822784 baseEnd_7822784 := by
    simpa [prefixWord, tailWord_7822784, baseEnd_7822784] using wordTrace_append hprefix tailTrace_7822784
  have hstable : (prefixWord ++ tailWord_7822784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822784).length < 2 ^ (prefixWord ++ tailWord_7822784).sum := by decide
  have hdescent : baseEnd_7822784 < baseStart_7822784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822794 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_7822794 : Nat := 118140960795 + 7822794 * 2 ^ 59
def prefixEnd_7822794 : Nat := 4983230072969 + 3 ^ 40 * 7822794 * 2
def baseEnd_7822794 : Nat := 446317042567574612910959

theorem tailTrace_7822794 : CollatzResearch.WordTrace tailWord_7822794 prefixEnd_7822794 446317042567574612910959 := by
  unfold tailWord_7822794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71330184305340209923444859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190213824814240559795852957 71330184305340209923444859)
  ·
    refine ⟨106995276458010314885167289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71330184305340209923444859 106995276458010314885167289)
    ·
      refine ⟨80246457343507736163875467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106995276458010314885167289 80246457343507736163875467)
      ·
        refine ⟨120369686015261604245813201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80246457343507736163875467 120369686015261604245813201)
        ·
          refine ⟨90277264511446203184359901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120369686015261604245813201 90277264511446203184359901)
          ·
            refine ⟨33853974191792326194134963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90277264511446203184359901 33853974191792326194134963)
            ·
              refine ⟨50780961287688489291202445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33853974191792326194134963 50780961287688489291202445)
              ·
                refine ⟨19042860482883183484200917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50780961287688489291202445 19042860482883183484200917)
                ·
                  refine ⟨446317042567574612910959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19042860482883183484200917 446317042567574612910959)
                  ·
                    rfl

theorem cell23_7822794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_7822794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822794 prefixEnd_7822794 := by exact prefixLift 7822794
  have htrace : WordTrace (prefixWord ++ tailWord_7822794) baseStart_7822794 baseEnd_7822794 := by
    simpa [prefixWord, tailWord_7822794, baseEnd_7822794] using wordTrace_append hprefix tailTrace_7822794
  have hstable : (prefixWord ++ tailWord_7822794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822794).length < 2 ^ (prefixWord ++ tailWord_7822794).sum := by decide
  have hdescent : baseEnd_7822794 < baseStart_7822794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822824 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_7822824 : Nat := 118140960795 + 7822824 * 2 ^ 59
def prefixEnd_7822824 : Nat := 4983230072969 + 3 ^ 40 * 7822824 * 2
def baseEnd_7822824 : Nat := 1338956262509268799607831

theorem tailTrace_7822824 : CollatzResearch.WordTrace tailWord_7822824 prefixEnd_7822824 1338956262509268799607831 := by
  unfold tailWord_7822824
  simp only [CollatzResearch.WordTrace]
  refine ⟨142660915705626077408685763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190214554274168103211581017 142660915705626077408685763)
  ·
    refine ⟨213991373558439116113028645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142660915705626077408685763 213991373558439116113028645)
    ·
      refine ⟨40123382542207334271192871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213991373558439116113028645 40123382542207334271192871)
      ·
        refine ⟨60185073813311001406789307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40123382542207334271192871 60185073813311001406789307)
        ·
          refine ⟨90277610719966502110183961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60185073813311001406789307 90277610719966502110183961)
          ·
            refine ⟨67708208039974876582637971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90277610719966502110183961 67708208039974876582637971)
            ·
              refine ⟨101562312059962314873956957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67708208039974876582637971 101562312059962314873956957)
              ·
                refine ⟨38085867022485868077733859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101562312059962314873956957 38085867022485868077733859)
                ·
                  refine ⟨57128800533728802116600789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38085867022485868077733859 57128800533728802116600789)
                  ·
                    refine ⟨1338956262509268799607831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57128800533728802116600789 1338956262509268799607831)
                    ·
                      rfl

theorem cell23_7822824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_7822824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822824 prefixEnd_7822824 := by exact prefixLift 7822824
  have htrace : WordTrace (prefixWord ++ tailWord_7822824) baseStart_7822824 baseEnd_7822824 := by
    simpa [prefixWord, tailWord_7822824, baseEnd_7822824] using wordTrace_append hprefix tailTrace_7822824
  have hstable : (prefixWord ++ tailWord_7822824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822824).length < 2 ^ (prefixWord ++ tailWord_7822824).sum := by decide
  have hdescent : baseEnd_7822824 < baseStart_7822824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822874 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7822874 : Nat := 118140960795 + 7822874 * 2 ^ 59
def prefixEnd_7822874 : Nat := 4983230072969 + 3 ^ 40 * 7822874 * 2
def baseEnd_7822874 : Nat := 4016894461560531203198263

theorem tailTrace_7822874 : CollatzResearch.WordTrace tailWord_7822874 prefixEnd_7822874 4016894461560531203198263 := by
  unfold tailWord_7822874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71330913765267753339172919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190215770040714008904461117 71330913765267753339172919)
  ·
    refine ⟨106996370647901630008759379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71330913765267753339172919 106996370647901630008759379)
    ·
      refine ⟨160494555971852445013139069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106996370647901630008759379 160494555971852445013139069)
      ·
        refine ⟨60185458489444666879927151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160494555971852445013139069 60185458489444666879927151)
        ·
          refine ⟨90278187734167000319890727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60185458489444666879927151 90278187734167000319890727)
          ·
            refine ⟨135417281601250500479836091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90278187734167000319890727 135417281601250500479836091)
            ·
              refine ⟨203125922401875750719754137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135417281601250500479836091 203125922401875750719754137)
              ·
                refine ⟨152344441801406813039815603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203125922401875750719754137 152344441801406813039815603)
                ·
                  refine ⟨228516662702110219559723405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152344441801406813039815603 228516662702110219559723405)
                  ·
                    refine ⟨85693748513291332334896277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228516662702110219559723405 85693748513291332334896277)
                    ·
                      refine ⟨4016894461560531203198263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85693748513291332334896277 4016894461560531203198263)
                      ·
                        rfl

theorem cell23_7822874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7822874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822874 prefixEnd_7822874 := by exact prefixLift 7822874
  have htrace : WordTrace (prefixWord ++ tailWord_7822874) baseStart_7822874 baseEnd_7822874 := by
    simpa [prefixWord, tailWord_7822874, baseEnd_7822874] using wordTrace_append hprefix tailTrace_7822874
  have hstable : (prefixWord ++ tailWord_7822874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822874).length < 2 ^ (prefixWord ++ tailWord_7822874).sum := by decide
  have hdescent : baseEnd_7822874 < baseStart_7822874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822901 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 6]
def baseStart_7822901 : Nat := 118140960795 + 7822901 * 2 ^ 59
def prefixEnd_7822901 : Nat := 4983230072969 + 3 ^ 40 * 7822901 * 2
def baseEnd_7822901 : Nat := 446323147282022510840071

theorem tailTrace_7822901 : CollatzResearch.WordTrace tailWord_7822901 prefixEnd_7822901 446323147282022510840071 := by
  unfold tailWord_7822901
  simp only [CollatzResearch.WordTrace]
  refine ⟨285324639831973196967924557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190216426554648797978616371 285324639831973196967924557)
  ·
    refine ⟨106996739936989948862971709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285324639831973196967924557 106996739936989948862971709)
    ·
      refine ⟨40123777476371230823614391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106996739936989948862971709 40123777476371230823614391)
      ·
        refine ⟨60185666214556846235421587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40123777476371230823614391 60185666214556846235421587)
        ·
          refine ⟨90278499321835269353132381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60185666214556846235421587 90278499321835269353132381)
          ·
            refine ⟨33854437245688226007424643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90278499321835269353132381 33854437245688226007424643)
            ·
              refine ⟨50781655868532339011136965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33854437245688226007424643 50781655868532339011136965)
              ·
                refine ⟨9521560475349813564588181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50781655868532339011136965 9521560475349813564588181)
                ·
                  refine ⟨446323147282022510840071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9521560475349813564588181 446323147282022510840071)
                  ·
                    rfl

theorem cell23_7822901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_7822901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822901 prefixEnd_7822901 := by exact prefixLift 7822901
  have htrace : WordTrace (prefixWord ++ tailWord_7822901) baseStart_7822901 baseEnd_7822901 := by
    simpa [prefixWord, tailWord_7822901, baseEnd_7822901] using wordTrace_append hprefix tailTrace_7822901
  have hstable : (prefixWord ++ tailWord_7822901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822901).length < 2 ^ (prefixWord ++ tailWord_7822901).sum := by decide
  have hdescent : baseEnd_7822901 < baseStart_7822901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822905 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 1, 4]
def baseStart_7822905 : Nat := 118140960795 + 7822905 * 2 ^ 59
def prefixEnd_7822905 : Nat := 4983230072969 + 3 ^ 40 * 7822905 * 2
def baseEnd_7822905 : Nat := 1338970126486940193970207

theorem tailTrace_7822905 : CollatzResearch.WordTrace tailWord_7822905 prefixEnd_7822905 1338970126486940193970207 := by
  unfold tailWord_7822905
  simp only [CollatzResearch.WordTrace]
  refine ⟨285324785723958705651070169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190216523815972470434046779 285324785723958705651070169)
  ·
    refine ⟨213993589292969029238302627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285324785723958705651070169 213993589292969029238302627)
    ·
      refine ⟨320990383939453543857453941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213993589292969029238302627 320990383939453543857453941)
      ·
        refine ⟨30092848494323769736636307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320990383939453543857453941 30092848494323769736636307)
        ·
          refine ⟨45139272741485654604954461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30092848494323769736636307 45139272741485654604954461)
          ·
            refine ⟨16927227278057120476857923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45139272741485654604954461 16927227278057120476857923)
            ·
              refine ⟨25390840917085680715286885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16927227278057120476857923 25390840917085680715286885)
              ·
                refine ⟨4760782671953565134116291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25390840917085680715286885 4760782671953565134116291)
                ·
                  refine ⟨7141174007930347701174437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760782671953565134116291 7141174007930347701174437)
                  ·
                    refine ⟨1338970126486940193970207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141174007930347701174437 1338970126486940193970207)
                    ·
                      rfl

theorem cell23_7822905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_7822905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822905 prefixEnd_7822905 := by exact prefixLift 7822905
  have htrace : WordTrace (prefixWord ++ tailWord_7822905) baseStart_7822905 baseEnd_7822905 := by
    simpa [prefixWord, tailWord_7822905, baseEnd_7822905] using wordTrace_append hprefix tailTrace_7822905
  have hstable : (prefixWord ++ tailWord_7822905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822905).length < 2 ^ (prefixWord ++ tailWord_7822905).sum := by decide
  have hdescent : baseEnd_7822905 < baseStart_7822905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822928 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_7822928 : Nat := 118140960795 + 7822928 * 2 ^ 59
def prefixEnd_7822928 : Nat := 4983230072969 + 3 ^ 40 * 7822928 * 2
def baseEnd_7822928 : Nat := 4016922189515873991923015

theorem tailTrace_7822928 : CollatzResearch.WordTrace tailWord_7822928 prefixEnd_7822928 4016922189515873991923015 := by
  unfold tailWord_7822928
  simp only [CollatzResearch.WordTrace]
  refine ⟨142662812301437690289578719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190217083068583587052771625 142662812301437690289578719)
  ·
    refine ⟨213994218452156535434368079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142662812301437690289578719 213994218452156535434368079)
    ·
      refine ⟨320991327678234803151552119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213994218452156535434368079 320991327678234803151552119)
      ·
        refine ⟨481486991517352204727328179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320991327678234803151552119 481486991517352204727328179)
        ·
          refine ⟨722230487276028307090992269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481486991517352204727328179 722230487276028307090992269)
          ·
            refine ⟨270836432728510615159122101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722230487276028307090992269 270836432728510615159122101)
            ·
              refine ⟨25390915568297870171167697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270836432728510615159122101 25390915568297870171167697)
              ·
                refine ⟨19043186676223402628375773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25390915568297870171167697 19043186676223402628375773)
                ·
                  refine ⟨7141195003583775985640915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19043186676223402628375773 7141195003583775985640915)
                  ·
                    refine ⟨10711792505375663978461373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7141195003583775985640915 10711792505375663978461373)
                    ·
                      refine ⟨4016922189515873991923015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711792505375663978461373 4016922189515873991923015)
                      ·
                        rfl

theorem cell23_7822928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_7822928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822928 prefixEnd_7822928 := by exact prefixLift 7822928
  have htrace : WordTrace (prefixWord ++ tailWord_7822928) baseStart_7822928 baseEnd_7822928 := by
    simpa [prefixWord, tailWord_7822928, baseEnd_7822928] using wordTrace_append hprefix tailTrace_7822928
  have hstable : (prefixWord ++ tailWord_7822928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822928).length < 2 ^ (prefixWord ++ tailWord_7822928).sum := by decide
  have hdescent : baseEnd_7822928 < baseStart_7822928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822948 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_7822948 : Nat := 118140960795 + 7822948 * 2 ^ 59
def prefixEnd_7822948 : Nat := 4983230072969 + 3 ^ 40 * 7822948 * 2
def baseEnd_7822948 : Nat := 1338977486376321304557641

theorem tailTrace_7822948 : CollatzResearch.WordTrace tailWord_7822948 prefixEnd_7822948 1338977486376321304557641 := by
  unfold tailWord_7822948
  simp only [CollatzResearch.WordTrace]
  refine ⟨142663177031401461997442749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190217569375201949329923665 142663177031401461997442749)
  ·
    refine ⟨53498691386775548249041031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142663177031401461997442749 53498691386775548249041031)
    ·
      refine ⟨80248037080163322373561547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53498691386775548249041031 80248037080163322373561547)
      ·
        refine ⟨120372055620244983560342321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80248037080163322373561547 120372055620244983560342321)
        ·
          refine ⟨90279041715183737670256741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120372055620244983560342321 90279041715183737670256741)
          ·
            refine ⟨16927320321596950813173139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90279041715183737670256741 16927320321596950813173139)
            ·
              refine ⟨25390980482395426219759709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16927320321596950813173139 25390980482395426219759709)
              ·
                refine ⟨9521617680898284832409891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25390980482395426219759709 9521617680898284832409891)
                ·
                  refine ⟨14282426521347427248614837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9521617680898284832409891 14282426521347427248614837)
                  ·
                    refine ⟨1338977486376321304557641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14282426521347427248614837 1338977486376321304557641)
                    ·
                      rfl

theorem cell23_7822948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_7822948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822948 prefixEnd_7822948 := by exact prefixLift 7822948
  have htrace : WordTrace (prefixWord ++ tailWord_7822948) baseStart_7822948 baseEnd_7822948 := by
    simpa [prefixWord, tailWord_7822948, baseEnd_7822948] using wordTrace_append hprefix tailTrace_7822948
  have hstable : (prefixWord ++ tailWord_7822948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822948).length < 2 ^ (prefixWord ++ tailWord_7822948).sum := by decide
  have hdescent : baseEnd_7822948 < baseStart_7822948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822962 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_7822962 : Nat := 118140960795 + 7822962 * 2 ^ 59
def prefixEnd_7822962 : Nat := 4983230072969 + 3 ^ 40 * 7822962 * 2
def baseEnd_7822962 : Nat := 4016939647858126858897859

theorem tailTrace_7822962 : CollatzResearch.WordTrace tailWord_7822962 prefixEnd_7822962 4016939647858126858897859 := by
  unfold tailWord_7822962
  simp only [CollatzResearch.WordTrace]
  refine ⟨71331716171188051096473785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190217909789834802923930093 71331716171188051096473785)
  ·
    refine ⟨53498787128391038322355339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71331716171188051096473785 53498787128391038322355339)
    ·
      refine ⟨80248180692586557483533009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53498787128391038322355339 80248180692586557483533009)
      ·
        refine ⟨60186135519439918112649757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80248180692586557483533009 60186135519439918112649757)
        ·
          refine ⟨22569800819789969292243659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60186135519439918112649757 22569800819789969292243659)
          ·
            refine ⟨33854701229684953938365489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22569800819789969292243659 33854701229684953938365489)
            ·
              refine ⟨25391025922263715453774117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33854701229684953938365489 25391025922263715453774117)
              ·
                refine ⟨4760817360424446647582647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25391025922263715453774117 4760817360424446647582647)
                ·
                  refine ⟨7141226040636669971373971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760817360424446647582647 7141226040636669971373971)
                  ·
                    refine ⟨10711839060955004957060957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7141226040636669971373971 10711839060955004957060957)
                    ·
                      refine ⟨4016939647858126858897859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711839060955004957060957 4016939647858126858897859)
                      ·
                        rfl

theorem cell23_7822962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_7822962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822962 prefixEnd_7822962 := by exact prefixLift 7822962
  have htrace : WordTrace (prefixWord ++ tailWord_7822962) baseStart_7822962 baseEnd_7822962 := by
    simpa [prefixWord, tailWord_7822962, baseEnd_7822962] using wordTrace_append hprefix tailTrace_7822962
  have hstable : (prefixWord ++ tailWord_7822962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822962).length < 2 ^ (prefixWord ++ tailWord_7822962).sum := by decide
  have hdescent : baseEnd_7822962 < baseStart_7822962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822971 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_7822971 : Nat := 118140960795 + 7822971 * 2 ^ 59
def prefixEnd_7822971 : Nat := 4983230072969 + 3 ^ 40 * 7822971 * 2
def baseEnd_7822971 : Nat := 4016944269184017323685317

theorem tailTrace_7822971 : CollatzResearch.WordTrace tailWord_7822971 prefixEnd_7822971 4016944269184017323685317 := by
  unfold tailWord_7822971
  simp only [CollatzResearch.WordTrace]
  refine ⟨285327192941719598922972767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190218128627813065948648511 285327192941719598922972767)
  ·
    refine ⟨427990789412579398384459151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285327192941719598922972767 427990789412579398384459151)
    ·
      refine ⟨641986184118869097576688727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427990789412579398384459151 641986184118869097576688727)
      ·
        refine ⟨962979276178303646365033091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641986184118869097576688727 962979276178303646365033091)
        ·
          refine ⟨1444468914267455469547549637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962979276178303646365033091 1444468914267455469547549637)
          ·
            refine ⟨270837921425147900540165557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1444468914267455469547549637 270837921425147900540165557)
            ·
              refine ⟨25391055133607615675640521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270837921425147900540165557 25391055133607615675640521)
              ·
                refine ⟨19043291350205711756730391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25391055133607615675640521 19043291350205711756730391)
                ·
                  refine ⟨28564937025308567635095587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19043291350205711756730391 28564937025308567635095587)
                  ·
                    refine ⟨42847405537962851452643381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28564937025308567635095587 42847405537962851452643381)
                    ·
                      refine ⟨4016944269184017323685317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42847405537962851452643381 4016944269184017323685317)
                      ·
                        rfl

theorem cell23_7822971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_7822971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822971 prefixEnd_7822971 := by exact prefixLift 7822971
  have htrace : WordTrace (prefixWord ++ tailWord_7822971) baseStart_7822971 baseEnd_7822971 := by
    simpa [prefixWord, tailWord_7822971, baseEnd_7822971] using wordTrace_append hprefix tailTrace_7822971
  have hstable : (prefixWord ++ tailWord_7822971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822971).length < 2 ^ (prefixWord ++ tailWord_7822971).sum := by decide
  have hdescent : baseEnd_7822971 < baseStart_7822971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822981 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_7822981 : Nat := 118140960795 + 7822981 * 2 ^ 59
def prefixEnd_7822981 : Nat := 4983230072969 + 3 ^ 40 * 7822981 * 2
def baseEnd_7822981 : Nat := 4016949403990562284560271

theorem tailTrace_7822981 : CollatzResearch.WordTrace tailWord_7822981 prefixEnd_7822981 4016949403990562284560271 := by
  unfold tailWord_7822981
  simp only [CollatzResearch.WordTrace]
  refine ⟨285327557671683370630836797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190218371781122247087224531 285327557671683370630836797)
  ·
    refine ⟨106997834126881263986563799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285327557671683370630836797 106997834126881263986563799)
    ·
      refine ⟨160496751190321895979845699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106997834126881263986563799 160496751190321895979845699)
      ·
        refine ⟨240745126785482843969768549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160496751190321895979845699 240745126785482843969768549)
        ·
          refine ⟨45139711272278033244331603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240745126785482843969768549 45139711272278033244331603)
          ·
            refine ⟨67709566908417049866497405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45139711272278033244331603 67709566908417049866497405)
            ·
              refine ⟨25391087590656393699936527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67709566908417049866497405 25391087590656393699936527)
              ·
                refine ⟨38086631385984590549904791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25391087590656393699936527 38086631385984590549904791)
                ·
                  refine ⟨57129947078976885824857187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38086631385984590549904791 57129947078976885824857187)
                  ·
                    refine ⟨85694920618465328737285781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57129947078976885824857187 85694920618465328737285781)
                    ·
                      refine ⟨4016949403990562284560271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85694920618465328737285781 4016949403990562284560271)
                      ·
                        rfl

theorem cell23_7822981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_7822981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822981 prefixEnd_7822981 := by exact prefixLift 7822981
  have htrace : WordTrace (prefixWord ++ tailWord_7822981) baseStart_7822981 baseEnd_7822981 := by
    simpa [prefixWord, tailWord_7822981, baseEnd_7822981] using wordTrace_append hprefix tailTrace_7822981
  have hstable : (prefixWord ++ tailWord_7822981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822981).length < 2 ^ (prefixWord ++ tailWord_7822981).sum := by decide
  have hdescent : baseEnd_7822981 < baseStart_7822981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822985 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 3, 2, 2]
def baseStart_7822985 : Nat := 118140960795 + 7822985 * 2 ^ 59
def prefixEnd_7822985 : Nat := 4983230072969 + 3 ^ 40 * 7822985 * 2
def baseEnd_7822985 : Nat := 4016951457913180268910253

theorem tailTrace_7822985 : CollatzResearch.WordTrace tailWord_7822985 prefixEnd_7822985 4016951457913180268910253 := by
  unfold tailWord_7822985
  simp only [CollatzResearch.WordTrace]
  refine ⟨285327703563668879313982409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190218469042445919542654939 285327703563668879313982409)
  ·
    refine ⟨213995777672751659485486807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285327703563668879313982409 213995777672751659485486807)
    ·
      refine ⟨320993666509127489228230211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213995777672751659485486807 320993666509127489228230211)
      ·
        refine ⟨481490499763691233842345317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320993666509127489228230211 481490499763691233842345317)
        ·
          refine ⟨90279468705692106345439747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481490499763691233842345317 90279468705692106345439747)
          ·
            refine ⟨135419203058538159518159621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90279468705692106345439747 135419203058538159518159621)
            ·
              refine ⟨25391100573475904909654929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135419203058538159518159621 25391100573475904909654929)
              ·
                refine ⟨19043325430106928682241197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25391100573475904909654929 19043325430106928682241197)
                ·
                  refine ⟨7141247036290098255840449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19043325430106928682241197 7141247036290098255840449)
                  ·
                    refine ⟨5355935277217573691880337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7141247036290098255840449 5355935277217573691880337)
                    ·
                      refine ⟨4016951457913180268910253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5355935277217573691880337 4016951457913180268910253)
                      ·
                        rfl

theorem cell23_7822985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 2, 2].length) (baseStart_7822985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822985 prefixEnd_7822985 := by exact prefixLift 7822985
  have htrace : WordTrace (prefixWord ++ tailWord_7822985) baseStart_7822985 baseEnd_7822985 := by
    simpa [prefixWord, tailWord_7822985, baseEnd_7822985] using wordTrace_append hprefix tailTrace_7822985
  have hstable : (prefixWord ++ tailWord_7822985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822985).length < 2 ^ (prefixWord ++ tailWord_7822985).sum := by decide
  have hdescent : baseEnd_7822985 < baseStart_7822985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7822996 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7822996 : Nat := 118140960795 + 7822996 * 2 ^ 59
def prefixEnd_7822996 : Nat := 4983230072969 + 3 ^ 40 * 7822996 * 2
def baseEnd_7822996 : Nat := 4016957106200379725872703

theorem tailTrace_7822996 : CollatzResearch.WordTrace tailWord_7822996 prefixEnd_7822996 4016957106200379725872703 := by
  unfold tailWord_7822996
  simp only [CollatzResearch.WordTrace]
  refine ⟨142664052383314514096316421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190218736511086018795088561 142664052383314514096316421)
  ·
    refine ⟨26749509821871471393059329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142664052383314514096316421 26749509821871471393059329)
    ·
      refine ⟨20062132366403603544794497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26749509821871471393059329 20062132366403603544794497)
      ·
        refine ⟨15046599274802702658595873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20062132366403603544794497 15046599274802702658595873)
        ·
          refine ⟨11284949456102026993946905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15046599274802702658595873 11284949456102026993946905)
          ·
            refine ⟨8463712092076520245460179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284949456102026993946905 8463712092076520245460179)
            ·
              refine ⟨12695568138114780368190269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463712092076520245460179 12695568138114780368190269)
              ·
                refine ⟨4760838051793042638071351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12695568138114780368190269 4760838051793042638071351)
                ·
                  refine ⟨7141257077689563957107027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760838051793042638071351 7141257077689563957107027)
                  ·
                    refine ⟨10711885616534345935660541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7141257077689563957107027 10711885616534345935660541)
                    ·
                      refine ⟨4016957106200379725872703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10711885616534345935660541 4016957106200379725872703)
                      ·
                        rfl

theorem cell23_7822996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7822996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7822996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7822996 prefixEnd_7822996 := by exact prefixLift 7822996
  have htrace : WordTrace (prefixWord ++ tailWord_7822996) baseStart_7822996 baseEnd_7822996 := by
    simpa [prefixWord, tailWord_7822996, baseEnd_7822996] using wordTrace_append hprefix tailTrace_7822996
  have hstable : (prefixWord ++ tailWord_7822996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7822996).length < 2 ^ (prefixWord ++ tailWord_7822996).sum := by decide
  have hdescent : baseEnd_7822996 < baseStart_7822996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7822996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823029 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7823029 : Nat := 118140960795 + 7823029 * 2 ^ 59
def prefixEnd_7823029 : Nat := 4983230072969 + 3 ^ 40 * 7823029 * 2
def baseEnd_7823029 : Nat := 1338991350353992698920017

theorem tailTrace_7823029 : CollatzResearch.WordTrace tailWord_7823029 prefixEnd_7823029 1338991350353992698920017 := by
  unfold tailWord_7823029
  simp only [CollatzResearch.WordTrace]
  refine ⟨285329308375509474828584141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190219538917006316552389427 285329308375509474828584141)
  ·
    refine ⟨106998490640816053060719053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285329308375509474828584141 106998490640816053060719053)
    ·
      refine ⟨40124433990306019897769645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106998490640816053060719053 40124433990306019897769645)
      ·
        refine ⟨15046662746364757461663617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40124433990306019897769645 15046662746364757461663617)
        ·
          refine ⟨11284997059773568096247713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15046662746364757461663617 11284997059773568096247713)
          ·
            refine ⟨8463747794830176072185785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284997059773568096247713 8463747794830176072185785)
            ·
              refine ⟨6347810846122632054139339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463747794830176072185785 6347810846122632054139339)
              ·
                refine ⟨9521716269183948081209009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347810846122632054139339 9521716269183948081209009)
                ·
                  refine ⟨7141287201887961060906757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9521716269183948081209009 7141287201887961060906757)
                  ·
                    refine ⟨1338991350353992698920017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141287201887961060906757 1338991350353992698920017)
                    ·
                      rfl

theorem cell23_7823029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7823029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823029 prefixEnd_7823029 := by exact prefixLift 7823029
  have htrace : WordTrace (prefixWord ++ tailWord_7823029) baseStart_7823029 baseEnd_7823029 := by
    simpa [prefixWord, tailWord_7823029, baseEnd_7823029] using wordTrace_append hprefix tailTrace_7823029
  have hstable : (prefixWord ++ tailWord_7823029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823029).length < 2 ^ (prefixWord ++ tailWord_7823029).sum := by decide
  have hdescent : baseEnd_7823029 < baseStart_7823029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823081 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 7]
def baseStart_7823081 : Nat := 118140960795 + 7823081 * 2 ^ 59
def prefixEnd_7823081 : Nat := 4983230072969 + 3 ^ 40 * 7823081 * 2
def baseEnd_7823081 : Nat := 446333416895112432589979

theorem tailTrace_7823081 : CollatzResearch.WordTrace tailWord_7823081 prefixEnd_7823081 446333416895112432589979 := by
  unfold tailWord_7823081
  simp only [CollatzResearch.WordTrace]
  refine ⟨285331204971321087709477097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190220803314214058472984731 285331204971321087709477097)
  ·
    refine ⟨213998403728490815782107823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285331204971321087709477097 213998403728490815782107823)
    ·
      refine ⟨320997605592736223673161735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213998403728490815782107823 320997605592736223673161735)
      ·
        refine ⟨481496408389104335509742603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320997605592736223673161735 481496408389104335509742603)
        ·
          refine ⟨722244612583656503264613905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481496408389104335509742603 722244612583656503264613905)
          ·
            refine ⟨541683459437742377448460429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722244612583656503264613905 541683459437742377448460429)
            ·
              refine ⟨203131297289153391543172661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541683459437742377448460429 203131297289153391543172661)
              ·
                refine ⟨19043559120858130457172437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203131297289153391543172661 19043559120858130457172437)
                ·
                  refine ⟨446333416895112432589979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19043559120858130457172437 446333416895112432589979)
                  ·
                    rfl

theorem cell23_7823081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_7823081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823081 prefixEnd_7823081 := by exact prefixLift 7823081
  have htrace : WordTrace (prefixWord ++ tailWord_7823081) baseStart_7823081 baseEnd_7823081 := by
    simpa [prefixWord, tailWord_7823081, baseEnd_7823081] using wordTrace_append hprefix tailTrace_7823081
  have hstable : (prefixWord ++ tailWord_7823081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823081).length < 2 ^ (prefixWord ++ tailWord_7823081).sum := by decide
  have hdescent : baseEnd_7823081 < baseStart_7823081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823128 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_7823128 : Nat := 118140960795 + 7823128 * 2 ^ 59
def prefixEnd_7823128 : Nat := 4983230072969 + 3 ^ 40 * 7823128 * 2
def baseEnd_7823128 : Nat := 1339008295215591069807365

theorem tailTrace_7823128 : CollatzResearch.WordTrace tailWord_7823128 prefixEnd_7823128 1339008295215591069807365 := by
  unfold tailWord_7823128
  simp only [CollatzResearch.WordTrace]
  refine ⟨142666459601075407368219019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190221946134767209824292025 142666459601075407368219019)
  ·
    refine ⟨213999689401613111052328529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142666459601075407368219019 213999689401613111052328529)
    ·
      refine ⟨160499767051209833289246397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213999689401613111052328529 160499767051209833289246397)
      ·
        refine ⟨60187412644203687483467399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160499767051209833289246397 60187412644203687483467399)
        ·
          refine ⟨90281118966305531225201099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60187412644203687483467399 90281118966305531225201099)
          ·
            refine ⟨135421678449458296837801649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90281118966305531225201099 135421678449458296837801649)
            ·
              refine ⟨101566258837093722628351237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135421678449458296837801649 101566258837093722628351237)
              ·
                refine ⟨19043673531955072992815857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101566258837093722628351237 19043673531955072992815857)
                ·
                  refine ⟨14282755148966304744611893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19043673531955072992815857 14282755148966304744611893)
                  ·
                    refine ⟨1339008295215591069807365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14282755148966304744611893 1339008295215591069807365)
                    ·
                      rfl

theorem cell23_7823128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_7823128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823128 prefixEnd_7823128 := by exact prefixLift 7823128
  have htrace : WordTrace (prefixWord ++ tailWord_7823128) baseStart_7823128 baseEnd_7823128 := by
    simpa [prefixWord, tailWord_7823128, baseEnd_7823128] using wordTrace_append hprefix tailTrace_7823128
  have hstable : (prefixWord ++ tailWord_7823128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823128).length < 2 ^ (prefixWord ++ tailWord_7823128).sum := by decide
  have hdescent : baseEnd_7823128 < baseStart_7823128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823138 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7823138 : Nat := 118140960795 + 7823138 * 2 ^ 59
def prefixEnd_7823138 : Nat := 4983230072969 + 3 ^ 40 * 7823138 * 2
def baseEnd_7823138 : Nat := 4017030020453318170297049

theorem tailTrace_7823138 : CollatzResearch.WordTrace tailWord_7823138 prefixEnd_7823138 4017030020453318170297049 := by
  unfold tailWord_7823138
  simp only [CollatzResearch.WordTrace]
  refine ⟨71333320983028646611075517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190222189288076390962868045 71333320983028646611075517)
  ·
    refine ⟨26749995368635742479153319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71333320983028646611075517 26749995368635742479153319)
    ·
      refine ⟨40124993052953613718729979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26749995368635742479153319 40124993052953613718729979)
      ·
        refine ⟨60187489579430420578094969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40124993052953613718729979 60187489579430420578094969)
        ·
          refine ⟨45140617184572815433571227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60187489579430420578094969 45140617184572815433571227)
          ·
            refine ⟨67710925776859223150356841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45140617184572815433571227 67710925776859223150356841)
            ·
              refine ⟨50783194332644417362767631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67710925776859223150356841 50783194332644417362767631)
              ·
                refine ⟨76174791498966626044151447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50783194332644417362767631 76174791498966626044151447)
                ·
                  refine ⟨114262187248449939066227171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76174791498966626044151447 114262187248449939066227171)
                  ·
                    refine ⟨171393280872674908599340757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114262187248449939066227171 171393280872674908599340757)
                    ·
                      refine ⟨4017030020453318170297049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171393280872674908599340757 4017030020453318170297049)
                      ·
                        rfl

theorem cell23_7823138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7823138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823138 prefixEnd_7823138 := by exact prefixLift 7823138
  have htrace : WordTrace (prefixWord ++ tailWord_7823138) baseStart_7823138 baseEnd_7823138 := by
    simpa [prefixWord, tailWord_7823138, baseEnd_7823138] using wordTrace_append hprefix tailTrace_7823138
  have hstable : (prefixWord ++ tailWord_7823138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823138).length < 2 ^ (prefixWord ++ tailWord_7823138).sum := by decide
  have hdescent : baseEnd_7823138 < baseStart_7823138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823148 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_7823148 : Nat := 118140960795 + 7823148 * 2 ^ 59
def prefixEnd_7823148 : Nat := 4983230072969 + 3 ^ 40 * 7823148 * 2
def baseEnd_7823148 : Nat := 4017035155259863131172003

theorem tailTrace_7823148 : CollatzResearch.WordTrace tailWord_7823148 prefixEnd_7823148 4017035155259863131172003 := by
  unfold tailWord_7823148
  simp only [CollatzResearch.WordTrace]
  refine ⟨142666824331039179076083049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190222432441385572101444065 142666824331039179076083049)
  ·
    refine ⟨107000118248279384307062287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142666824331039179076083049 107000118248279384307062287)
    ·
      refine ⟨160500177372419076460593431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107000118248279384307062287 160500177372419076460593431)
      ·
        refine ⟨240750266058628614690890147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160500177372419076460593431 240750266058628614690890147)
        ·
          refine ⟨361125399087942922036335221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240750266058628614690890147 361125399087942922036335221)
          ·
            refine ⟨33855506164494648940906427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361125399087942922036335221 33855506164494648940906427)
            ·
              refine ⟨50783259246741973411359641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33855506164494648940906427 50783259246741973411359641)
              ·
                refine ⟨38087444435056480058519731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50783259246741973411359641 38087444435056480058519731)
                ·
                  refine ⟨57131166652584720087779597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38087444435056480058519731 57131166652584720087779597)
                  ·
                    refine ⟨21424187494719270032917349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57131166652584720087779597 21424187494719270032917349)
                    ·
                      refine ⟨4017035155259863131172003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21424187494719270032917349 4017035155259863131172003)
                      ·
                        rfl

theorem cell23_7823148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_7823148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823148 prefixEnd_7823148 := by exact prefixLift 7823148
  have htrace : WordTrace (prefixWord ++ tailWord_7823148) baseStart_7823148 baseEnd_7823148 := by
    simpa [prefixWord, tailWord_7823148, baseEnd_7823148] using wordTrace_append hprefix tailTrace_7823148
  have hstable : (prefixWord ++ tailWord_7823148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823148).length < 2 ^ (prefixWord ++ tailWord_7823148).sum := by decide
  have hdescent : baseEnd_7823148 < baseStart_7823148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823165 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7823165 : Nat := 118140960795 + 7823165 * 2 ^ 59
def prefixEnd_7823165 : Nat := 4983230072969 + 3 ^ 40 * 7823165 * 2
def baseEnd_7823165 : Nat := 4017043884430989564659425

theorem tailTrace_7823165 : CollatzResearch.WordTrace tailWord_7823165 prefixEnd_7823165 4017043884430989564659425 := by
  unfold tailWord_7823165
  simp only [CollatzResearch.WordTrace]
  refine ⟨285334268703016770055534949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190222845802011180037023299 285334268703016770055534949)
  ·
    refine ⟨53500175381815644385412803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285334268703016770055534949 53500175381815644385412803)
    ·
      refine ⟨80250263072723466578119205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53500175381815644385412803 80250263072723466578119205)
      ·
        refine ⟨15046924326135649983397351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80250263072723466578119205 15046924326135649983397351)
        ·
          refine ⟨22570386489203474975096027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15046924326135649983397351 22570386489203474975096027)
          ·
            refine ⟨33855579733805212462644041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22570386489203474975096027 33855579733805212462644041)
            ·
              refine ⟨25391684800353909346983031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33855579733805212462644041 25391684800353909346983031)
              ·
                refine ⟨38087527200530864020474547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25391684800353909346983031 38087527200530864020474547)
                ·
                  refine ⟨57131290800796296030711821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38087527200530864020474547 57131290800796296030711821)
                  ·
                    refine ⟨21424234050298611011516933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57131290800796296030711821 21424234050298611011516933)
                    ·
                      refine ⟨4017043884430989564659425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21424234050298611011516933 4017043884430989564659425)
                      ·
                        rfl

theorem cell23_7823165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7823165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823165 prefixEnd_7823165 := by exact prefixLift 7823165
  have htrace : WordTrace (prefixWord ++ tailWord_7823165) baseStart_7823165 baseEnd_7823165 := by
    simpa [prefixWord, tailWord_7823165, baseEnd_7823165] using wordTrace_append hprefix tailTrace_7823165
  have hstable : (prefixWord ++ tailWord_7823165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823165).length < 2 ^ (prefixWord ++ tailWord_7823165).sum := by decide
  have hdescent : baseEnd_7823165 < baseStart_7823165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823185 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_7823185 : Nat := 118140960795 + 7823185 * 2 ^ 59
def prefixEnd_7823185 : Nat := 4983230072969 + 3 ^ 40 * 7823185 * 2
def baseEnd_7823185 : Nat := 4017054154044079486409333

theorem tailTrace_7823185 : CollatzResearch.WordTrace tailWord_7823185 prefixEnd_7823185 4017054154044079486409333 := by
  unfold tailWord_7823185
  simp only [CollatzResearch.WordTrace]
  refine ⟨285334998162944313471263009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190223332108629542314175339 285334998162944313471263009)
  ·
    refine ⟨214001248622208235103447257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285334998162944313471263009 214001248622208235103447257)
    ·
      refine ⟨160500936466656176327585443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214001248622208235103447257 160500936466656176327585443)
      ·
        refine ⟨240751404699984264491378165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160500936466656176327585443 240751404699984264491378165)
        ·
          refine ⟨22570444190623524796066703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240751404699984264491378165 22570444190623524796066703)
          ·
            refine ⟨33855666285935287194100055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22570444190623524796066703 33855666285935287194100055)
            ·
              refine ⟨50783499428902930791150083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33855666285935287194100055 50783499428902930791150083)
              ·
                refine ⟨76175249143354396186725125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50783499428902930791150083 76175249143354396186725125)
                ·
                  refine ⟨14282859214378949285010961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76175249143354396186725125 14282859214378949285010961)
                  ·
                    refine ⟨10712144410784211963758221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14282859214378949285010961 10712144410784211963758221)
                    ·
                      refine ⟨4017054154044079486409333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10712144410784211963758221 4017054154044079486409333)
                      ·
                        rfl

theorem cell23_7823185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_7823185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823185 prefixEnd_7823185 := by exact prefixLift 7823185
  have htrace : WordTrace (prefixWord ++ tailWord_7823185) baseStart_7823185 baseEnd_7823185 := by
    simpa [prefixWord, tailWord_7823185, baseEnd_7823185] using wordTrace_append hprefix tailTrace_7823185
  have hstable : (prefixWord ++ tailWord_7823185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823185).length < 2 ^ (prefixWord ++ tailWord_7823185).sum := by decide
  have hdescent : baseEnd_7823185 < baseStart_7823185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823255 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7823255 : Nat := 118140960795 + 7823255 * 2 ^ 59
def prefixEnd_7823255 : Nat := 4983230072969 + 3 ^ 40 * 7823255 * 2
def baseEnd_7823255 : Nat := 4017090097689894212534011

theorem tailTrace_7823255 : CollatzResearch.WordTrace tailWord_7823255 prefixEnd_7823255 4017090097689894212534011 := by
  unfold tailWord_7823255
  simp only [CollatzResearch.WordTrace]
  refine ⟨285337551272690715426311219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190225034181793810284207479 285337551272690715426311219)
  ·
    refine ⟨428006326909036073139466829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285337551272690715426311219 428006326909036073139466829)
    ·
      refine ⟨160502372590888527427300061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428006326909036073139466829 160502372590888527427300061)
      ·
        refine ⟨60188389721583197785237523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160502372590888527427300061 60188389721583197785237523)
        ·
          refine ⟨90282584582374796677856285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60188389721583197785237523 90282584582374796677856285)
          ·
            refine ⟨33855969218390548754196107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90282584582374796677856285 33855969218390548754196107)
            ·
              refine ⟨50783953827585823131294161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33855969218390548754196107 50783953827585823131294161)
              ·
                refine ⟨38087965370689367348470621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50783953827585823131294161 38087965370689367348470621)
                ·
                  refine ⟨14282987014008512755676483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38087965370689367348470621 14282987014008512755676483)
                  ·
                    refine ⟨21424480521012769133514725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14282987014008512755676483 21424480521012769133514725)
                    ·
                      refine ⟨4017090097689894212534011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21424480521012769133514725 4017090097689894212534011)
                      ·
                        rfl

theorem cell23_7823255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7823255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823255 prefixEnd_7823255 := by exact prefixLift 7823255
  have htrace : WordTrace (prefixWord ++ tailWord_7823255) baseStart_7823255 baseEnd_7823255 := by
    simpa [prefixWord, tailWord_7823255, baseEnd_7823255] using wordTrace_append hprefix tailTrace_7823255
  have hstable : (prefixWord ++ tailWord_7823255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823255).length < 2 ^ (prefixWord ++ tailWord_7823255).sum := by decide
  have hdescent : baseEnd_7823255 < baseStart_7823255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823306 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_7823306 : Nat := 118140960795 + 7823306 * 2 ^ 59
def prefixEnd_7823306 : Nat := 4983230072969 + 3 ^ 40 * 7823306 * 2
def baseEnd_7823306 : Nat := 4017116285203273512996277

theorem tailTrace_7823306 : CollatzResearch.WordTrace tailWord_7823306 prefixEnd_7823306 4017116285203273512996277 := by
  unfold tailWord_7823306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71334852848876487784104443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190226274263670634090945181 71334852848876487784104443)
  ·
    refine ⟨107002279273314731676156665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71334852848876487784104443 107002279273314731676156665)
    ·
      refine ⟨80251709454986048757117499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107002279273314731676156665 80251709454986048757117499)
      ·
        refine ⟨120377564182479073135676249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80251709454986048757117499 120377564182479073135676249)
        ·
          refine ⟨90283173136859304851757187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120377564182479073135676249 90283173136859304851757187)
          ·
            refine ⟨135424759705288957277635781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90283173136859304851757187 135424759705288957277635781)
            ·
              refine ⟨25392142444741679489556709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135424759705288957277635781 25392142444741679489556709)
              ·
                refine ⟨4761026708389064904291883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25392142444741679489556709 4761026708389064904291883)
                ·
                  refine ⟨7141540062583597356437825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761026708389064904291883 7141540062583597356437825)
                  ·
                    refine ⟨5356155046937698017328369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7141540062583597356437825 5356155046937698017328369)
                    ·
                      refine ⟨4017116285203273512996277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356155046937698017328369 4017116285203273512996277)
                      ·
                        rfl

theorem cell23_7823306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_7823306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823306 prefixEnd_7823306 := by exact prefixLift 7823306
  have htrace : WordTrace (prefixWord ++ tailWord_7823306) baseStart_7823306 baseEnd_7823306 := by
    simpa [prefixWord, tailWord_7823306, baseEnd_7823306] using wordTrace_append hprefix tailTrace_7823306
  have hstable : (prefixWord ++ tailWord_7823306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823306).length < 2 ^ (prefixWord ++ tailWord_7823306).sum := by decide
  have hdescent : baseEnd_7823306 < baseStart_7823306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823383 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7823383 : Nat := 118140960795 + 7823383 * 2 ^ 59
def prefixEnd_7823383 : Nat := 4983230072969 + 3 ^ 40 * 7823383 * 2
def baseEnd_7823383 : Nat := 4017155823213669711733423

theorem tailTrace_7823383 : CollatzResearch.WordTrace tailWord_7823383 prefixEnd_7823383 4017155823213669711733423 := by
  unfold tailWord_7823383
  simp only [CollatzResearch.WordTrace]
  refine ⟨285342219816226993286970803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190228146544151328857980535 285342219816226993286970803)
  ·
    refine ⟨428013329724340489930456205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285342219816226993286970803 428013329724340489930456205)
    ·
      refine ⟨160504998646627683723921077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428013329724340489930456205 160504998646627683723921077)
      ·
        refine ⟨15047343623121345349117601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160504998646627683723921077 15047343623121345349117601)
        ·
          refine ⟨11285507717341009011838201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047343623121345349117601 11285507717341009011838201)
          ·
            refine ⟨8464130788005756758878651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11285507717341009011838201 8464130788005756758878651)
            ·
              refine ⟨12696196182008635138317977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464130788005756758878651 12696196182008635138317977)
              ·
                refine ⟨9522147136506476353738483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696196182008635138317977 9522147136506476353738483)
                ·
                  refine ⟨14283220704759714530607725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522147136506476353738483 14283220704759714530607725)
                  ·
                    refine ⟨5356207764284892948977897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14283220704759714530607725 5356207764284892948977897)
                    ·
                      refine ⟨4017155823213669711733423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356207764284892948977897 4017155823213669711733423)
                      ·
                        rfl

theorem cell23_7823383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7823383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823383 prefixEnd_7823383 := by exact prefixLift 7823383
  have htrace : WordTrace (prefixWord ++ tailWord_7823383) baseStart_7823383 baseEnd_7823383 := by
    simpa [prefixWord, tailWord_7823383, baseEnd_7823383] using wordTrace_append hprefix tailTrace_7823383
  have hstable : (prefixWord ++ tailWord_7823383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823383).length < 2 ^ (prefixWord ++ tailWord_7823383).sum := by decide
  have hdescent : baseEnd_7823383 < baseStart_7823383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823396 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7823396 : Nat := 118140960795 + 7823396 * 2 ^ 59
def prefixEnd_7823396 : Nat := 4983230072969 + 3 ^ 40 * 7823396 * 2
def baseEnd_7823396 : Nat := 4017162498462178160870863

theorem tailTrace_7823396 : CollatzResearch.WordTrace tailWord_7823396 prefixEnd_7823396 4017162498462178160870863 := by
  unfold tailWord_7823396
  simp only [CollatzResearch.WordTrace]
  refine ⟨142671346982589948253597021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190228462643453264338129361 142671346982589948253597021)
  ·
    refine ⟨53501755118471230595098883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142671346982589948253597021 53501755118471230595098883)
    ·
      refine ⟨80252632677706845892648325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53501755118471230595098883 80252632677706845892648325)
      ·
        refine ⟨15047368627070033604871561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80252632677706845892648325 15047368627070033604871561)
        ·
          refine ⟨11285526470302525203653671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047368627070033604871561 11285526470302525203653671)
          ·
            refine ⟨16928289705453787805480507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285526470302525203653671 16928289705453787805480507)
            ·
              refine ⟨25392434558180681708220761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16928289705453787805480507 25392434558180681708220761)
              ·
                refine ⟨19044325918635511281165571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25392434558180681708220761 19044325918635511281165571)
                ·
                  refine ⟨28566488877953266921748357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19044325918635511281165571 28566488877953266921748357)
                  ·
                    refine ⟨5356216664616237547827817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28566488877953266921748357 5356216664616237547827817)
                    ·
                      refine ⟨4017162498462178160870863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356216664616237547827817 4017162498462178160870863)
                      ·
                        rfl

theorem cell23_7823396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7823396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823396 prefixEnd_7823396 := by exact prefixLift 7823396
  have htrace : WordTrace (prefixWord ++ tailWord_7823396) baseStart_7823396 baseEnd_7823396 := by
    simpa [prefixWord, tailWord_7823396, baseEnd_7823396] using wordTrace_append hprefix tailTrace_7823396
  have hstable : (prefixWord ++ tailWord_7823396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823396).length < 2 ^ (prefixWord ++ tailWord_7823396).sum := by decide
  have hdescent : baseEnd_7823396 < baseStart_7823396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823400 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7823400 : Nat := 118140960795 + 7823400 * 2 ^ 59
def prefixEnd_7823400 : Nat := 4983230072969 + 3 ^ 40 * 7823400 * 2
def baseEnd_7823400 : Nat := 4017164552384796145220845

theorem tailTrace_7823400 : CollatzResearch.WordTrace tailWord_7823400 prefixEnd_7823400 4017164552384796145220845 := by
  unfold tailWord_7823400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142671419928582702595169827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190228559904776936793559769 142671419928582702595169827)
  ·
    refine ⟨214007129892874053892754741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142671419928582702595169827 214007129892874053892754741)
    ·
      refine ⟨20063168427456942552445757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214007129892874053892754741 20063168427456942552445757)
      ·
        refine ⟨7523688160296353457167159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20063168427456942552445757 7523688160296353457167159)
        ·
          refine ⟨11285532240444530185750739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523688160296353457167159 11285532240444530185750739)
          ·
            refine ⟨16928298360666795278626109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285532240444530185750739 16928298360666795278626109)
            ·
              refine ⟨6348111885250048229484791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16928298360666795278626109 6348111885250048229484791)
              ·
                refine ⟨9522167827875072344227187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348111885250048229484791 9522167827875072344227187)
                ·
                  refine ⟨14283251741812608516340781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522167827875072344227187 14283251741812608516340781)
                  ·
                    refine ⟨5356219403179728193627793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14283251741812608516340781 5356219403179728193627793)
                    ·
                      refine ⟨4017164552384796145220845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356219403179728193627793 4017164552384796145220845)
                      ·
                        rfl

theorem cell23_7823400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7823400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823400 prefixEnd_7823400 := by exact prefixLift 7823400
  have htrace : WordTrace (prefixWord ++ tailWord_7823400) baseStart_7823400 baseEnd_7823400 := by
    simpa [prefixWord, tailWord_7823400, baseEnd_7823400] using wordTrace_append hprefix tailTrace_7823400
  have hstable : (prefixWord ++ tailWord_7823400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823400).length < 2 ^ (prefixWord ++ tailWord_7823400).sum := by decide
  have hdescent : baseEnd_7823400 < baseStart_7823400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823435 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_7823435 : Nat := 118140960795 + 7823435 * 2 ^ 59
def prefixEnd_7823435 : Nat := 4983230072969 + 3 ^ 40 * 7823435 * 2
def baseEnd_7823435 : Nat := 4017182524207703508283183

theorem tailTrace_7823435 : CollatzResearch.WordTrace tailWord_7823435 prefixEnd_7823435 4017182524207703508283183 := by
  unfold tailWord_7823435
  simp only [CollatzResearch.WordTrace]
  refine ⟨285344116412038606167863759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190229410941359070778575839 285344116412038606167863759)
  ·
    refine ⟨428016174618057909251795639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285344116412038606167863759 428016174618057909251795639)
    ·
      refine ⟨642024261927086863877693459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428016174618057909251795639 642024261927086863877693459)
      ·
        refine ⟨963036392890630295816540189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642024261927086863877693459 963036392890630295816540189)
        ·
          refine ⟨361138647333986360931202571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 963036392890630295816540189 361138647333986360931202571)
          ·
            refine ⟨541707971000979541396803857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361138647333986360931202571 541707971000979541396803857)
            ·
              refine ⟨406280978250734656047602893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541707971000979541396803857 406280978250734656047602893)
              ·
                refine ⟨152355366844025496017851085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406280978250734656047602893 152355366844025496017851085)
                ·
                  refine ⟨57133262566509561006694157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152355366844025496017851085 57133262566509561006694157)
                  ·
                    refine ⟨21424973462441085377510309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57133262566509561006694157 21424973462441085377510309)
                    ·
                      refine ⟨4017182524207703508283183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21424973462441085377510309 4017182524207703508283183)
                      ·
                        rfl

theorem cell23_7823435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_7823435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823435 prefixEnd_7823435 := by exact prefixLift 7823435
  have htrace : WordTrace (prefixWord ++ tailWord_7823435) baseStart_7823435 baseEnd_7823435 := by
    simpa [prefixWord, tailWord_7823435, baseEnd_7823435] using wordTrace_append hprefix tailTrace_7823435
  have hstable : (prefixWord ++ tailWord_7823435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823435).length < 2 ^ (prefixWord ++ tailWord_7823435).sum := by decide
  have hdescent : baseEnd_7823435 < baseStart_7823435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823455 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7823455 : Nat := 118140960795 + 7823455 * 2 ^ 59
def prefixEnd_7823455 : Nat := 4983230072969 + 3 ^ 40 * 7823455 * 2
def baseEnd_7823455 : Nat := 4017192793820793430033091

theorem tailTrace_7823455 : CollatzResearch.WordTrace tailWord_7823455 prefixEnd_7823455 4017192793820793430033091 := by
  unfold tailWord_7823455
  simp only [CollatzResearch.WordTrace]
  refine ⟨285344845871966149583591819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190229897247977433055727879 285344845871966149583591819)
  ·
    refine ⟨428017268807949224375387729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285344845871966149583591819 428017268807949224375387729)
    ·
      refine ⟨321012951605961918281540797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428017268807949224375387729 321012951605961918281540797)
      ·
        refine ⟨120379856852235719355577799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321012951605961918281540797 120379856852235719355577799)
        ·
          refine ⟨180569785278353579033366699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120379856852235719355577799 180569785278353579033366699)
          ·
            refine ⟨270854677917530368550050049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180569785278353579033366699 270854677917530368550050049)
            ·
              refine ⟨203141008438147776412537537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270854677917530368550050049 203141008438147776412537537)
              ·
                refine ⟨152355756328610832309403153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203141008438147776412537537 152355756328610832309403153)
                ·
                  refine ⟨114266817246458124232052365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152355756328610832309403153 114266817246458124232052365)
                  ·
                    refine ⟨42850056467421796587019637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114266817246458124232052365 42850056467421796587019637)
                    ·
                      refine ⟨4017192793820793430033091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42850056467421796587019637 4017192793820793430033091)
                      ·
                        rfl

theorem cell23_7823455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7823455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823455 prefixEnd_7823455 := by exact prefixLift 7823455
  have htrace : WordTrace (prefixWord ++ tailWord_7823455) baseStart_7823455 baseEnd_7823455 := by
    simpa [prefixWord, tailWord_7823455, baseEnd_7823455] using wordTrace_append hprefix tailTrace_7823455
  have hstable : (prefixWord ++ tailWord_7823455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823455).length < 2 ^ (prefixWord ++ tailWord_7823455).sum := by decide
  have hdescent : baseEnd_7823455 < baseStart_7823455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823465 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_7823465 : Nat := 118140960795 + 7823465 * 2 ^ 59
def prefixEnd_7823465 : Nat := 4983230072969 + 3 ^ 40 * 7823465 * 2
def baseEnd_7823465 : Nat := 4017197928627338390908045

theorem tailTrace_7823465 : CollatzResearch.WordTrace tailWord_7823465 prefixEnd_7823465 4017197928627338390908045 := by
  unfold tailWord_7823465
  simp only [CollatzResearch.WordTrace]
  refine ⟨285345210601929921291455849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190230140401286614194303899 285345210601929921291455849)
  ·
    refine ⟨214008907951447440968591887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285345210601929921291455849 214008907951447440968591887)
    ·
      refine ⟨321013361927171161452887831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214008907951447440968591887 321013361927171161452887831)
      ·
        refine ⟨481520042890756742179331747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321013361927171161452887831 481520042890756742179331747)
        ·
          refine ⟨722280064336135113268997621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481520042890756742179331747 722280064336135113268997621)
          ·
            refine ⟨67713756031512666868968527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 722280064336135113268997621 67713756031512666868968527)
            ·
              refine ⟨101570634047269000303452791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67713756031512666868968527 101570634047269000303452791)
              ·
                refine ⟨152355951070903500455179187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101570634047269000303452791 152355951070903500455179187)
                ·
                  refine ⟨228533926606355250682768781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152355951070903500455179187 228533926606355250682768781)
                  ·
                    refine ⟨85700222477383219006038293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228533926606355250682768781 85700222477383219006038293)
                    ·
                      refine ⟨4017197928627338390908045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85700222477383219006038293 4017197928627338390908045)
                      ·
                        rfl

theorem cell23_7823465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_7823465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823465 prefixEnd_7823465 := by exact prefixLift 7823465
  have htrace : WordTrace (prefixWord ++ tailWord_7823465) baseStart_7823465 baseEnd_7823465 := by
    simpa [prefixWord, tailWord_7823465, baseEnd_7823465] using wordTrace_append hprefix tailTrace_7823465
  have hstable : (prefixWord ++ tailWord_7823465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823465).length < 2 ^ (prefixWord ++ tailWord_7823465).sum := by decide
  have hdescent : baseEnd_7823465 < baseStart_7823465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823469 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_7823469 : Nat := 118140960795 + 7823469 * 2 ^ 59
def prefixEnd_7823469 : Nat := 4983230072969 + 3 ^ 40 * 7823469 * 2
def baseEnd_7823469 : Nat := 4017199982549956375258027

theorem tailTrace_7823469 : CollatzResearch.WordTrace tailWord_7823469 prefixEnd_7823469 4017199982549956375258027 := by
  unfold tailWord_7823469
  simp only [CollatzResearch.WordTrace]
  refine ⟨285345356493915429974601461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190230237662610286649734307 285345356493915429974601461)
  ·
    refine ⟨26751127171304571560118887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285345356493915429974601461 26751127171304571560118887)
    ·
      refine ⟨40126690756956857340178331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26751127171304571560118887 40126690756956857340178331)
      ·
        refine ⟨60190036135435286010267497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40126690756956857340178331 60190036135435286010267497)
        ·
          refine ⟨45142527101576464507700623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60190036135435286010267497 45142527101576464507700623)
          ·
            refine ⟨67713790652364696761550935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45142527101576464507700623 67713790652364696761550935)
            ·
              refine ⟨101570685978547045142326403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67713790652364696761550935 101570685978547045142326403)
              ·
                refine ⟨152356028967820567713489605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101570685978547045142326403 152356028967820567713489605)
                ·
                  refine ⟨28566755431466356446279301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152356028967820567713489605 28566755431466356446279301)
                  ·
                    refine ⟨5356266643399941833677369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28566755431466356446279301 5356266643399941833677369)
                    ·
                      refine ⟨4017199982549956375258027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356266643399941833677369 4017199982549956375258027)
                      ·
                        rfl

theorem cell23_7823469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_7823469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823469 prefixEnd_7823469 := by exact prefixLift 7823469
  have htrace : WordTrace (prefixWord ++ tailWord_7823469) baseStart_7823469 baseEnd_7823469 := by
    simpa [prefixWord, tailWord_7823469, baseEnd_7823469] using wordTrace_append hprefix tailTrace_7823469
  have hstable : (prefixWord ++ tailWord_7823469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823469).length < 2 ^ (prefixWord ++ tailWord_7823469).sum := by decide
  have hdescent : baseEnd_7823469 < baseStart_7823469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823479 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 3, 4]
def baseStart_7823479 : Nat := 118140960795 + 7823479 * 2 ^ 59
def prefixEnd_7823479 : Nat := 4983230072969 + 3 ^ 40 * 7823479 * 2
def baseEnd_7823479 : Nat := 1339068372452167112044327

theorem tailTrace_7823479 : CollatzResearch.WordTrace tailWord_7823479 prefixEnd_7823479 1339068372452167112044327 := by
  unfold tailWord_7823479
  simp only [CollatzResearch.WordTrace]
  refine ⟨285345721223879201682465491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190230480815919467788310327 285345721223879201682465491)
  ·
    refine ⟨428018581835818802523698237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285345721223879201682465491 428018581835818802523698237)
    ·
      refine ⟨160506968188432050946386839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428018581835818802523698237 160506968188432050946386839)
      ·
        refine ⟨240760452282648076419580259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160506968188432050946386839 240760452282648076419580259)
        ·
          refine ⟨361140678423972114629370389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240760452282648076419580259 361140678423972114629370389)
          ·
            refine ⟨16928469301123692873251737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361140678423972114629370389 16928469301123692873251737)
            ·
              refine ⟨12696351975842769654938803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16928469301123692873251737 12696351975842769654938803)
              ·
                refine ⟨19044527963764154482408205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696351975842769654938803 19044527963764154482408205)
                ·
                  refine ⟨7141697986411557930903077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19044527963764154482408205 7141697986411557930903077)
                  ·
                    refine ⟨1339068372452167112044327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141697986411557930903077 1339068372452167112044327)
                    ·
                      rfl

theorem cell23_7823479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_7823479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823479 prefixEnd_7823479 := by exact prefixLift 7823479
  have htrace : WordTrace (prefixWord ++ tailWord_7823479) baseStart_7823479 baseEnd_7823479 := by
    simpa [prefixWord, tailWord_7823479, baseEnd_7823479] using wordTrace_append hprefix tailTrace_7823479
  have hstable : (prefixWord ++ tailWord_7823479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823479).length < 2 ^ (prefixWord ++ tailWord_7823479).sum := by decide
  have hdescent : baseEnd_7823479 < baseStart_7823479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823505 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_7823505 : Nat := 118140960795 + 7823505 * 2 ^ 59
def prefixEnd_7823505 : Nat := 4983230072969 + 3 ^ 40 * 7823505 * 2
def baseEnd_7823505 : Nat := 1339072822617839411469287

theorem tailTrace_7823505 : CollatzResearch.WordTrace tailWord_7823505 prefixEnd_7823505 1339072822617839411469287 := by
  unfold tailWord_7823505
  simp only [CollatzResearch.WordTrace]
  refine ⟨285346669521785008122911969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190231113014523338748607979 285346669521785008122911969)
  ·
    refine ⟨214010002141338756092183977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285346669521785008122911969 214010002141338756092183977)
    ·
      refine ⟨160507501606004067069137983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214010002141338756092183977 160507501606004067069137983)
      ·
        refine ⟨240761252409006100603706975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160507501606004067069137983 240761252409006100603706975)
        ·
          refine ⟨361141878613509150905560463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240761252409006100603706975 361141878613509150905560463)
          ·
            refine ⟨541712817920263726358340695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361141878613509150905560463 541712817920263726358340695)
            ·
              refine ⟨812569226880395589537511043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541712817920263726358340695 812569226880395589537511043)
              ·
                refine ⟨1218853840320593384306266565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812569226880395589537511043 1218853840320593384306266565)
                ·
                  refine ⟨228535095060111259557424981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1218853840320593384306266565 228535095060111259557424981)
                  ·
                    refine ⟨1339072822617839411469287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228535095060111259557424981 1339072822617839411469287)
                    ·
                      rfl

theorem cell23_7823505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_7823505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823505 prefixEnd_7823505 := by exact prefixLift 7823505
  have htrace : WordTrace (prefixWord ++ tailWord_7823505) baseStart_7823505 baseEnd_7823505 := by
    simpa [prefixWord, tailWord_7823505, baseEnd_7823505] using wordTrace_append hprefix tailTrace_7823505
  have hstable : (prefixWord ++ tailWord_7823505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823505).length < 2 ^ (prefixWord ++ tailWord_7823505).sum := by decide
  have hdescent : baseEnd_7823505 < baseStart_7823505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823515 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_7823515 : Nat := 118140960795 + 7823515 * 2 ^ 59
def prefixEnd_7823515 : Nat := 4983230072969 + 3 ^ 40 * 7823515 * 2
def baseEnd_7823515 : Nat := 4017223602660063195282815

theorem tailTrace_7823515 : CollatzResearch.WordTrace tailWord_7823515 prefixEnd_7823515 4017223602660063195282815 := by
  unfold tailWord_7823515
  simp only [CollatzResearch.WordTrace]
  refine ⟨285347034251748779830775999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190231356167832519887183999 285347034251748779830775999)
  ·
    refine ⟨428020551377623169746163999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285347034251748779830775999 428020551377623169746163999)
    ·
      refine ⟨642030827066434754619245999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428020551377623169746163999 642030827066434754619245999)
      ·
        refine ⟨963046240599652131928868999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642030827066434754619245999 963046240599652131928868999)
        ·
          refine ⟨1444569360899478197893303499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963046240599652131928868999 1444569360899478197893303499)
          ·
            refine ⟨2166854041349217296839955249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444569360899478197893303499 2166854041349217296839955249)
            ·
              refine ⟨1625140531011912972629966437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166854041349217296839955249 1625140531011912972629966437)
              ·
                refine ⟨304713849564733682368118707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1625140531011912972629966437 304713849564733682368118707)
                ·
                  refine ⟨457070774347100523552178061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304713849564733682368118707 457070774347100523552178061)
                  ·
                    refine ⟨171401540380162696332066773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457070774347100523552178061 171401540380162696332066773)
                    ·
                      refine ⟨4017223602660063195282815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171401540380162696332066773 4017223602660063195282815)
                      ·
                        rfl

theorem cell23_7823515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_7823515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823515 prefixEnd_7823515 := by exact prefixLift 7823515
  have htrace : WordTrace (prefixWord ++ tailWord_7823515) baseStart_7823515 baseEnd_7823515 := by
    simpa [prefixWord, tailWord_7823515, baseEnd_7823515] using wordTrace_append hprefix tailTrace_7823515
  have hstable : (prefixWord ++ tailWord_7823515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823515).length < 2 ^ (prefixWord ++ tailWord_7823515).sum := by decide
  have hdescent : baseEnd_7823515 < baseStart_7823515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823530 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7823530 : Nat := 118140960795 + 7823530 * 2 ^ 59
def prefixEnd_7823530 : Nat := 4983230072969 + 3 ^ 40 * 7823530 * 2
def baseEnd_7823530 : Nat := 1339077101623293545531749

theorem tailTrace_7823530 : CollatzResearch.WordTrace tailWord_7823530 prefixEnd_7823530 1339077101623293545531749 := by
  unfold tailWord_7823530
  simp only [CollatzResearch.WordTrace]
  refine ⟨71336895336673609348143011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190231720897796291595048029 71336895336673609348143011)
  ·
    refine ⟨107005343005010414022214517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71336895336673609348143011 107005343005010414022214517)
    ·
      refine ⟨10031750906719726314582611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107005343005010414022214517 10031750906719726314582611)
      ·
        refine ⟨15047626360079589471873917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031750906719726314582611 15047626360079589471873917)
        ·
          refine ⟨5642859885029846051952719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15047626360079589471873917 5642859885029846051952719)
          ·
            refine ⟨8464289827544769077929079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642859885029846051952719 8464289827544769077929079)
            ·
              refine ⟨12696434741317153616893619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464289827544769077929079 12696434741317153616893619)
              ·
                refine ⟨19044652111975730425340429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696434741317153616893619 19044652111975730425340429)
                ·
                  refine ⟨7141744541990898909502661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19044652111975730425340429 7141744541990898909502661)
                  ·
                    refine ⟨1339077101623293545531749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141744541990898909502661 1339077101623293545531749)
                    ·
                      rfl

theorem cell23_7823530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7823530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823530 prefixEnd_7823530 := by exact prefixLift 7823530
  have htrace : WordTrace (prefixWord ++ tailWord_7823530) baseStart_7823530 baseEnd_7823530 := by
    simpa [prefixWord, tailWord_7823530, baseEnd_7823530] using wordTrace_append hprefix tailTrace_7823530
  have hstable : (prefixWord ++ tailWord_7823530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823530).length < 2 ^ (prefixWord ++ tailWord_7823530).sum := by decide
  have hdescent : baseEnd_7823530 < baseStart_7823530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823556 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_7823556 : Nat := 118140960795 + 7823556 * 2 ^ 59
def prefixEnd_7823556 : Nat := 4983230072969 + 3 ^ 40 * 7823556 * 2
def baseEnd_7823556 : Nat := 1339081551788965844956709

theorem tailTrace_7823556 : CollatzResearch.WordTrace tailWord_7823556 prefixEnd_7823556 1339081551788965844956709 := by
  unfold tailWord_7823556
  simp only [CollatzResearch.WordTrace]
  refine ⟨142674264822300121916509261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190232353096400162555345681 142674264822300121916509261)
  ·
    refine ⟨53502849308362545718690973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142674264822300121916509261 53502849308362545718690973)
    ·
      refine ⟨20063568490635954644509115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53502849308362545718690973 20063568490635954644509115)
      ·
        refine ⟨30095352735953931966763673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20063568490635954644509115 30095352735953931966763673)
        ·
          refine ⟨22571514551965448975072755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30095352735953931966763673 22571514551965448975072755)
          ·
            refine ⟨33857271827948173462609133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22571514551965448975072755 33857271827948173462609133)
            ·
              refine ⟨12696476935480565048478425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33857271827948173462609133 12696476935480565048478425)
              ·
                refine ⟨9522357701610423786358819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696476935480565048478425 9522357701610423786358819)
                ·
                  refine ⟨14283536552415635679538229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522357701610423786358819 14283536552415635679538229)
                  ·
                    refine ⟨1339081551788965844956709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14283536552415635679538229 1339081551788965844956709)
                    ·
                      rfl

theorem cell23_7823556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_7823556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823556 prefixEnd_7823556 := by exact prefixLift 7823556
  have htrace : WordTrace (prefixWord ++ tailWord_7823556) baseStart_7823556 baseEnd_7823556 := by
    simpa [prefixWord, tailWord_7823556, baseEnd_7823556] using wordTrace_append hprefix tailTrace_7823556
  have hstable : (prefixWord ++ tailWord_7823556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823556).length < 2 ^ (prefixWord ++ tailWord_7823556).sum := by decide
  have hdescent : baseEnd_7823556 < baseStart_7823556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823573 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_7823573 : Nat := 118140960795 + 7823573 * 2 ^ 59
def prefixEnd_7823573 : Nat := 4983230072969 + 3 ^ 40 * 7823573 * 2
def baseEnd_7823573 : Nat := 1339084461512674656119183

theorem tailTrace_7823573 : CollatzResearch.WordTrace tailWord_7823573 prefixEnd_7823573 1339084461512674656119183 := by
  unfold tailWord_7823573
  simp only [CollatzResearch.WordTrace]
  refine ⟨285349149685538655736387373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190232766457025770490924915 285349149685538655736387373)
  ·
    refine ⟨107005931132076995901145265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285349149685538655736387373 107005931132076995901145265)
    ·
      refine ⟨80254448349057746925858949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107005931132076995901145265 80254448349057746925858949)
      ·
        refine ⟨15047709065448327548598553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80254448349057746925858949 15047709065448327548598553)
        ·
          refine ⟨11285781799086245661448915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047709065448327548598553 11285781799086245661448915)
          ·
            refine ⟨16928672698629368492173373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285781799086245661448915 16928672698629368492173373)
            ·
              refine ⟨6348252261986013184565015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16928672698629368492173373 6348252261986013184565015)
              ·
                refine ⟨9522378392979019776847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348252261986013184565015 9522378392979019776847523)
                ·
                  refine ⟨14283567589468529665271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522378392979019776847523 14283567589468529665271285)
                  ·
                    refine ⟨1339084461512674656119183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14283567589468529665271285 1339084461512674656119183)
                    ·
                      rfl

theorem cell23_7823573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_7823573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823573 prefixEnd_7823573 := by exact prefixLift 7823573
  have htrace : WordTrace (prefixWord ++ tailWord_7823573) baseStart_7823573 baseEnd_7823573 := by
    simpa [prefixWord, tailWord_7823573, baseEnd_7823573] using wordTrace_append hprefix tailTrace_7823573
  have hstable : (prefixWord ++ tailWord_7823573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823573).length < 2 ^ (prefixWord ++ tailWord_7823573).sum := by decide
  have hdescent : baseEnd_7823573 < baseStart_7823573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823593 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 1, 2, 2]
def baseStart_7823593 : Nat := 118140960795 + 7823593 * 2 ^ 59
def prefixEnd_7823593 : Nat := 4983230072969 + 3 ^ 40 * 7823593 * 2
def baseEnd_7823593 : Nat := 4017263654151113890107457

theorem tailTrace_7823593 : CollatzResearch.WordTrace tailWord_7823593 prefixEnd_7823593 4017263654151113890107457 := by
  unfold tailWord_7823593
  simp only [CollatzResearch.WordTrace]
  refine ⟨285349879145466199152115433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190233252763644132768076955 285349879145466199152115433)
  ·
    refine ⟨214012409359099649364086575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285349879145466199152115433 214012409359099649364086575)
    ·
      refine ⟨321018614038649474046129863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214012409359099649364086575 321018614038649474046129863)
      ·
        refine ⟨481527921057974211069194795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321018614038649474046129863 481527921057974211069194795)
        ·
          refine ⟨722291881586961316603792193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481527921057974211069194795 722291881586961316603792193)
          ·
            refine ⟨541718911190220987452844145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722291881586961316603792193 541718911190220987452844145)
            ·
              refine ⟨406289183392665740589633109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541718911190220987452844145 406289183392665740589633109)
              ·
                refine ⟨4761201367882801647534763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 406289183392665740589633109 4761201367882801647534763)
                ·
                  refine ⟨7141802051824202471302145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761201367882801647534763 7141802051824202471302145)
                  ·
                    refine ⟨5356351538868151853476609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7141802051824202471302145 5356351538868151853476609)
                    ·
                      refine ⟨4017263654151113890107457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356351538868151853476609 4017263654151113890107457)
                      ·
                        rfl

theorem cell23_7823593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 1, 2, 2].length) (baseStart_7823593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823593 prefixEnd_7823593 := by exact prefixLift 7823593
  have htrace : WordTrace (prefixWord ++ tailWord_7823593) baseStart_7823593 baseEnd_7823593 := by
    simpa [prefixWord, tailWord_7823593, baseEnd_7823593] using wordTrace_append hprefix tailTrace_7823593
  have hstable : (prefixWord ++ tailWord_7823593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823593).length < 2 ^ (prefixWord ++ tailWord_7823593).sum := by decide
  have hdescent : baseEnd_7823593 < baseStart_7823593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823599 : List Nat := [1, 1, 2, 1, 6, 3, 1, 8]
def baseStart_7823599 : Nat := 118140960795 + 7823599 * 2 ^ 59
def prefixEnd_7823599 : Nat := 4983230072969 + 3 ^ 40 * 7823599 * 2
def baseEnd_7823599 : Nat := 148787656853149661727127

theorem tailTrace_7823599 : CollatzResearch.WordTrace tailWord_7823599 prefixEnd_7823599 148787656853149661727127 := by
  unfold tailWord_7823599
  simp only [CollatzResearch.WordTrace]
  refine ⟨285350097983444462176833851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190233398655629641451222567 285350097983444462176833851)
  ·
    refine ⟨428025146975166693265250777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285350097983444462176833851 428025146975166693265250777)
    ·
      refine ⟨321018860231375019948938083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428025146975166693265250777 321018860231375019948938083)
      ·
        refine ⟨481528290347062529923407125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321018860231375019948938083 481528290347062529923407125)
        ·
          refine ⟨22571638610018556090159709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 481528290347062529923407125 22571638610018556090159709)
          ·
            refine ⟨8464364478756958533809891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22571638610018556090159709 8464364478756958533809891)
            ·
              refine ⟨12696546718135437800714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464364478756958533809891 12696546718135437800714837)
              ·
                refine ⟨148787656853149661727127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12696546718135437800714837 148787656853149661727127)
                ·
                  rfl

theorem cell23_7823599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 8].length) (baseStart_7823599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823599 prefixEnd_7823599 := by exact prefixLift 7823599
  have htrace : WordTrace (prefixWord ++ tailWord_7823599) baseStart_7823599 baseEnd_7823599 := by
    simpa [prefixWord, tailWord_7823599, baseEnd_7823599] using wordTrace_append hprefix tailTrace_7823599
  have hstable : (prefixWord ++ tailWord_7823599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823599).length < 2 ^ (prefixWord ++ tailWord_7823599).sum := by decide
  have hdescent : baseEnd_7823599 < baseStart_7823599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823669 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7823669 : Nat := 118140960795 + 7823669 * 2 ^ 59
def prefixEnd_7823669 : Nat := 4983230072969 + 3 ^ 40 * 7823669 * 2
def baseEnd_7823669 : Nat := 4017302678680855592757107

theorem tailTrace_7823669 : CollatzResearch.WordTrace tailWord_7823669 prefixEnd_7823669 4017302678680855592757107 := by
  unfold tailWord_7823669
  simp only [CollatzResearch.WordTrace]
  refine ⟨285352651093190864131882061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190235100728793909421254707 285352651093190864131882061)
  ·
    refine ⟨107007244159946574049455773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285352651093190864131882061 107007244159946574049455773)
    ·
      refine ⟨40127716559979965268545915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107007244159946574049455773 40127716559979965268545915)
      ·
        refine ⟨60191574839969947902818873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40127716559979965268545915 60191574839969947902818873)
        ·
          refine ⟨45143681129977460927114155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60191574839969947902818873 45143681129977460927114155)
          ·
            refine ⟨67715521694966191390671233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45143681129977460927114155 67715521694966191390671233)
            ·
              refine ⟨50786641271224643543003425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67715521694966191390671233 50786641271224643543003425)
              ·
                refine ⟨38089980953418482657252569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50786641271224643543003425 38089980953418482657252569)
                ·
                  refine ⟨28567485715063861992939427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38089980953418482657252569 28567485715063861992939427)
                  ·
                    refine ⟨42851228572595792989409141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28567485715063861992939427 42851228572595792989409141)
                    ·
                      refine ⟨4017302678680855592757107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42851228572595792989409141 4017302678680855592757107)
                      ·
                        rfl

theorem cell23_7823669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7823669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823669 prefixEnd_7823669 := by exact prefixLift 7823669
  have htrace : WordTrace (prefixWord ++ tailWord_7823669) baseStart_7823669 baseEnd_7823669 := by
    simpa [prefixWord, tailWord_7823669, baseEnd_7823669] using wordTrace_append hprefix tailTrace_7823669
  have hstable : (prefixWord ++ tailWord_7823669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823669).length < 2 ^ (prefixWord ++ tailWord_7823669).sum := by decide
  have hdescent : baseEnd_7823669 < baseStart_7823669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823699 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3]
def baseStart_7823699 : Nat := 118140960795 + 7823699 * 2 ^ 59
def prefixEnd_7823699 : Nat := 4983230072969 + 3 ^ 40 * 7823699 * 2
def baseEnd_7823699 : Nat := 4017318083100490475381969

theorem tailTrace_7823699 : CollatzResearch.WordTrace tailWord_7823699 prefixEnd_7823699 4017318083100490475381969 := by
  unfold tailWord_7823699
  simp only [CollatzResearch.WordTrace]
  refine ⟨285353745283082179255474151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190235830188721452836982767 285353745283082179255474151)
  ·
    refine ⟨428030617924623268883211227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285353745283082179255474151 428030617924623268883211227)
    ·
      refine ⟨642045926886934903324816841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428030617924623268883211227 642045926886934903324816841)
      ·
        refine ⟨481534445165201177493612631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642045926886934903324816841 481534445165201177493612631)
        ·
          refine ⟨722301667747801766240418947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481534445165201177493612631 722301667747801766240418947)
          ·
            refine ⟨1083452501621702649360628421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722301667747801766240418947 1083452501621702649360628421)
            ·
              refine ⟨203147344054069246755117829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1083452501621702649360628421 203147344054069246755117829)
              ·
                refine ⟨38090127010137983766584593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203147344054069246755117829 38090127010137983766584593)
                ·
                  refine ⟨28567595257603487824938445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38090127010137983766584593 28567595257603487824938445)
                  ·
                    refine ⟨10712848221601307934351917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28567595257603487824938445 10712848221601307934351917)
                    ·
                      refine ⟨4017318083100490475381969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10712848221601307934351917 4017318083100490475381969)
                      ·
                        rfl

theorem cell23_7823699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_7823699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823699 prefixEnd_7823699 := by exact prefixLift 7823699
  have htrace : WordTrace (prefixWord ++ tailWord_7823699) baseStart_7823699 baseEnd_7823699 := by
    simpa [prefixWord, tailWord_7823699, baseEnd_7823699] using wordTrace_append hprefix tailTrace_7823699
  have hstable : (prefixWord ++ tailWord_7823699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823699).length < 2 ^ (prefixWord ++ tailWord_7823699).sum := by decide
  have hdescent : baseEnd_7823699 < baseStart_7823699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823717 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_7823717 : Nat := 118140960795 + 7823717 * 2 ^ 59
def prefixEnd_7823717 : Nat := 4983230072969 + 3 ^ 40 * 7823717 * 2
def baseEnd_7823717 : Nat := 4017327325752271404956887

theorem tailTrace_7823717 : CollatzResearch.WordTrace tailWord_7823717 prefixEnd_7823717 4017327325752271404956887 := by
  unfold tailWord_7823717
  simp only [CollatzResearch.WordTrace]
  refine ⟨285354401797016968329629405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190236267864677978886419603 285354401797016968329629405)
  ·
    refine ⟨107007900673881363123611027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285354401797016968329629405 107007900673881363123611027)
    ·
      refine ⟨160511851010822044685416541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107007900673881363123611027 160511851010822044685416541)
      ·
        refine ⟨60191944129058266757031203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160511851010822044685416541 60191944129058266757031203)
        ·
          refine ⟨90287916193587400135546805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60191944129058266757031203 90287916193587400135546805)
          ·
            refine ⟨8464492143148818762707513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90287916193587400135546805 8464492143148818762707513)
            ·
              refine ⟨6348369107361614072030635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464492143148818762707513 6348369107361614072030635)
              ·
                refine ⟨9522553661042421108045953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348369107361614072030635 9522553661042421108045953)
                ·
                  refine ⟨7141915245781815831034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522553661042421108045953 7141915245781815831034465)
                  ·
                    refine ⟨5356436434336361873275849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7141915245781815831034465 5356436434336361873275849)
                    ·
                      refine ⟨4017327325752271404956887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356436434336361873275849 4017327325752271404956887)
                      ·
                        rfl

theorem cell23_7823717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_7823717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823717 prefixEnd_7823717 := by exact prefixLift 7823717
  have htrace : WordTrace (prefixWord ++ tailWord_7823717) baseStart_7823717 baseEnd_7823717 := by
    simpa [prefixWord, tailWord_7823717, baseEnd_7823717] using wordTrace_append hprefix tailTrace_7823717
  have hstable : (prefixWord ++ tailWord_7823717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823717).length < 2 ^ (prefixWord ++ tailWord_7823717).sum := by decide
  have hdescent : baseEnd_7823717 < baseStart_7823717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823756 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_7823756 : Nat := 118140960795 + 7823756 * 2 ^ 59
def prefixEnd_7823756 : Nat := 4983230072969 + 3 ^ 40 * 7823756 * 2
def baseEnd_7823756 : Nat := 4017347351497796752369207

theorem tailTrace_7823756 : CollatzResearch.WordTrace tailWord_7823756 prefixEnd_7823756 4017347351497796752369207 := by
  unfold tailWord_7823756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142677912121937838995149561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190237216162583785326866081 142677912121937838995149561)
  ·
    refine ⟨107008434091453379246362171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142677912121937838995149561 107008434091453379246362171)
    ·
      refine ⟨160512651137180068869543257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107008434091453379246362171 160512651137180068869543257)
      ·
        refine ⟨120384488352885051652157443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160512651137180068869543257 120384488352885051652157443)
        ·
          refine ⟨180576732529327577478236165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120384488352885051652157443 180576732529327577478236165)
          ·
            refine ⟨33858137349248920777169281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180576732529327577478236165 33858137349248920777169281)
            ·
              refine ⟨25393603011936690582876961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33858137349248920777169281 25393603011936690582876961)
              ·
                refine ⟨19045202258952517937157721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25393603011936690582876961 19045202258952517937157721)
                ·
                  refine ⟨14283901694214388452868291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19045202258952517937157721 14283901694214388452868291)
                  ·
                    refine ⟨21425852541321582679302437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14283901694214388452868291 21425852541321582679302437)
                    ·
                      refine ⟨4017347351497796752369207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21425852541321582679302437 4017347351497796752369207)
                      ·
                        rfl

theorem cell23_7823756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_7823756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823756 prefixEnd_7823756 := by exact prefixLift 7823756
  have htrace : WordTrace (prefixWord ++ tailWord_7823756) baseStart_7823756 baseEnd_7823756 := by
    simpa [prefixWord, tailWord_7823756, baseEnd_7823756] using wordTrace_append hprefix tailTrace_7823756
  have hstable : (prefixWord ++ tailWord_7823756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823756).length < 2 ^ (prefixWord ++ tailWord_7823756).sum := by decide
  have hdescent : baseEnd_7823756 < baseStart_7823756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823783 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7823783 : Nat := 118140960795 + 7823783 * 2 ^ 59
def prefixEnd_7823783 : Nat := 4983230072969 + 3 ^ 40 * 7823783 * 2
def baseEnd_7823783 : Nat := 1339120405158489382243861

theorem tailTrace_7823783 : CollatzResearch.WordTrace tailWord_7823783 prefixEnd_7823783 1339120405158489382243861 := by
  unfold tailWord_7823783
  simp only [CollatzResearch.WordTrace]
  refine ⟨285356809014777861601532003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190237872676518574401021335 285356809014777861601532003)
  ·
    refine ⟨428035213522166792402298005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285356809014777861601532003 428035213522166792402298005)
    ·
      refine ⟨20064150633851568393857719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 428035213522166792402298005 20064150633851568393857719)
      ·
        refine ⟨30096225950777352590786579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064150633851568393857719 30096225950777352590786579)
        ·
          refine ⟨45144338926166028886179869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30096225950777352590786579 45144338926166028886179869)
          ·
            refine ⟨16929127097312260832317451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45144338926166028886179869 16929127097312260832317451)
            ·
              refine ⟨25393690645968391248476177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16929127097312260832317451 25393690645968391248476177)
              ·
                refine ⟨19045267984476293436357133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25393690645968391248476177 19045267984476293436357133)
                ·
                  refine ⟨7141975494178610038633925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19045267984476293436357133 7141975494178610038633925)
                  ·
                    refine ⟨1339120405158489382243861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141975494178610038633925 1339120405158489382243861)
                    ·
                      rfl

theorem cell23_7823783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7823783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823783 prefixEnd_7823783 := by exact prefixLift 7823783
  have htrace : WordTrace (prefixWord ++ tailWord_7823783) baseStart_7823783 baseEnd_7823783 := by
    simpa [prefixWord, tailWord_7823783, baseEnd_7823783] using wordTrace_append hprefix tailTrace_7823783
  have hstable : (prefixWord ++ tailWord_7823783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823783).length < 2 ^ (prefixWord ++ tailWord_7823783).sum := by decide
  have hdescent : baseEnd_7823783 < baseStart_7823783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823793 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7823793 : Nat := 118140960795 + 7823793 * 2 ^ 59
def prefixEnd_7823793 : Nat := 4983230072969 + 3 ^ 40 * 7823793 * 2
def baseEnd_7823793 : Nat := 4017366350282013107606537

theorem tailTrace_7823793 : CollatzResearch.WordTrace tailWord_7823793 prefixEnd_7823793 4017366350282013107606537 := by
  unfold tailWord_7823793
  simp only [CollatzResearch.WordTrace]
  refine ⟨285357173744741633309396033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190238115829827755539597355 285357173744741633309396033)
  ·
    refine ⟨214017880308556224982047025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285357173744741633309396033 214017880308556224982047025)
    ·
      refine ⟨160513410231417168736535269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214017880308556224982047025 160513410231417168736535269)
      ·
        refine ⟨30096264418390719138100363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160513410231417168736535269 30096264418390719138100363)
        ·
          refine ⟨45144396627586078707150545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30096264418390719138100363 45144396627586078707150545)
          ·
            refine ⟨33858297470689559030362909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45144396627586078707150545 33858297470689559030362909)
            ·
              refine ⟨12696861551508584636386091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33858297470689559030362909 12696861551508584636386091)
              ·
                refine ⟨19045292327262876954579137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696861551508584636386091 19045292327262876954579137)
                ·
                  refine ⟨14283969245447157715934353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19045292327262876954579137 14283969245447157715934353)
                  ·
                    refine ⟨10712976934085368286950765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14283969245447157715934353 10712976934085368286950765)
                    ·
                      refine ⟨4017366350282013107606537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10712976934085368286950765 4017366350282013107606537)
                      ·
                        rfl

theorem cell23_7823793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7823793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823793 prefixEnd_7823793 := by exact prefixLift 7823793
  have htrace : WordTrace (prefixWord ++ tailWord_7823793) baseStart_7823793 baseEnd_7823793 := by
    simpa [prefixWord, tailWord_7823793, baseEnd_7823793] using wordTrace_append hprefix tailTrace_7823793
  have hstable : (prefixWord ++ tailWord_7823793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823793).length < 2 ^ (prefixWord ++ tailWord_7823793).sum := by decide
  have hdescent : baseEnd_7823793 < baseStart_7823793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823830 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_7823830 : Nat := 118140960795 + 7823830 * 2 ^ 59
def prefixEnd_7823830 : Nat := 4983230072969 + 3 ^ 40 * 7823830 * 2
def baseEnd_7823830 : Nat := 446376149896247718093763

theorem tailTrace_7823830 : CollatzResearch.WordTrace tailWord_7823830 prefixEnd_7823830 446376149896247718093763 := by
  unfold tailWord_7823830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17834907702850474289280809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190239015497071725752328629 17834907702850474289280809)
  ·
    refine ⟨13376180777137855716960607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17834907702850474289280809 13376180777137855716960607)
    ·
      refine ⟨20064271165706783575440911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376180777137855716960607 20064271165706783575440911)
      ·
        refine ⟨30096406748560175363161367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064271165706783575440911 30096406748560175363161367)
        ·
          refine ⟨45144610122840263044742051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30096406748560175363161367 45144610122840263044742051)
          ·
            refine ⟨67716915184260394567113077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45144610122840263044742051 67716915184260394567113077)
            ·
              refine ⟨6348460798524411990666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67716915184260394567113077 6348460798524411990666851)
              ·
                refine ⟨9522691197786617986000277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348460798524411990666851 9522691197786617986000277)
                ·
                  refine ⟨446376149896247718093763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9522691197786617986000277 446376149896247718093763)
                  ·
                    rfl

theorem cell23_7823830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_7823830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823830 prefixEnd_7823830 := by exact prefixLift 7823830
  have htrace : WordTrace (prefixWord ++ tailWord_7823830) baseStart_7823830 baseEnd_7823830 := by
    simpa [prefixWord, tailWord_7823830, baseEnd_7823830] using wordTrace_append hprefix tailTrace_7823830
  have hstable : (prefixWord ++ tailWord_7823830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823830).length < 2 ^ (prefixWord ++ tailWord_7823830).sum := by decide
  have hdescent : baseEnd_7823830 < baseStart_7823830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823856 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_7823856 : Nat := 118140960795 + 7823856 * 2 ^ 59
def prefixEnd_7823856 : Nat := 4983230072969 + 3 ^ 40 * 7823856 * 2
def baseEnd_7823856 : Nat := 1339132899854415453706249

theorem tailTrace_7823856 : CollatzResearch.WordTrace tailWord_7823856 prefixEnd_7823856 1339132899854415453706249 := by
  unfold tailWord_7823856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142679735771756697534469711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190239647695675596712626281 142679735771756697534469711)
  ·
    refine ⟨214019603657635046301704567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142679735771756697534469711 214019603657635046301704567)
    ·
      refine ⟨321029405486452569452556851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214019603657635046301704567 321029405486452569452556851)
      ·
        refine ⟨481544108229678854178835277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321029405486452569452556851 481544108229678854178835277)
        ·
          refine ⟨180579040586129570317063229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481544108229678854178835277 180579040586129570317063229)
          ·
            refine ⟨67717140219798588868898711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180579040586129570317063229 67717140219798588868898711)
            ·
              refine ⟨101575710329697883303348067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67717140219798588868898711 101575710329697883303348067)
              ·
                refine ⟨152363565494546824955022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101575710329697883303348067 152363565494546824955022101)
                ·
                  refine ⟨7142042132556882419766661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152363565494546824955022101 7142042132556882419766661)
                  ·
                    refine ⟨1339132899854415453706249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142042132556882419766661 1339132899854415453706249)
                    ·
                      rfl

theorem cell23_7823856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_7823856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823856 prefixEnd_7823856 := by exact prefixLift 7823856
  have htrace : WordTrace (prefixWord ++ tailWord_7823856) baseStart_7823856 baseEnd_7823856 := by
    simpa [prefixWord, tailWord_7823856, baseEnd_7823856] using wordTrace_append hprefix tailTrace_7823856
  have hstable : (prefixWord ++ tailWord_7823856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823856).length < 2 ^ (prefixWord ++ tailWord_7823856).sum := by decide
  have hdescent : baseEnd_7823856 < baseStart_7823856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823873 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_7823873 : Nat := 118140960795 + 7823873 * 2 ^ 59
def prefixEnd_7823873 : Nat := 4983230072969 + 3 ^ 40 * 7823873 * 2
def baseEnd_7823873 : Nat := 1339135809578124264868723

theorem tailTrace_7823873 : CollatzResearch.WordTrace tailWord_7823873 prefixEnd_7823873 1339135809578124264868723 := by
  unfold tailWord_7823873
  simp only [CollatzResearch.WordTrace]
  refine ⟨285360091584451806972308273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190240061056301204648205515 285360091584451806972308273)
  ·
    refine ⟨214020068688338855229231205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285360091584451806972308273 214020068688338855229231205)
    ·
      refine ⟨40128762879063535355480851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214020068688338855229231205 40128762879063535355480851)
      ·
        refine ⟨60193144318595303033221277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40128762879063535355480851 60193144318595303033221277)
        ·
          refine ⟨22572429119473238637457979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60193144318595303033221277 22572429119473238637457979)
          ·
            refine ⟨33858643679209857956186969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22572429119473238637457979 33858643679209857956186969)
            ·
              refine ⟨25393982759407393467140227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33858643679209857956186969 25393982759407393467140227)
              ·
                refine ⟨38090974139111090200710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25393982759407393467140227 38090974139111090200710341)
                ·
                  refine ⟨7142057651083329412633189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38090974139111090200710341 7142057651083329412633189)
                  ·
                    refine ⟨1339135809578124264868723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142057651083329412633189 1339135809578124264868723)
                    ·
                      rfl

theorem cell23_7823873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_7823873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823873 prefixEnd_7823873 := by exact prefixLift 7823873
  have htrace : WordTrace (prefixWord ++ tailWord_7823873) baseStart_7823873 baseEnd_7823873 := by
    simpa [prefixWord, tailWord_7823873, baseEnd_7823873] using wordTrace_append hprefix tailTrace_7823873
  have hstable : (prefixWord ++ tailWord_7823873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823873).length < 2 ^ (prefixWord ++ tailWord_7823873).sum := by decide
  have hdescent : baseEnd_7823873 < baseStart_7823873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823874 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7823874 : Nat := 118140960795 + 7823874 * 2 ^ 59
def prefixEnd_7823874 : Nat := 4983230072969 + 3 ^ 40 * 7823874 * 2
def baseEnd_7823874 : Nat := 4017407942215027290693665

theorem tailTrace_7823874 : CollatzResearch.WordTrace tailWord_7823874 prefixEnd_7823874 4017407942215027290693665 := by
  unfold tailWord_7823874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340032014362046035773669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190240085371632122762063117 71340032014362046035773669)
  ·
    refine ⟨13376256002692883631707563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71340032014362046035773669 13376256002692883631707563)
    ·
      refine ⟨20064384004039325447561345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376256002692883631707563 20064384004039325447561345)
      ·
        refine ⟨15048288003029494085671009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20064384004039325447561345 15048288003029494085671009)
        ·
          refine ⟨11286216002272120564253257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15048288003029494085671009 11286216002272120564253257)
          ·
            refine ⟨8464662001704090423189943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286216002272120564253257 8464662001704090423189943)
            ·
              refine ⟨12696993002556135634784915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464662001704090423189943 12696993002556135634784915)
              ·
                refine ⟨19045489503834203452177373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696993002556135634784915 19045489503834203452177373)
                ·
                  refine ⟨7142058563937826294566515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19045489503834203452177373 7142058563937826294566515)
                  ·
                    refine ⟨10713087845906739441849773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7142058563937826294566515 10713087845906739441849773)
                    ·
                      refine ⟨4017407942215027290693665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713087845906739441849773 4017407942215027290693665)
                      ·
                        rfl

theorem cell23_7823874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7823874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823874 prefixEnd_7823874 := by exact prefixLift 7823874
  have htrace : WordTrace (prefixWord ++ tailWord_7823874) baseStart_7823874 baseEnd_7823874 := by
    simpa [prefixWord, tailWord_7823874, baseEnd_7823874] using wordTrace_append hprefix tailTrace_7823874
  have hstable : (prefixWord ++ tailWord_7823874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823874).length < 2 ^ (prefixWord ++ tailWord_7823874).sum := by decide
  have hdescent : baseEnd_7823874 < baseStart_7823874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823886 : List Nat := [4, 1, 1, 2, 3, 1, 1, 10]
def baseStart_7823886 : Nat := 118140960795 + 7823886 * 2 ^ 59
def prefixEnd_7823886 : Nat := 4983230072969 + 3 ^ 40 * 7823886 * 2
def baseEnd_7823886 : Nat := 148793114962328934953467

theorem tailTrace_7823886 : CollatzResearch.WordTrace tailWord_7823886 prefixEnd_7823886 148793114962328934953467 := by
  unfold tailWord_7823886
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670070716675588774066439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190240377155603140128354341 35670070716675588774066439)
  ·
    refine ⟨53505106075013383161099659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35670070716675588774066439 53505106075013383161099659)
    ·
      refine ⟨80257659112520074741649489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53505106075013383161099659 80257659112520074741649489)
      ·
        refine ⟨60193244334390056056237117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80257659112520074741649489 60193244334390056056237117)
        ·
          refine ⟨22572466625396271021088919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60193244334390056056237117 22572466625396271021088919)
          ·
            refine ⟨33858699938094406531633379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22572466625396271021088919 33858699938094406531633379)
            ·
              refine ⟨50788049907141609797450069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33858699938094406531633379 50788049907141609797450069)
              ·
                refine ⟨148793114962328934953467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50788049907141609797450069 148793114962328934953467)
                ·
                  rfl

theorem cell23_7823886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_7823886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823886 prefixEnd_7823886 := by exact prefixLift 7823886
  have htrace : WordTrace (prefixWord ++ tailWord_7823886) baseStart_7823886 baseEnd_7823886 := by
    simpa [prefixWord, tailWord_7823886, baseEnd_7823886] using wordTrace_append hprefix tailTrace_7823886
  have hstable : (prefixWord ++ tailWord_7823886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823886).length < 2 ^ (prefixWord ++ tailWord_7823886).sum := by decide
  have hdescent : baseEnd_7823886 < baseStart_7823886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823900 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7823900 : Nat := 118140960795 + 7823900 * 2 ^ 59
def prefixEnd_7823900 : Nat := 4983230072969 + 3 ^ 40 * 7823900 * 2
def baseEnd_7823900 : Nat := 4017421292712044188968545

theorem tailTrace_7823900 : CollatzResearch.WordTrace tailWord_7823900 prefixEnd_7823900 4017421292712044188968545 := by
  unfold tailWord_7823900
  simp only [CollatzResearch.WordTrace]
  refine ⟨142680538177676995291770577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190240717570235993722360769 142680538177676995291770577)
  ·
    refine ⟨107010403633257746468827933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142680538177676995291770577 107010403633257746468827933)
    ·
      refine ⟨40128901362471654925810475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107010403633257746468827933 40128901362471654925810475)
      ·
        refine ⟨60193352043707482388715713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40128901362471654925810475 60193352043707482388715713)
        ·
          refine ⟨45145014032780611791536785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60193352043707482388715713 45145014032780611791536785)
          ·
            refine ⟨33858760524585458843652589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45145014032780611791536785 33858760524585458843652589)
            ·
              refine ⟨12697035196719547066369721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33858760524585458843652589 12697035196719547066369721)
              ·
                refine ⟨9522776397539660299777291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12697035196719547066369721 9522776397539660299777291)
                ·
                  refine ⟨14284164596309490449665937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522776397539660299777291 14284164596309490449665937)
                  ·
                    refine ⟨10713123447232117837249453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14284164596309490449665937 10713123447232117837249453)
                    ·
                      refine ⟨4017421292712044188968545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713123447232117837249453 4017421292712044188968545)
                      ·
                        rfl

theorem cell23_7823900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7823900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823900 prefixEnd_7823900 := by exact prefixLift 7823900
  have htrace : WordTrace (prefixWord ++ tailWord_7823900) baseStart_7823900 baseEnd_7823900 := by
    simpa [prefixWord, tailWord_7823900, baseEnd_7823900] using wordTrace_append hprefix tailTrace_7823900
  have hstable : (prefixWord ++ tailWord_7823900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823900).length < 2 ^ (prefixWord ++ tailWord_7823900).sum := by decide
  have hdescent : baseEnd_7823900 < baseStart_7823900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823924 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_7823924 : Nat := 118140960795 + 7823924 * 2 ^ 59
def prefixEnd_7823924 : Nat := 4983230072969 + 3 ^ 40 * 7823924 * 2
def baseEnd_7823924 : Nat := 1339144538749250698356145

theorem tailTrace_7823924 : CollatzResearch.WordTrace tailWord_7823924 prefixEnd_7823924 1339144538749250698356145 := by
  unfold tailWord_7823924
  simp only [CollatzResearch.WordTrace]
  refine ⟨142680975853633521341207413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190241301138178028454943217 142680975853633521341207413)
  ·
    refine ⟨13376341486278142625738195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142680975853633521341207413 13376341486278142625738195)
    ·
      refine ⟨20064512229417213938607293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376341486278142625738195 20064512229417213938607293)
      ·
        refine ⟨7524192086031455226977735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20064512229417213938607293 7524192086031455226977735)
        ·
          refine ⟨11286288129047182840466603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524192086031455226977735 11286288129047182840466603)
          ·
            refine ⟨16929432193570774260699905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286288129047182840466603 16929432193570774260699905)
            ·
              refine ⟨12697074145178080695524929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929432193570774260699905 12697074145178080695524929)
              ·
                refine ⟨9522805608883560521643697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12697074145178080695524929 9522805608883560521643697)
                ·
                  refine ⟨7142104206662670391232773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522805608883560521643697 7142104206662670391232773)
                  ·
                    refine ⟨1339144538749250698356145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142104206662670391232773 1339144538749250698356145)
                    ·
                      rfl

theorem cell23_7823924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_7823924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823924 prefixEnd_7823924 := by exact prefixLift 7823924
  have htrace : WordTrace (prefixWord ++ tailWord_7823924) baseStart_7823924 baseEnd_7823924 := by
    simpa [prefixWord, tailWord_7823924, baseEnd_7823924] using wordTrace_append hprefix tailTrace_7823924
  have hstable : (prefixWord ++ tailWord_7823924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823924).length < 2 ^ (prefixWord ++ tailWord_7823924).sum := by decide
  have hdescent : baseEnd_7823924 < baseStart_7823924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823930 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_7823930 : Nat := 118140960795 + 7823930 * 2 ^ 59
def prefixEnd_7823930 : Nat := 4983230072969 + 3 ^ 40 * 7823930 * 2
def baseEnd_7823930 : Nat := 4017436697131679071593407

theorem tailTrace_7823930 : CollatzResearch.WordTrace tailWord_7823930 prefixEnd_7823930 4017436697131679071593407 := by
  unfold tailWord_7823930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340542636311326426783311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190241447030163537138088829 71340542636311326426783311)
  ·
    refine ⟨107010813954466989640174967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340542636311326426783311 107010813954466989640174967)
    ·
      refine ⟨160516220931700484460262451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107010813954466989640174967 160516220931700484460262451)
      ·
        refine ⟨240774331397550726690393677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160516220931700484460262451 240774331397550726690393677)
        ·
          refine ⟨90290374274081522508897629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240774331397550726690393677 90290374274081522508897629)
          ·
            refine ⟨33858890352780570940836611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90290374274081522508897629 33858890352780570940836611)
            ·
              refine ⟨50788335529170856411254917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33858890352780570940836611 50788335529170856411254917)
              ·
                refine ⟨9522812911719535577110297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50788335529170856411254917 9522812911719535577110297)
                ·
                  refine ⟨7142109683789651682832723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522812911719535577110297 7142109683789651682832723)
                  ·
                    refine ⟨10713164525684477524249085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7142109683789651682832723 10713164525684477524249085)
                    ·
                      refine ⟨4017436697131679071593407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713164525684477524249085 4017436697131679071593407)
                      ·
                        rfl

theorem cell23_7823930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_7823930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823930 prefixEnd_7823930 := by exact prefixLift 7823930
  have htrace : WordTrace (prefixWord ++ tailWord_7823930) baseStart_7823930 baseEnd_7823930 := by
    simpa [prefixWord, tailWord_7823930, baseEnd_7823930] using wordTrace_append hprefix tailTrace_7823930
  have hstable : (prefixWord ++ tailWord_7823930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823930).length < 2 ^ (prefixWord ++ tailWord_7823930).sum := by decide
  have hdescent : baseEnd_7823930 < baseStart_7823930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823936 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_7823936 : Nat := 118140960795 + 7823936 * 2 ^ 59
def prefixEnd_7823936 : Nat := 4983230072969 + 3 ^ 40 * 7823936 * 2
def baseEnd_7823936 : Nat := 4017439778015606048118379

theorem tailTrace_7823936 : CollatzResearch.WordTrace tailWord_7823936 prefixEnd_7823936 4017439778015606048118379 := by
  unfold tailWord_7823936
  simp only [CollatzResearch.WordTrace]
  refine ⟨142681194691611784365925831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190241592922149045821234441 142681194691611784365925831)
  ·
    refine ⟨214021792037417676548888747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142681194691611784365925831 214021792037417676548888747)
    ·
      refine ⟨321032688056126514823333121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214021792037417676548888747 321032688056126514823333121)
      ·
        refine ⟨240774516042094886117499841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321032688056126514823333121 240774516042094886117499841)
        ·
          refine ⟨180580887031571164588124881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240774516042094886117499841 180580887031571164588124881)
          ·
            refine ⟨135435665273678373441093661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180580887031571164588124881 135435665273678373441093661)
            ·
              refine ⟨50788374477629390040410123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135435665273678373441093661 50788374477629390040410123)
              ·
                refine ⟨76182561716444085060615185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50788374477629390040410123 76182561716444085060615185)
                ·
                  refine ⟨57136921287333063795461389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76182561716444085060615185 57136921287333063795461389)
                  ·
                    refine ⟨21426345482749898923298021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57136921287333063795461389 21426345482749898923298021)
                    ·
                      refine ⟨4017439778015606048118379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21426345482749898923298021 4017439778015606048118379)
                      ·
                        rfl

theorem cell23_7823936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_7823936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823936 prefixEnd_7823936 := by exact prefixLift 7823936
  have htrace : WordTrace (prefixWord ++ tailWord_7823936) baseStart_7823936 baseEnd_7823936 := by
    simpa [prefixWord, tailWord_7823936, baseEnd_7823936] using wordTrace_append hprefix tailTrace_7823936
  have hstable : (prefixWord ++ tailWord_7823936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823936).length < 2 ^ (prefixWord ++ tailWord_7823936).sum := by decide
  have hdescent : baseEnd_7823936 < baseStart_7823936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823946 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_7823946 : Nat := 118140960795 + 7823946 * 2 ^ 59
def prefixEnd_7823946 : Nat := 4983230072969 + 3 ^ 40 * 7823946 * 2
def baseEnd_7823946 : Nat := 1339148304274050336331111

theorem tailTrace_7823946 : CollatzResearch.WordTrace tailWord_7823946 prefixEnd_7823946 1339148304274050336331111 := by
  unfold tailWord_7823946
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340688528296835109928923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190241836075458226959810461 71340688528296835109928923)
  ·
    refine ⟨107011032792445252664893385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340688528296835109928923 107011032792445252664893385)
    ·
      refine ⟨80258274594333939498670039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107011032792445252664893385 80258274594333939498670039)
      ·
        refine ⟨120387411891500909248005059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80258274594333939498670039 120387411891500909248005059)
        ·
          refine ⟨180581117837251363872007589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120387411891500909248005059 180581117837251363872007589)
          ·
            refine ⟨33858959594484630726001423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180581117837251363872007589 33858959594484630726001423)
            ·
              refine ⟨50788439391726946089002135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33858959594484630726001423 50788439391726946089002135)
              ·
                refine ⟨76182659087590419133503203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50788439391726946089002135 76182659087590419133503203)
                ·
                  refine ⟨114273988631385628700254805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76182659087590419133503203 114273988631385628700254805)
                  ·
                    refine ⟨1339148304274050336331111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114273988631385628700254805 1339148304274050336331111)
                    ·
                      rfl

theorem cell23_7823946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_7823946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823946 prefixEnd_7823946 := by exact prefixLift 7823946
  have htrace : WordTrace (prefixWord ++ tailWord_7823946) baseStart_7823946 baseEnd_7823946 := by
    simpa [prefixWord, tailWord_7823946, baseEnd_7823946] using wordTrace_append hprefix tailTrace_7823946
  have hstable : (prefixWord ++ tailWord_7823946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823946).length < 2 ^ (prefixWord ++ tailWord_7823946).sum := by decide
  have hdescent : baseEnd_7823946 < baseStart_7823946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7823993 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 7]
def baseStart_7823993 : Nat := 118140960795 + 7823993 * 2 ^ 59
def prefixEnd_7823993 : Nat := 4983230072969 + 3 ^ 40 * 7823993 * 2
def baseEnd_7823993 : Nat := 446385449601434702789513

theorem tailTrace_7823993 : CollatzResearch.WordTrace tailWord_7823993 prefixEnd_7823993 446385449601434702789513 := by
  unfold tailWord_7823993
  simp only [CollatzResearch.WordTrace]
  refine ⟨285364468344017067466676633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190242978896011378311117755 285364468344017067466676633)
  ·
    refine ⟨214023351258012800600007475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285364468344017067466676633 214023351258012800600007475)
    ·
      refine ⟨321035026887019200900011213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214023351258012800600007475 321035026887019200900011213)
      ·
        refine ⟨120388135082632200337504205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321035026887019200900011213 120388135082632200337504205)
        ·
          refine ⟨45145550655987075126564077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120388135082632200337504205 45145550655987075126564077)
          ·
            refine ⟨16929581495995153172461529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45145550655987075126564077 16929581495995153172461529)
            ·
              refine ⟨12697186121996364879346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929581495995153172461529 12697186121996364879346147)
              ·
                refine ⟨19045779182994547319019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12697186121996364879346147 19045779182994547319019221)
                ·
                  refine ⟨446385449601434702789513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19045779182994547319019221 446385449601434702789513)
                  ·
                    rfl

theorem cell23_7823993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_7823993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7823993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7823993 prefixEnd_7823993 := by exact prefixLift 7823993
  have htrace : WordTrace (prefixWord ++ tailWord_7823993) baseStart_7823993 baseEnd_7823993 := by
    simpa [prefixWord, tailWord_7823993, baseEnd_7823993] using wordTrace_append hprefix tailTrace_7823993
  have hstable : (prefixWord ++ tailWord_7823993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7823993).length < 2 ^ (prefixWord ++ tailWord_7823993).sum := by decide
  have hdescent : baseEnd_7823993 < baseStart_7823993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7823993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824003 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3]
def baseStart_7824003 : Nat := 118140960795 + 7824003 * 2 ^ 59
def prefixEnd_7824003 : Nat := 4983230072969 + 3 ^ 40 * 7824003 * 2
def baseEnd_7824003 : Nat := 4017474181219457285980571

theorem tailTrace_7824003 : CollatzResearch.WordTrace tailWord_7824003 prefixEnd_7824003 4017474181219457285980571 := by
  unfold tailWord_7824003
  simp only [CollatzResearch.WordTrace]
  refine ⟨285364833073980839174540663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190243222049320559449693775 285364833073980839174540663)
  ·
    refine ⟨428047249610971258761810995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285364833073980839174540663 428047249610971258761810995)
    ·
      refine ⟨642070874416456888142716493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428047249610971258761810995 642070874416456888142716493)
      ·
        refine ⟨240776577906171333053518685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642070874416456888142716493 240776577906171333053518685)
        ·
          refine ⟨90291216714814249895069507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240776577906171333053518685 90291216714814249895069507)
          ·
            refine ⟨135436825072221374842604261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90291216714814249895069507 135436825072221374842604261)
            ·
              refine ⟨25394404701041507782988299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135436825072221374842604261 25394404701041507782988299)
              ·
                refine ⟨38091607051562261674482449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25394404701041507782988299 38091607051562261674482449)
                ·
                  refine ⟨28568705288671696255861837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38091607051562261674482449 28568705288671696255861837)
                  ·
                    refine ⟨10713264483251886095948189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28568705288671696255861837 10713264483251886095948189)
                    ·
                      refine ⟨4017474181219457285980571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713264483251886095948189 4017474181219457285980571)
                      ·
                        rfl

theorem cell23_7824003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_7824003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824003 prefixEnd_7824003 := by exact prefixLift 7824003
  have htrace : WordTrace (prefixWord ++ tailWord_7824003) baseStart_7824003 baseEnd_7824003 := by
    simpa [prefixWord, tailWord_7824003, baseEnd_7824003] using wordTrace_append hprefix tailTrace_7824003
  have hstable : (prefixWord ++ tailWord_7824003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824003).length < 2 ^ (prefixWord ++ tailWord_7824003).sum := by decide
  have hdescent : baseEnd_7824003 < baseStart_7824003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824016 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_7824016 : Nat := 118140960795 + 7824016 * 2 ^ 59
def prefixEnd_7824016 : Nat := 4983230072969 + 3 ^ 40 * 7824016 * 2
def baseEnd_7824016 : Nat := 4017480856467965735118011

theorem tailTrace_7824016 : CollatzResearch.WordTrace tailWord_7824016 prefixEnd_7824016 4017480856467965735118011 := by
  unfold tailWord_7824016
  simp only [CollatzResearch.WordTrace]
  refine ⟨142682653611466871197381951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190243538148622494929842601 142682653611466871197381951)
  ·
    refine ⟨214023980417200306796072927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142682653611466871197381951 214023980417200306796072927)
    ·
      refine ⟨321035970625800460194109391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214023980417200306796072927 321035970625800460194109391)
      ·
        refine ⟨481553955938700690291164087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321035970625800460194109391 481553955938700690291164087)
        ·
          refine ⟨722330933908051035436746131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481553955938700690291164087 722330933908051035436746131)
          ·
            refine ⟨1083496400862076553155119197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722330933908051035436746131 1083496400862076553155119197)
            ·
              refine ⟨406311150323278707433169699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1083496400862076553155119197 406311150323278707433169699)
              ·
                refine ⟨609466725484918061149754549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406311150323278707433169699 609466725484918061149754549)
                ·
                  refine ⟨57137505514211068232789489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609466725484918061149754549 57137505514211068232789489)
                  ·
                    refine ⟨42853129135658301174592117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57137505514211068232789489 42853129135658301174592117)
                    ·
                      refine ⟨4017480856467965735118011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42853129135658301174592117 4017480856467965735118011)
                      ·
                        rfl

theorem cell23_7824016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_7824016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824016 prefixEnd_7824016 := by exact prefixLift 7824016
  have htrace : WordTrace (prefixWord ++ tailWord_7824016) baseStart_7824016 baseEnd_7824016 := by
    simpa [prefixWord, tailWord_7824016, baseEnd_7824016] using wordTrace_append hprefix tailTrace_7824016
  have hstable : (prefixWord ++ tailWord_7824016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824016).length < 2 ^ (prefixWord ++ tailWord_7824016).sum := by decide
  have hdescent : baseEnd_7824016 < baseStart_7824016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824023 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 2, 5]
def baseStart_7824023 : Nat := 118140960795 + 7824023 * 2 ^ 59
def prefixEnd_7824023 : Nat := 4983230072969 + 3 ^ 40 * 7824023 * 2
def baseEnd_7824023 : Nat := 1339161483610849069243493

theorem tailTrace_7824023 : CollatzResearch.WordTrace tailWord_7824023 prefixEnd_7824023 1339161483610849069243493 := by
  unfold tailWord_7824023
  simp only [CollatzResearch.WordTrace]
  refine ⟨285365562533908382590268723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190243708355938921726845815 285365562533908382590268723)
  ·
    refine ⟨428048343800862573885403085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285365562533908382590268723 428048343800862573885403085)
    ·
      refine ⟨160518128925323465207026157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428048343800862573885403085 160518128925323465207026157)
      ·
        refine ⟨60194298346996299452634809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160518128925323465207026157 60194298346996299452634809)
        ·
          refine ⟨45145723760247224589476107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60194298346996299452634809 45145723760247224589476107)
          ·
            refine ⟨67718585640370836884214161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45145723760247224589476107 67718585640370836884214161)
            ·
              refine ⟨50788939230278127663160621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67718585640370836884214161 50788939230278127663160621)
              ·
                refine ⟨19045852211354297873685233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50788939230278127663160621 19045852211354297873685233)
                ·
                  refine ⟨14284389158515723405263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19045852211354297873685233 14284389158515723405263925)
                  ·
                    refine ⟨1339161483610849069243493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14284389158515723405263925 1339161483610849069243493)
                    ·
                      rfl

theorem cell23_7824023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_7824023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824023 prefixEnd_7824023 := by exact prefixLift 7824023
  have htrace : WordTrace (prefixWord ++ tailWord_7824023) baseStart_7824023 baseEnd_7824023 := by
    simpa [prefixWord, tailWord_7824023, baseEnd_7824023] using wordTrace_append hprefix tailTrace_7824023
  have hstable : (prefixWord ++ tailWord_7824023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824023).length < 2 ^ (prefixWord ++ tailWord_7824023).sum := by decide
  have hdescent : baseEnd_7824023 < baseStart_7824023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824060 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7824060 : Nat := 118140960795 + 7824060 * 2 ^ 59
def prefixEnd_7824060 : Nat := 4983230072969 + 3 ^ 40 * 7824060 * 2
def baseEnd_7824060 : Nat := 4017503449616763562967809

theorem tailTrace_7824060 : CollatzResearch.WordTrace tailWord_7824060 prefixEnd_7824060 4017503449616763562967809 := by
  unfold tailWord_7824060
  simp only [CollatzResearch.WordTrace]
  refine ⟨142683456017387168954682817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190244608023182891939577089 142683456017387168954682817)
  ·
    refine ⟨107012592013040376716012113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142683456017387168954682817 107012592013040376716012113)
    ·
      refine ⟨80259444009780282537009085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107012592013040376716012113 80259444009780282537009085)
      ·
        refine ⟨30097291503667605951378407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80259444009780282537009085 30097291503667605951378407)
        ·
          refine ⟨45145937255501408927067611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30097291503667605951378407 45145937255501408927067611)
          ·
            refine ⟨67718905883252113390601417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45145937255501408927067611 67718905883252113390601417)
            ·
              refine ⟨50789179412439085042951063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67718905883252113390601417 50789179412439085042951063)
              ·
                refine ⟨76183769118658627564426595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50789179412439085042951063 76183769118658627564426595)
                ·
                  refine ⟨114275653677987941346639893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76183769118658627564426595 114275653677987941346639893)
                  ·
                    refine ⟨5356671266155684750623745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114275653677987941346639893 5356671266155684750623745)
                    ·
                      refine ⟨4017503449616763562967809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356671266155684750623745 4017503449616763562967809)
                      ·
                        rfl

theorem cell23_7824060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7824060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824060 prefixEnd_7824060 := by exact prefixLift 7824060
  have htrace : WordTrace (prefixWord ++ tailWord_7824060) baseStart_7824060 baseEnd_7824060 := by
    simpa [prefixWord, tailWord_7824060, baseEnd_7824060] using wordTrace_append hprefix tailTrace_7824060
  have hstable : (prefixWord ++ tailWord_7824060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824060).length < 2 ^ (prefixWord ++ tailWord_7824060).sum := by decide
  have hdescent : baseEnd_7824060 < baseStart_7824060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824100 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 6]
def baseStart_7824100 : Nat := 118140960795 + 7824100 * 2 ^ 59
def prefixEnd_7824100 : Nat := 4983230072969 + 3 ^ 40 * 7824100 * 2
def baseEnd_7824100 : Nat := 446391554315882600718625

theorem tailTrace_7824100 : CollatzResearch.WordTrace tailWord_7824100 prefixEnd_7824100 446391554315882600718625 := by
  unfold tailWord_7824100
  simp only [CollatzResearch.WordTrace]
  refine ⟨142684185477314712370410877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190245580636419616493881169 142684185477314712370410877)
  ·
    refine ⟨53506569553993017138904079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142684185477314712370410877 53506569553993017138904079)
    ·
      refine ⟨80259854330989525708356119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53506569553993017138904079 80259854330989525708356119)
      ·
        refine ⟨120389781496484288562534179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80259854330989525708356119 120389781496484288562534179)
        ·
          refine ⟨180584672244726432843801269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120389781496484288562534179 180584672244726432843801269)
          ·
            refine ⟨16929813022943103079106369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180584672244726432843801269 16929813022943103079106369)
            ·
              refine ⟨12697359767207327309329777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929813022943103079106369 12697359767207327309329777)
              ·
                refine ⟨9523019825405495481997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12697359767207327309329777 9523019825405495481997333)
                ·
                  refine ⟨446391554315882600718625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9523019825405495481997333 446391554315882600718625)
                  ·
                    rfl

theorem cell23_7824100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_7824100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824100 prefixEnd_7824100 := by exact prefixLift 7824100
  have htrace : WordTrace (prefixWord ++ tailWord_7824100) baseStart_7824100 baseEnd_7824100 := by
    simpa [prefixWord, tailWord_7824100, baseEnd_7824100] using wordTrace_append hprefix tailTrace_7824100
  have hstable : (prefixWord ++ tailWord_7824100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824100).length < 2 ^ (prefixWord ++ tailWord_7824100).sum := by decide
  have hdescent : baseEnd_7824100 < baseStart_7824100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824104 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7824104 : Nat := 118140960795 + 7824104 * 2 ^ 59
def prefixEnd_7824104 : Nat := 4983230072969 + 3 ^ 40 * 7824104 * 2
def baseEnd_7824104 : Nat := 1339175347588520463605869

theorem tailTrace_7824104 : CollatzResearch.WordTrace tailWord_7824104 prefixEnd_7824104 1339175347588520463605869 := by
  unfold tailWord_7824104
  simp only [CollatzResearch.WordTrace]
  refine ⟨142684258423307466711983683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190245677897743288949311577 142684258423307466711983683)
  ·
    refine ⟨214026387634961200067975525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142684258423307466711983683 214026387634961200067975525)
    ·
      refine ⟨40129947681555225012745411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214026387634961200067975525 40129947681555225012745411)
      ·
        refine ⟨60194921522332837519118117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40129947681555225012745411 60194921522332837519118117)
        ·
          refine ⟨11286547785437407034834647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60194921522332837519118117 11286547785437407034834647)
          ·
            refine ⟨16929821678156110552251971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286547785437407034834647 16929821678156110552251971)
            ·
              refine ⟨25394732517234165828377957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16929821678156110552251971 25394732517234165828377957)
              ·
                refine ⟨4761512346981406092820867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25394732517234165828377957 4761512346981406092820867)
                ·
                  refine ⟨7142268520472109139231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761512346981406092820867 7142268520472109139231301)
                  ·
                    refine ⟨1339175347588520463605869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142268520472109139231301 1339175347588520463605869)
                    ·
                      rfl

theorem cell23_7824104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7824104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824104 prefixEnd_7824104 := by exact prefixLift 7824104
  have htrace : WordTrace (prefixWord ++ tailWord_7824104) baseStart_7824104 baseEnd_7824104 := by
    simpa [prefixWord, tailWord_7824104, baseEnd_7824104] using wordTrace_append hprefix tailTrace_7824104
  have hstable : (prefixWord ++ tailWord_7824104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824104).length < 2 ^ (prefixWord ++ tailWord_7824104).sum := by decide
  have hdescent : baseEnd_7824104 < baseStart_7824104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824113 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_7824113 : Nat := 118140960795 + 7824113 * 2 ^ 59
def prefixEnd_7824113 : Nat := 4983230072969 + 3 ^ 40 * 7824113 * 2
def baseEnd_7824113 : Nat := 1339176888030483951868355

theorem tailTrace_7824113 : CollatzResearch.WordTrace tailWord_7824113 prefixEnd_7824113 1339176888030483951868355 := by
  unfold tailWord_7824113
  simp only [CollatzResearch.WordTrace]
  refine ⟨285368845103582327961044993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190245896735721551974029995 285368845103582327961044993)
  ·
    refine ⟨214026633827686745970783745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285368845103582327961044993 214026633827686745970783745)
    ·
      refine ⟨160519975370765059478087809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214026633827686745970783745 160519975370765059478087809)
      ·
        refine ⟨120389981528073794608565857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160519975370765059478087809 120389981528073794608565857)
        ·
          refine ⟨90292486146055345956424393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120389981528073794608565857 90292486146055345956424393)
          ·
            refine ⟨67719364609541509467318295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90292486146055345956424393 67719364609541509467318295)
            ·
              refine ⟨101579046914312264200977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67719364609541509467318295 101579046914312264200977443)
              ·
                refine ⟨152368570371468396301466165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101579046914312264200977443 152368570371468396301466165)
                ·
                  refine ⟨14284553472325162153262453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152368570371468396301466165 14284553472325162153262453)
                  ·
                    refine ⟨1339176888030483951868355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14284553472325162153262453 1339176888030483951868355)
                    ·
                      rfl

theorem cell23_7824113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_7824113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824113 prefixEnd_7824113 := by exact prefixLift 7824113
  have htrace : WordTrace (prefixWord ++ tailWord_7824113) baseStart_7824113 baseEnd_7824113 := by
    simpa [prefixWord, tailWord_7824113, baseEnd_7824113] using wordTrace_append hprefix tailTrace_7824113
  have hstable : (prefixWord ++ tailWord_7824113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824113).length < 2 ^ (prefixWord ++ tailWord_7824113).sum := by decide
  have hdescent : baseEnd_7824113 < baseStart_7824113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824120 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_7824120 : Nat := 118140960795 + 7824120 * 2 ^ 59
def prefixEnd_7824120 : Nat := 4983230072969 + 3 ^ 40 * 7824120 * 2
def baseEnd_7824120 : Nat := 4017534258456033328217533

theorem tailTrace_7824120 : CollatzResearch.WordTrace tailWord_7824120 prefixEnd_7824120 4017534258456033328217533 := by
  unfold tailWord_7824120
  simp only [CollatzResearch.WordTrace]
  refine ⟨142684550207278484078274907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190246066943037978771033209 142684550207278484078274907)
  ·
    refine ⟨214026825310917726117412361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142684550207278484078274907 214026825310917726117412361)
    ·
      refine ⟨160520118983188294588059271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214026825310917726117412361 160520118983188294588059271)
      ·
        refine ⟨240780178474782441882088907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160520118983188294588059271 240780178474782441882088907)
        ·
          refine ⟨361170267712173662823133361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240780178474782441882088907 361170267712173662823133361)
          ·
            refine ⟨270877700784130247117350021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361170267712173662823133361 270877700784130247117350021)
            ·
              refine ⟨50789568897024421334503129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270877700784130247117350021 50789568897024421334503129)
              ·
                refine ⟨38092176672768316000877347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50789568897024421334503129 38092176672768316000877347)
                ·
                  refine ⟨57138265009152474001316021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38092176672768316000877347 57138265009152474001316021)
                  ·
                    refine ⟨5356712344608044437623377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57138265009152474001316021 5356712344608044437623377)
                    ·
                      refine ⟨4017534258456033328217533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356712344608044437623377 4017534258456033328217533)
                      ·
                        rfl

theorem cell23_7824120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_7824120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824120 prefixEnd_7824120 := by exact prefixLift 7824120
  have htrace : WordTrace (prefixWord ++ tailWord_7824120) baseStart_7824120 baseEnd_7824120 := by
    simpa [prefixWord, tailWord_7824120, baseEnd_7824120] using wordTrace_append hprefix tailTrace_7824120
  have hstable : (prefixWord ++ tailWord_7824120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824120).length < 2 ^ (prefixWord ++ tailWord_7824120).sum := by decide
  have hdescent : baseEnd_7824120 < baseStart_7824120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824137 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 2, 3, 2]
def baseStart_7824137 : Nat := 118140960795 + 7824137 * 2 ^ 59
def prefixEnd_7824137 : Nat := 4983230072969 + 3 ^ 40 * 7824137 * 2
def baseEnd_7824137 : Nat := 4017542987627159761704955

theorem tailTrace_7824137 : CollatzResearch.WordTrace tailWord_7824137 prefixEnd_7824137 4017542987627159761704955 := by
  unfold tailWord_7824137
  simp only [CollatzResearch.WordTrace]
  refine ⟨285369720455495380059918665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190246480303663586706612443 285369720455495380059918665)
  ·
    refine ⟨214027290341621535044938999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285369720455495380059918665 214027290341621535044938999)
    ·
      refine ⟨321040935512432302567408499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214027290341621535044938999 321040935512432302567408499)
      ·
        refine ⟨481561403268648453851112749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321040935512432302567408499 481561403268648453851112749)
        ·
          refine ⟨180585526225743170194167281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481561403268648453851112749 180585526225743170194167281)
          ·
            refine ⟨135439144669307377645625461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180585526225743170194167281 135439144669307377645625461)
            ·
              refine ⟨12697419812747566654277387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135439144669307377645625461 12697419812747566654277387)
              ·
                refine ⟨19046129719121349981416081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12697419812747566654277387 19046129719121349981416081)
                ·
                  refine ⟨14284597289341012486062061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19046129719121349981416081 14284597289341012486062061)
                  ·
                    refine ⟨5356723983502879682273273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14284597289341012486062061 5356723983502879682273273)
                    ·
                      refine ⟨4017542987627159761704955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356723983502879682273273 4017542987627159761704955)
                      ·
                        rfl

theorem cell23_7824137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 3, 2].length) (baseStart_7824137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824137 prefixEnd_7824137 := by exact prefixLift 7824137
  have htrace : WordTrace (prefixWord ++ tailWord_7824137) baseStart_7824137 baseEnd_7824137 := by
    simpa [prefixWord, tailWord_7824137, baseEnd_7824137] using wordTrace_append hprefix tailTrace_7824137
  have hstable : (prefixWord ++ tailWord_7824137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824137).length < 2 ^ (prefixWord ++ tailWord_7824137).sum := by decide
  have hdescent : baseEnd_7824137 < baseStart_7824137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824143 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 6]
def baseStart_7824143 : Nat := 118140960795 + 7824143 * 2 ^ 59
def prefixEnd_7824143 : Nat := 4983230072969 + 3 ^ 40 * 7824143 * 2
def baseEnd_7824143 : Nat := 1339182022837028912743309

theorem tailTrace_7824143 : CollatzResearch.WordTrace tailWord_7824143 prefixEnd_7824143 1339182022837028912743309 := by
  unfold tailWord_7824143
  simp only [CollatzResearch.WordTrace]
  refine ⟨285369939293473643084637083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190246626195649095389758055 285369939293473643084637083)
  ·
    refine ⟨428054908940210464626955625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285369939293473643084637083 428054908940210464626955625)
    ·
      refine ⟨321041181705157848470216719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428054908940210464626955625 321041181705157848470216719)
      ·
        refine ⟨481561772557736772705325079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321041181705157848470216719 481561772557736772705325079)
        ·
          refine ⟨722342658836605159057987619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481561772557736772705325079 722342658836605159057987619)
          ·
            refine ⟨1083513988254907738586981429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722342658836605159057987619 1083513988254907738586981429)
            ·
              refine ⟨101579436398897600492529509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1083513988254907738586981429 101579436398897600492529509)
              ·
                refine ⟨19046144324793300092349283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101579436398897600492529509 19046144324793300092349283)
                ·
                  refine ⟨28569216487189950138523925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19046144324793300092349283 28569216487189950138523925)
                  ·
                    refine ⟨1339182022837028912743309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28569216487189950138523925 1339182022837028912743309)
                    ·
                      rfl

theorem cell23_7824143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_7824143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824143 prefixEnd_7824143 := by exact prefixLift 7824143
  have htrace : WordTrace (prefixWord ++ tailWord_7824143) baseStart_7824143 baseEnd_7824143 := by
    simpa [prefixWord, tailWord_7824143, baseEnd_7824143] using wordTrace_append hprefix tailTrace_7824143
  have hstable : (prefixWord ++ tailWord_7824143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824143).length < 2 ^ (prefixWord ++ tailWord_7824143).sum := by decide
  have hdescent : baseEnd_7824143 < baseStart_7824143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824163 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7824163 : Nat := 118140960795 + 7824163 * 2 ^ 59
def prefixEnd_7824163 : Nat := 4983230072969 + 3 ^ 40 * 7824163 * 2
def baseEnd_7824163 : Nat := 4017556338124176659979835

theorem tailTrace_7824163 : CollatzResearch.WordTrace tailWord_7824163 prefixEnd_7824163 4017556338124176659979835 := by
  unfold tailWord_7824163
  simp only [CollatzResearch.WordTrace]
  refine ⟨285370668753401186500365143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190247112502267457666910095 285370668753401186500365143)
  ·
    refine ⟨428056003130101779750547715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285370668753401186500365143 428056003130101779750547715)
    ·
      refine ⟨642084004695152669625821573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428056003130101779750547715 642084004695152669625821573)
      ·
        refine ⟨120390750880341125554841545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 642084004695152669625821573 120390750880341125554841545)
        ·
          refine ⟨90293063160255844166131159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120390750880341125554841545 90293063160255844166131159)
          ·
            refine ⟨135439594740383766249196739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90293063160255844166131159 135439594740383766249196739)
            ·
              refine ⟨203159392110575649373795109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135439594740383766249196739 203159392110575649373795109)
              ·
                refine ⟨38092386020732934257586583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203159392110575649373795109 38092386020732934257586583)
                ·
                  refine ⟨57138579031099401386379875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38092386020732934257586583 57138579031099401386379875)
                  ·
                    refine ⟨85707868546649102079569813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57138579031099401386379875 85707868546649102079569813)
                    ·
                      refine ⟨4017556338124176659979835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85707868546649102079569813 4017556338124176659979835)
                      ·
                        rfl

theorem cell23_7824163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7824163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824163 prefixEnd_7824163 := by exact prefixLift 7824163
  have htrace : WordTrace (prefixWord ++ tailWord_7824163) baseStart_7824163 baseEnd_7824163 := by
    simpa [prefixWord, tailWord_7824163, baseEnd_7824163] using wordTrace_append hprefix tailTrace_7824163
  have hstable : (prefixWord ++ tailWord_7824163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824163).length < 2 ^ (prefixWord ++ tailWord_7824163).sum := by decide
  have hdescent : baseEnd_7824163 < baseStart_7824163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824200 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_7824200 : Nat := 118140960795 + 7824200 * 2 ^ 59
def prefixEnd_7824200 : Nat := 4983230072969 + 3 ^ 40 * 7824200 * 2
def baseEnd_7824200 : Nat := 4017575336908393015217165

theorem tailTrace_7824200 : CollatzResearch.WordTrace tailWord_7824200 prefixEnd_7824200 4017575336908393015217165 := by
  unfold tailWord_7824200
  simp only [CollatzResearch.WordTrace]
  refine ⟨142686009127133570909731027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190248012169511427879641369 142686009127133570909731027)
  ·
    refine ⟨214029013690700356364596541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142686009127133570909731027 214029013690700356364596541)
    ·
      refine ⟨80260880134012633636723703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214029013690700356364596541 80260880134012633636723703)
      ·
        refine ⟨120391320201018950455085555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80260880134012633636723703 120391320201018950455085555)
        ·
          refine ⟨180586980301528425682628333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120391320201018950455085555 180586980301528425682628333)
          ·
            refine ⟨67720117613073159630985625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180586980301528425682628333 67720117613073159630985625)
            ·
              refine ⟨50790088209804869723239219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67720117613073159630985625 50790088209804869723239219)
              ·
                refine ⟨76185132314707304584858829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50790088209804869723239219 76185132314707304584858829)
                ·
                  refine ⟨28569424618015239219322061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76185132314707304584858829 28569424618015239219322061)
                  ·
                    refine ⟨10713534231755714707245773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28569424618015239219322061 10713534231755714707245773)
                    ·
                      refine ⟨4017575336908393015217165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713534231755714707245773 4017575336908393015217165)
                      ·
                        rfl

theorem cell23_7824200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_7824200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824200 prefixEnd_7824200 := by exact prefixLift 7824200
  have htrace : WordTrace (prefixWord ++ tailWord_7824200) baseStart_7824200 baseEnd_7824200 := by
    simpa [prefixWord, tailWord_7824200, baseEnd_7824200] using wordTrace_append hprefix tailTrace_7824200
  have hstable : (prefixWord ++ tailWord_7824200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824200).length < 2 ^ (prefixWord ++ tailWord_7824200).sum := by decide
  have hdescent : baseEnd_7824200 < baseStart_7824200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824201 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 1, 2, 2]
def baseStart_7824201 : Nat := 118140960795 + 7824201 * 2 ^ 59
def prefixEnd_7824201 : Nat := 4983230072969 + 3 ^ 40 * 7824201 * 2
def baseEnd_7824201 : Nat := 4017575850389047511304661

theorem tailTrace_7824201 : CollatzResearch.WordTrace tailWord_7824201 prefixEnd_7824201 4017575850389047511304661 := by
  unfold tailWord_7824201
  simp only [CollatzResearch.WordTrace]
  refine ⟨285372054727263518990248457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190248036484842345993498971 285372054727263518990248457)
  ·
    refine ⟨214029041045447639242686343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285372054727263518990248457 214029041045447639242686343)
    ·
      refine ⟨321043561568171458864029515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214029041045447639242686343 321043561568171458864029515)
      ·
        refine ⟨481565342352257188296044273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321043561568171458864029515 481565342352257188296044273)
        ·
          refine ⟨361174006764192891222033205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481565342352257188296044273 361174006764192891222033205)
          ·
            refine ⟨33860063134143083552065613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361174006764192891222033205 33860063134143083552065613)
            ·
              refine ⟨12697523675303656332024605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33860063134143083552065613 12697523675303656332024605)
              ·
                refine ⟨4761571378238871124509227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12697523675303656332024605 4761571378238871124509227)
                ·
                  refine ⟨7142357067358306686763841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761571378238871124509227 7142357067358306686763841)
                  ·
                    refine ⟨5356767800518730015072881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142357067358306686763841 5356767800518730015072881)
                    ·
                      refine ⟨4017575850389047511304661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356767800518730015072881 4017575850389047511304661)
                      ·
                        rfl

theorem cell23_7824201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 1, 2, 2].length) (baseStart_7824201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824201 prefixEnd_7824201 := by exact prefixLift 7824201
  have htrace : WordTrace (prefixWord ++ tailWord_7824201) baseStart_7824201 baseEnd_7824201 := by
    simpa [prefixWord, tailWord_7824201, baseEnd_7824201] using wordTrace_append hprefix tailTrace_7824201
  have hstable : (prefixWord ++ tailWord_7824201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824201).length < 2 ^ (prefixWord ++ tailWord_7824201).sum := by decide
  have hdescent : baseEnd_7824201 < baseStart_7824201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824217 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_7824217 : Nat := 118140960795 + 7824217 * 2 ^ 59
def prefixEnd_7824217 : Nat := 4983230072969 + 3 ^ 40 * 7824217 * 2
def baseEnd_7824217 : Nat := 4017584066079519448704587

theorem tailTrace_7824217 : CollatzResearch.WordTrace tailWord_7824217 prefixEnd_7824217 4017584066079519448704587 := by
  unfold tailWord_7824217
  simp only [CollatzResearch.WordTrace]
  refine ⟨285372638295205553722830905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190248425530137035815220603 285372638295205553722830905)
  ·
    refine ⟨214029478721404165292123179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285372638295205553722830905 214029478721404165292123179)
    ·
      refine ⟨321044218082106247938184769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214029478721404165292123179 321044218082106247938184769)
      ·
        refine ⟨240783163561579685953638577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321044218082106247938184769 240783163561579685953638577)
        ·
          refine ⟨180587372671184764465228933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240783163561579685953638577 180587372671184764465228933)
          ·
            refine ⟨33860132375847143337230425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180587372671184764465228933 33860132375847143337230425)
            ·
              refine ⟨25395099281885357502922819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33860132375847143337230425 25395099281885357502922819)
              ·
                refine ⟨38092648922828036254384229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25395099281885357502922819 38092648922828036254384229)
                ·
                  refine ⟨7142371673030256797697043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38092648922828036254384229 7142371673030256797697043)
                  ·
                    refine ⟨10713557509545385196545565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7142371673030256797697043 10713557509545385196545565)
                    ·
                      refine ⟨4017584066079519448704587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713557509545385196545565 4017584066079519448704587)
                      ·
                        rfl

theorem cell23_7824217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_7824217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824217 prefixEnd_7824217 := by exact prefixLift 7824217
  have htrace : WordTrace (prefixWord ++ tailWord_7824217) baseStart_7824217 baseEnd_7824217 := by
    simpa [prefixWord, tailWord_7824217, baseEnd_7824217] using wordTrace_append hprefix tailTrace_7824217
  have hstable : (prefixWord ++ tailWord_7824217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824217).length < 2 ^ (prefixWord ++ tailWord_7824217).sum := by decide
  have hdescent : baseEnd_7824217 < baseStart_7824217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824218 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_7824218 : Nat := 118140960795 + 7824218 * 2 ^ 59
def prefixEnd_7824218 : Nat := 4983230072969 + 3 ^ 40 * 7824218 * 2
def baseEnd_7824218 : Nat := 4017584579560173944792083

theorem tailTrace_7824218 : CollatzResearch.WordTrace tailWord_7824218 prefixEnd_7824218 4017584579560173944792083 := by
  unfold tailWord_7824218
  simp only [CollatzResearch.WordTrace]
  refine ⟨71343168692050482723404327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190248449845467953929078205 71343168692050482723404327)
  ·
    refine ⟨107014753038075724085106491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71343168692050482723404327 107014753038075724085106491)
    ·
      refine ⟨160522129557113586127659737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107014753038075724085106491 160522129557113586127659737)
      ·
        refine ⟨120391597167835189595744803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160522129557113586127659737 120391597167835189595744803)
        ·
          refine ⟨180587395751752784393617205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120391597167835189595744803 180587395751752784393617205)
          ·
            refine ⟨16930068351726823536901613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180587395751752784393617205 16930068351726823536901613)
            ·
              refine ⟨6348775631897558826338105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16930068351726823536901613 6348775631897558826338105)
              ·
                refine ⟨4761581723923169119753579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348775631897558826338105 4761581723923169119753579)
                ·
                  refine ⟨7142372585884753679630369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761581723923169119753579 7142372585884753679630369)
                  ·
                    refine ⟨5356779439413565259722777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142372585884753679630369 5356779439413565259722777)
                    ·
                      refine ⟨4017584579560173944792083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356779439413565259722777 4017584579560173944792083)
                      ·
                        rfl

theorem cell23_7824218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_7824218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824218 prefixEnd_7824218 := by exact prefixLift 7824218
  have htrace : WordTrace (prefixWord ++ tailWord_7824218) baseStart_7824218 baseEnd_7824218 := by
    simpa [prefixWord, tailWord_7824218, baseEnd_7824218] using wordTrace_append hprefix tailTrace_7824218
  have hstable : (prefixWord ++ tailWord_7824218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824218).length < 2 ^ (prefixWord ++ tailWord_7824218).sum := by decide
  have hdescent : baseEnd_7824218 < baseStart_7824218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824238 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_7824238 : Nat := 118140960795 + 7824238 * 2 ^ 59
def prefixEnd_7824238 : Nat := 4983230072969 + 3 ^ 40 * 7824238 * 2
def baseEnd_7824238 : Nat := 4017594849173263866541991

theorem tailTrace_7824238 : CollatzResearch.WordTrace tailWord_7824238 prefixEnd_7824238 4017594849173263866541991 := by
  unfold tailWord_7824238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35671675528516184288668171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190248936152086316206230245 35671675528516184288668171)
  ·
    refine ⟨53507513292774276433002257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35671675528516184288668171 53507513292774276433002257)
    ·
      refine ⟨40130634969580707324751693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53507513292774276433002257 40130634969580707324751693)
      ·
        refine ⟨15048988113592765246781885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40130634969580707324751693 15048988113592765246781885)
        ·
          refine ⟨5643370542597286967543207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15048988113592765246781885 5643370542597286967543207)
          ·
            refine ⟨8465055813895930451314811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643370542597286967543207 8465055813895930451314811)
            ·
              refine ⟨12697583720843895676972217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465055813895930451314811 12697583720843895676972217)
              ·
                refine ⟨9523187790632921757729163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12697583720843895676972217 9523187790632921757729163)
                ·
                  refine ⟨14284781685949382636593745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523187790632921757729163 14284781685949382636593745)
                  ·
                    refine ⟨10713586264462036977445309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14284781685949382636593745 10713586264462036977445309)
                    ·
                      refine ⟨4017594849173263866541991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713586264462036977445309 4017594849173263866541991)
                      ·
                        rfl

theorem cell23_7824238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_7824238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824238 prefixEnd_7824238 := by exact prefixLift 7824238
  have htrace : WordTrace (prefixWord ++ tailWord_7824238) baseStart_7824238 baseEnd_7824238 := by
    simpa [prefixWord, tailWord_7824238, baseEnd_7824238] using wordTrace_append hprefix tailTrace_7824238
  have hstable : (prefixWord ++ tailWord_7824238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824238).length < 2 ^ (prefixWord ++ tailWord_7824238).sum := by decide
  have hdescent : baseEnd_7824238 < baseStart_7824238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824261 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_7824261 : Nat := 118140960795 + 7824261 * 2 ^ 59
def prefixEnd_7824261 : Nat := 4983230072969 + 3 ^ 40 * 7824261 * 2
def baseEnd_7824261 : Nat := 4017606659228317276554385

theorem tailTrace_7824261 : CollatzResearch.WordTrace tailWord_7824261 prefixEnd_7824261 4017606659228317276554385 := by
  unfold tailWord_7824261
  simp only [CollatzResearch.WordTrace]
  refine ⟨285374243107046149237432637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190249495404697432824955091 285374243107046149237432637)
  ·
    refine ⟨107015341165142305964037239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285374243107046149237432637 107015341165142305964037239)
    ·
      refine ⟨160523011747713458946055859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107015341165142305964037239 160523011747713458946055859)
      ·
        refine ⟨240784517621570188419083789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160523011747713458946055859 240784517621570188419083789)
        ·
          refine ⟨90294194108088820657156421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240784517621570188419083789 90294194108088820657156421)
          ·
            refine ⟨16930161395266653873216829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90294194108088820657156421 16930161395266653873216829)
            ·
              refine ⟨6348810523224995202456311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16930161395266653873216829 6348810523224995202456311)
              ·
                refine ⟨9523215784837492803684467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348810523224995202456311 9523215784837492803684467)
                ·
                  refine ⟨14284823677256239205526701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523215784837492803684467 14284823677256239205526701)
                  ·
                    refine ⟨5356808878971089702072513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14284823677256239205526701 5356808878971089702072513)
                    ·
                      refine ⟨4017606659228317276554385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356808878971089702072513 4017606659228317276554385)
                      ·
                        rfl

theorem cell23_7824261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_7824261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824261 prefixEnd_7824261 := by exact prefixLift 7824261
  have htrace : WordTrace (prefixWord ++ tailWord_7824261) baseStart_7824261 baseEnd_7824261 := by
    simpa [prefixWord, tailWord_7824261, baseEnd_7824261] using wordTrace_append hprefix tailTrace_7824261
  have hstable : (prefixWord ++ tailWord_7824261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824261).length < 2 ^ (prefixWord ++ tailWord_7824261).sum := by decide
  have hdescent : baseEnd_7824261 < baseStart_7824261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824278 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7824278 : Nat := 118140960795 + 7824278 * 2 ^ 59
def prefixEnd_7824278 : Nat := 4983230072969 + 3 ^ 40 * 7824278 * 2
def baseEnd_7824278 : Nat := 4017615388399443710041807

theorem tailTrace_7824278 : CollatzResearch.WordTrace tailWord_7824278 prefixEnd_7824278 4017615388399443710041807 := by
  unfold tailWord_7824278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17835928946749035071300093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190249908765323040760534325 17835928946749035071300093)
  ·
    refine ⟨6688473355030888151737535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17835928946749035071300093 6688473355030888151737535)
    ·
      refine ⟨10032710032546332227606303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688473355030888151737535 10032710032546332227606303)
      ·
        refine ⟨15049065048819498341409455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032710032546332227606303 15049065048819498341409455)
        ·
          refine ⟨22573597573229247512114183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049065048819498341409455 22573597573229247512114183)
          ·
            refine ⟨33860396359843871268171275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22573597573229247512114183 33860396359843871268171275)
            ·
              refine ⟨50790594539765806902256913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33860396359843871268171275 50790594539765806902256913)
              ·
                refine ⟨38092945904824355176692685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50790594539765806902256913 38092945904824355176692685)
                ·
                  refine ⟨14284854714309133191259757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38092945904824355176692685 14284854714309133191259757)
                  ·
                    refine ⟨5356820517865924946722409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14284854714309133191259757 5356820517865924946722409)
                    ·
                      refine ⟨4017615388399443710041807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356820517865924946722409 4017615388399443710041807)
                      ·
                        rfl

theorem cell23_7824278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7824278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824278 prefixEnd_7824278 := by exact prefixLift 7824278
  have htrace : WordTrace (prefixWord ++ tailWord_7824278) baseStart_7824278 baseEnd_7824278 := by
    simpa [prefixWord, tailWord_7824278, baseEnd_7824278] using wordTrace_append hprefix tailTrace_7824278
  have hstable : (prefixWord ++ tailWord_7824278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824278).length < 2 ^ (prefixWord ++ tailWord_7824278).sum := by decide
  have hdescent : baseEnd_7824278 < baseStart_7824278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824287 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7824287 : Nat := 118140960795 + 7824287 * 2 ^ 59
def prefixEnd_7824287 : Nat := 4983230072969 + 3 ^ 40 * 7824287 * 2
def baseEnd_7824287 : Nat := 4017620009725334174829265

theorem tailTrace_7824287 : CollatzResearch.WordTrace tailWord_7824287 prefixEnd_7824287 4017620009725334174829265 := by
  unfold tailWord_7824287
  simp only [CollatzResearch.WordTrace]
  refine ⟨285375191404951955677879115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190250127603301303785252743 285375191404951955677879115)
  ·
    refine ⟨428062787107427933516818673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285375191404951955677879115 428062787107427933516818673)
    ·
      refine ⟨321047090330570950137614005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428062787107427933516818673 321047090330570950137614005)
      ·
        refine ⟨30098164718491026575401313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321047090330570950137614005 30098164718491026575401313)
        ·
          refine ⟨22573623538868269931550985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30098164718491026575401313 22573623538868269931550985)
          ·
            refine ⟨16930217654151202448663239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22573623538868269931550985 16930217654151202448663239)
            ·
              refine ⟨25395326481226803672994859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16930217654151202448663239 25395326481226803672994859)
              ·
                refine ⟨38092989721840205509492289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25395326481226803672994859 38092989721840205509492289)
                ·
                  refine ⟨28569742291380154132119217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38092989721840205509492289 28569742291380154132119217)
                  ·
                    refine ⟨21427306718535115599089413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28569742291380154132119217 21427306718535115599089413)
                    ·
                      refine ⟨4017620009725334174829265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21427306718535115599089413 4017620009725334174829265)
                      ·
                        rfl

theorem cell23_7824287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7824287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824287 prefixEnd_7824287 := by exact prefixLift 7824287
  have htrace : WordTrace (prefixWord ++ tailWord_7824287) baseStart_7824287 baseEnd_7824287 := by
    simpa [prefixWord, tailWord_7824287, baseEnd_7824287] using wordTrace_append hprefix tailTrace_7824287
  have hstable : (prefixWord ++ tailWord_7824287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824287).length < 2 ^ (prefixWord ++ tailWord_7824287).sum := by decide
  have hdescent : baseEnd_7824287 < baseStart_7824287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824367 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_7824367 : Nat := 118140960795 + 7824367 * 2 ^ 59
def prefixEnd_7824367 : Nat := 4983230072969 + 3 ^ 40 * 7824367 * 2
def baseEnd_7824367 : Nat := 4017661088177693861828897

theorem tailTrace_7824367 : CollatzResearch.WordTrace tailWord_7824367 prefixEnd_7824367 4017661088177693861828897 := by
  unfold tailWord_7824367
  simp only [CollatzResearch.WordTrace]
  refine ⟨285378109244662129340791355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190252072829774752893860903 285378109244662129340791355)
  ·
    refine ⟨428067163866993194011187033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285378109244662129340791355 428067163866993194011187033)
    ·
      refine ⟨321050372900244895508390275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428067163866993194011187033 321050372900244895508390275)
      ·
        refine ⟨481575559350367343262585413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321050372900244895508390275 481575559350367343262585413)
        ·
          refine ⟨90295417378193876861734765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481575559350367343262585413 90295417378193876861734765)
          ·
            refine ⟨33860781516822703823150537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90295417378193876861734765 33860781516822703823150537)
            ·
              refine ⟨25395586137617027867362903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33860781516822703823150537 25395586137617027867362903)
              ·
                refine ⟨38093379206425541801044355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25395586137617027867362903 38093379206425541801044355)
                ·
                  refine ⟨57140068809638312701566533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38093379206425541801044355 57140068809638312701566533)
                  ·
                    refine ⟨10713762901807183631543725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57140068809638312701566533 10713762901807183631543725)
                    ·
                      refine ⟨4017661088177693861828897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713762901807183631543725 4017661088177693861828897)
                      ·
                        rfl

theorem cell23_7824367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_7824367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824367 prefixEnd_7824367 := by exact prefixLift 7824367
  have htrace : WordTrace (prefixWord ++ tailWord_7824367) baseStart_7824367 baseEnd_7824367 := by
    simpa [prefixWord, tailWord_7824367, baseEnd_7824367] using wordTrace_append hprefix tailTrace_7824367
  have hstable : (prefixWord ++ tailWord_7824367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824367).length < 2 ^ (prefixWord ++ tailWord_7824367).sum := by decide
  have hdescent : baseEnd_7824367 < baseStart_7824367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824441 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7824441 : Nat := 118140960795 + 7824441 * 2 ^ 59
def prefixEnd_7824441 : Nat := 4983230072969 + 3 ^ 40 * 7824441 * 2
def baseEnd_7824441 : Nat := 4017699085746126572303557

theorem tailTrace_7824441 : CollatzResearch.WordTrace tailWord_7824441 prefixEnd_7824441 4017699085746126572303557 := by
  unfold tailWord_7824441
  simp only [CollatzResearch.WordTrace]
  refine ⟨285380808246394039978985177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190253872164262693319323451 285380808246394039978985177)
  ·
    refine ⟨214035606184795529984238883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285380808246394039978985177 214035606184795529984238883)
    ·
      refine ⟨321053409277193294976358325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214035606184795529984238883 321053409277193294976358325)
      ·
        refine ⟨30098757119736871404033593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321053409277193294976358325 30098757119736871404033593)
        ·
          refine ⟨22574067839802653553025195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30098757119736871404033593 22574067839802653553025195)
          ·
            refine ⟨33861101759703980329537793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574067839802653553025195 33861101759703980329537793)
            ·
              refine ⟨25395826319777985247153345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33861101759703980329537793 25395826319777985247153345)
              ·
                refine ⟨19046869739833488935365009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25395826319777985247153345 19046869739833488935365009)
                ·
                  refine ⟨14285152304875116701523757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19046869739833488935365009 14285152304875116701523757)
                  ·
                    refine ⟨5356932114328168763071409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14285152304875116701523757 5356932114328168763071409)
                    ·
                      refine ⟨4017699085746126572303557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356932114328168763071409 4017699085746126572303557)
                      ·
                        rfl

theorem cell23_7824441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7824441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824441 prefixEnd_7824441 := by exact prefixLift 7824441
  have htrace : WordTrace (prefixWord ++ tailWord_7824441) baseStart_7824441 baseEnd_7824441 := by
    simpa [prefixWord, tailWord_7824441, baseEnd_7824441] using wordTrace_append hprefix tailTrace_7824441
  have hstable : (prefixWord ++ tailWord_7824441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824441).length < 2 ^ (prefixWord ++ tailWord_7824441).sum := by decide
  have hdescent : baseEnd_7824441 < baseStart_7824441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824467 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_7824467 : Nat := 118140960795 + 7824467 * 2 ^ 59
def prefixEnd_7824467 : Nat := 4983230072969 + 3 ^ 40 * 7824467 * 2
def baseEnd_7824467 : Nat := 4017712436243143470578437

theorem tailTrace_7824467 : CollatzResearch.WordTrace tailWord_7824467 prefixEnd_7824467 4017712436243143470578437 := by
  unfold tailWord_7824467
  simp only [CollatzResearch.WordTrace]
  refine ⟨285381756544299846419431655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190254504362866564279621103 285381756544299846419431655)
  ·
    refine ⟨428072634816449769629147483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285381756544299846419431655 428072634816449769629147483)
    ·
      refine ⟨642108952224674654443721225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428072634816449769629147483 642108952224674654443721225)
      ·
        refine ⟨481581714168505990832790919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642108952224674654443721225 481581714168505990832790919)
        ·
          refine ⟨722372571252758986249186379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481581714168505990832790919 722372571252758986249186379)
          ·
            refine ⟨1083558856879138479373779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722372571252758986249186379 1083558856879138479373779569)
            ·
              refine ⟨812669142659353859530334677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083558856879138479373779569 812669142659353859530334677)
              ·
                refine ⟨19046933031078606082742219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 812669142659353859530334677 19046933031078606082742219)
                ·
                  refine ⟨28570399546617909124113329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19046933031078606082742219 28570399546617909124113329)
                  ·
                    refine ⟨21427799659963431843084997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28570399546617909124113329 21427799659963431843084997)
                    ·
                      refine ⟨4017712436243143470578437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21427799659963431843084997 4017712436243143470578437)
                      ·
                        rfl

theorem cell23_7824467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_7824467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824467 prefixEnd_7824467 := by exact prefixLift 7824467
  have htrace : WordTrace (prefixWord ++ tailWord_7824467) baseStart_7824467 baseEnd_7824467 := by
    simpa [prefixWord, tailWord_7824467, baseEnd_7824467] using wordTrace_append hprefix tailTrace_7824467
  have hstable : (prefixWord ++ tailWord_7824467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824467).length < 2 ^ (prefixWord ++ tailWord_7824467).sum := by decide
  have hdescent : baseEnd_7824467 < baseStart_7824467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824488 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7824488 : Nat := 118140960795 + 7824488 * 2 ^ 59
def prefixEnd_7824488 : Nat := 4983230072969 + 3 ^ 40 * 7824488 * 2
def baseEnd_7824488 : Nat := 4017723219336887888415841

theorem tailTrace_7824488 : CollatzResearch.WordTrace tailWord_7824488 prefixEnd_7824488 4017723219336887888415841 := by
  unfold tailWord_7824488
  simp only [CollatzResearch.WordTrace]
  refine ⟨142691261238611883502973059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190255014984815844670630745 142691261238611883502973059)
  ·
    refine ⟨214036891857917825254459589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142691261238611883502973059 214036891857917825254459589)
    ·
      refine ⟨40131917223359592235211173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214036891857917825254459589 40131917223359592235211173)
      ·
        refine ⟨7524734479379923544102095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40131917223359592235211173 7524734479379923544102095)
        ·
          refine ⟨11287101719069885316153143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524734479379923544102095 11287101719069885316153143)
          ·
            refine ⟨16930652578604827974229715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287101719069885316153143 16930652578604827974229715)
            ·
              refine ⟨25395978867907241961344573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16930652578604827974229715 25395978867907241961344573)
              ·
                refine ⟨9523492075465215735504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25395978867907241961344573 9523492075465215735504215)
                ·
                  refine ⟨14285238113197823603256323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523492075465215735504215 14285238113197823603256323)
                  ·
                    refine ⟨21427857169796735404884485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14285238113197823603256323 21427857169796735404884485)
                    ·
                      refine ⟨4017723219336887888415841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21427857169796735404884485 4017723219336887888415841)
                      ·
                        rfl

theorem cell23_7824488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7824488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824488 prefixEnd_7824488 := by exact prefixLift 7824488
  have htrace : WordTrace (prefixWord ++ tailWord_7824488) baseStart_7824488 baseEnd_7824488 := by
    simpa [prefixWord, tailWord_7824488, baseEnd_7824488] using wordTrace_append hprefix tailTrace_7824488
  have hstable : (prefixWord ++ tailWord_7824488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824488).length < 2 ^ (prefixWord ++ tailWord_7824488).sum := by decide
  have hdescent : baseEnd_7824488 < baseStart_7824488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824521 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_7824521 : Nat := 118140960795 + 7824521 * 2 ^ 59
def prefixEnd_7824521 : Nat := 4983230072969 + 3 ^ 40 * 7824521 * 2
def baseEnd_7824521 : Nat := 4017740164198486259303189

theorem tailTrace_7824521 : CollatzResearch.WordTrace tailWord_7824521 prefixEnd_7824521 4017740164198486259303189 := by
  unfold tailWord_7824521
  simp only [CollatzResearch.WordTrace]
  refine ⟨285383726086104213641897417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190255817390736142427931611 285383726086104213641897417)
  ·
    refine ⟨214037794564578160231423063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285383726086104213641897417 214037794564578160231423063)
    ·
      refine ⟨321056691846867240347134595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214037794564578160231423063 321056691846867240347134595)
      ·
        refine ⟨481585037770300860520701893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321056691846867240347134595 481585037770300860520701893)
        ·
          refine ⟨90297194581931411347631605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481585037770300860520701893 90297194581931411347631605)
          ·
            refine ⟨8465361992056069813840463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90297194581931411347631605 8465361992056069813840463)
            ·
              refine ⟨12698042988084104720760695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465361992056069813840463 12698042988084104720760695)
              ·
                refine ⟨19047064482126157081141043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698042988084104720760695 19047064482126157081141043)
                ·
                  refine ⟨28570596723189235621711565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19047064482126157081141043 28570596723189235621711565)
                  ·
                    refine ⟨10713973771195963358141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28570596723189235621711565 10713973771195963358141837)
                    ·
                      refine ⟨4017740164198486259303189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10713973771195963358141837 4017740164198486259303189)
                      ·
                        rfl

theorem cell23_7824521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_7824521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824521 prefixEnd_7824521 := by exact prefixLift 7824521
  have htrace : WordTrace (prefixWord ++ tailWord_7824521) baseStart_7824521 baseEnd_7824521 := by
    simpa [prefixWord, tailWord_7824521, baseEnd_7824521] using wordTrace_append hprefix tailTrace_7824521
  have hstable : (prefixWord ++ tailWord_7824521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824521).length < 2 ^ (prefixWord ++ tailWord_7824521).sum := by decide
  have hdescent : baseEnd_7824521 < baseStart_7824521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824531 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 1, 3, 2]
def baseStart_7824531 : Nat := 118140960795 + 7824531 * 2 ^ 59
def prefixEnd_7824531 : Nat := 4983230072969 + 3 ^ 40 * 7824531 * 2
def baseEnd_7824531 : Nat := 4017745299005031220178143

theorem tailTrace_7824531 : CollatzResearch.WordTrace tailWord_7824531 prefixEnd_7824531 4017745299005031220178143 := by
  unfold tailWord_7824531
  simp only [CollatzResearch.WordTrace]
  refine ⟨285384090816067985349761447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190256060544045323566507631 285384090816067985349761447)
  ·
    refine ⟨428076136224101978024642171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285384090816067985349761447 428076136224101978024642171)
    ·
      refine ⟨642114204336152967036963257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428076136224101978024642171 642114204336152967036963257)
      ·
        refine ⟨481585653252114725277722443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642114204336152967036963257 481585653252114725277722443)
        ·
          refine ⟨722378479878172087916583665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481585653252114725277722443 722378479878172087916583665)
          ·
            refine ⟨541783859908629065937437749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722378479878172087916583665 541783859908629065937437749)
            ·
              refine ⟨50792236866433974931634789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541783859908629065937437749 50792236866433974931634789)
              ·
                refine ⟨9523544412456370299681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50792236866433974931634789 9523544412456370299681523)
                ·
                  refine ⟨14285316618684555449522285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523544412456370299681523 14285316618684555449522285)
                  ·
                    refine ⟨5356993732006708293570857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14285316618684555449522285 5356993732006708293570857)
                    ·
                      refine ⟨4017745299005031220178143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5356993732006708293570857 4017745299005031220178143)
                      ·
                        rfl

theorem cell23_7824531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3, 2].length) (baseStart_7824531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824531 prefixEnd_7824531 := by exact prefixLift 7824531
  have htrace : WordTrace (prefixWord ++ tailWord_7824531) baseStart_7824531 baseEnd_7824531 := by
    simpa [prefixWord, tailWord_7824531, baseEnd_7824531] using wordTrace_append hprefix tailTrace_7824531
  have hstable : (prefixWord ++ tailWord_7824531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824531).length < 2 ^ (prefixWord ++ tailWord_7824531).sum := by decide
  have hdescent : baseEnd_7824531 < baseStart_7824531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824548 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_7824548 : Nat := 118140960795 + 7824548 * 2 ^ 59
def prefixEnd_7824548 : Nat := 4983230072969 + 3 ^ 40 * 7824548 * 2
def baseEnd_7824548 : Nat := 4017754028176157653665565

theorem tailTrace_7824548 : CollatzResearch.WordTrace tailWord_7824548 prefixEnd_7824548 4017754028176157653665565 := by
  unfold tailWord_7824548
  simp only [CollatzResearch.WordTrace]
  refine ⟨142692355428503198626565149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190256473904670931502086865 142692355428503198626565149)
  ·
    refine ⟨53509633285688699484961931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142692355428503198626565149 53509633285688699484961931)
    ·
      refine ⟨80264449928533049227442897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53509633285688699484961931 80264449928533049227442897)
      ·
        refine ⟨60198337446399786920582173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80264449928533049227442897 60198337446399786920582173)
        ·
          refine ⟨22574376542399920095218315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60198337446399786920582173 22574376542399920095218315)
          ·
            refine ⟨33861564813599880142827473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574376542399920095218315 33861564813599880142827473)
            ·
              refine ⟨25396173610199910107120605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33861564813599880142827473 25396173610199910107120605)
              ·
                refine ⟨9523565103824966290170227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25396173610199910107120605 9523565103824966290170227)
                ·
                  refine ⟨14285347655737449435255341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523565103824966290170227 14285347655737449435255341)
                  ·
                    refine ⟨5357005370901543538220753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14285347655737449435255341 5357005370901543538220753)
                    ·
                      refine ⟨4017754028176157653665565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5357005370901543538220753 4017754028176157653665565)
                      ·
                        rfl

theorem cell23_7824548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_7824548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824548 prefixEnd_7824548 := by exact prefixLift 7824548
  have htrace : WordTrace (prefixWord ++ tailWord_7824548) baseStart_7824548 baseEnd_7824548 := by
    simpa [prefixWord, tailWord_7824548, baseEnd_7824548] using wordTrace_append hprefix tailTrace_7824548
  have hstable : (prefixWord ++ tailWord_7824548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824548).length < 2 ^ (prefixWord ++ tailWord_7824548).sum := by decide
  have hdescent : baseEnd_7824548 < baseStart_7824548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824617 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_7824617 : Nat := 118140960795 + 7824617 * 2 ^ 59
def prefixEnd_7824617 : Nat := 4983230072969 + 3 ^ 40 * 7824617 * 2
def baseEnd_7824617 : Nat := 4017789458341317883702747

theorem tailTrace_7824617 : CollatzResearch.WordTrace tailWord_7824617 prefixEnd_7824617 4017789458341317883702747 := by
  unfold tailWord_7824617
  simp only [CollatzResearch.WordTrace]
  refine ⟨285387227493756422037392105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190258151662504281358261403 285387227493756422037392105)
  ·
    refine ⟨214040420620317316528044079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285387227493756422037392105 214040420620317316528044079)
    ·
      refine ⟨321060630930475974792066119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214040420620317316528044079 321060630930475974792066119)
      ·
        refine ⟨481590946395713962188099179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321060630930475974792066119 481590946395713962188099179)
        ·
          refine ⟨722386419593570943282148769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481590946395713962188099179 722386419593570943282148769)
          ·
            refine ⟨541789814695178207461611577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722386419593570943282148769 541789814695178207461611577)
            ·
              refine ⟨406342361021383655596208683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541789814695178207461611577 406342361021383655596208683)
              ·
                refine ⟨609513541532075483394313025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406342361021383655596208683 609513541532075483394313025)
                ·
                  refine ⟨457135156149056612545734769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609513541532075483394313025 457135156149056612545734769)
                  ·
                    refine ⟨342851367111792459409301077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457135156149056612545734769 342851367111792459409301077)
                    ·
                      refine ⟨4017789458341317883702747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 342851367111792459409301077 4017789458341317883702747)
                      ·
                        rfl

theorem cell23_7824617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_7824617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824617 prefixEnd_7824617 := by exact prefixLift 7824617
  have htrace : WordTrace (prefixWord ++ tailWord_7824617) baseStart_7824617 baseEnd_7824617 := by
    simpa [prefixWord, tailWord_7824617, baseEnd_7824617] using wordTrace_append hprefix tailTrace_7824617
  have hstable : (prefixWord ++ tailWord_7824617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824617).length < 2 ^ (prefixWord ++ tailWord_7824617).sum := by decide
  have hdescent : baseEnd_7824617 < baseStart_7824617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824618 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_7824618 : Nat := 118140960795 + 7824618 * 2 ^ 59
def prefixEnd_7824618 : Nat := 4983230072969 + 3 ^ 40 * 7824618 * 2
def baseEnd_7824618 : Nat := 446421107980219153310027

theorem tailTrace_7824618 : CollatzResearch.WordTrace tailWord_7824618 prefixEnd_7824618 446421107980219153310027 := by
  unfold tailWord_7824618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71346815991688199802044627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190258175977835199472119005 71346815991688199802044627)
  ·
    refine ⟨107020223987532299703066941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71346815991688199802044627 107020223987532299703066941)
    ·
      refine ⟨40132583995324612388650103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107020223987532299703066941 40132583995324612388650103)
      ·
        refine ⟨60198875992986918582975155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40132583995324612388650103 60198875992986918582975155)
        ·
          refine ⟨90298313989480377874462733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60198875992986918582975155 90298313989480377874462733)
          ·
            refine ⟨33861867746055141702923525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90298313989480377874462733 33861867746055141702923525)
            ·
              refine ⟨6349100202385339069298161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33861867746055141702923525 6349100202385339069298161)
              ·
                refine ⟨4761825151789004301973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349100202385339069298161 4761825151789004301973621)
                ·
                  refine ⟨446421107980219153310027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761825151789004301973621 446421107980219153310027)
                  ·
                    rfl

theorem cell23_7824618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_7824618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824618 prefixEnd_7824618 := by exact prefixLift 7824618
  have htrace : WordTrace (prefixWord ++ tailWord_7824618) baseStart_7824618 baseEnd_7824618 := by
    simpa [prefixWord, tailWord_7824618, baseEnd_7824618] using wordTrace_append hprefix tailTrace_7824618
  have hstable : (prefixWord ++ tailWord_7824618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824618).length < 2 ^ (prefixWord ++ tailWord_7824618).sum := by decide
  have hdescent : baseEnd_7824618 < baseStart_7824618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824634 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_7824634 : Nat := 118140960795 + 7824634 * 2 ^ 59
def prefixEnd_7824634 : Nat := 4983230072969 + 3 ^ 40 * 7824634 * 2
def baseEnd_7824634 : Nat := 4017798187512444317190169

theorem tailTrace_7824634 : CollatzResearch.WordTrace tailWord_7824634 prefixEnd_7824634 4017798187512444317190169 := by
  unfold tailWord_7824634
  simp only [CollatzResearch.WordTrace]
  refine ⟨71346961883673708485190239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190258565023129889293840637 71346961883673708485190239)
  ·
    refine ⟨107020442825510562727785359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71346961883673708485190239 107020442825510562727785359)
    ·
      refine ⟨160530664238265844091678039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107020442825510562727785359 160530664238265844091678039)
      ·
        refine ⟨240795996357398766137517059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160530664238265844091678039 240795996357398766137517059)
        ·
          refine ⟨361193994536098149206275589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240795996357398766137517059 361193994536098149206275589)
          ·
            refine ⟨67723873975518402976176673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361193994536098149206275589 67723873975518402976176673)
            ·
              refine ⟨50792905481638802232132505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67723873975518402976176673 50792905481638802232132505)
              ·
                refine ⟨38094679111229101674099379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50792905481638802232132505 38094679111229101674099379)
                ·
                  refine ⟨57142018666843652511149069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38094679111229101674099379 57142018666843652511149069)
                  ·
                    refine ⟨21428257000066369691680901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57142018666843652511149069 21428257000066369691680901)
                    ·
                      refine ⟨4017798187512444317190169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21428257000066369691680901 4017798187512444317190169)
                      ·
                        rfl

theorem cell23_7824634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_7824634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824634 prefixEnd_7824634 := by exact prefixLift 7824634
  have htrace : WordTrace (prefixWord ++ tailWord_7824634) baseStart_7824634 baseEnd_7824634 := by
    simpa [prefixWord, tailWord_7824634, baseEnd_7824634] using wordTrace_append hprefix tailTrace_7824634
  have hstable : (prefixWord ++ tailWord_7824634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824634).length < 2 ^ (prefixWord ++ tailWord_7824634).sum := by decide
  have hdescent : baseEnd_7824634 < baseStart_7824634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824648 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_7824648 : Nat := 118140960795 + 7824648 * 2 ^ 59
def prefixEnd_7824648 : Nat := 4983230072969 + 3 ^ 40 * 7824648 * 2
def baseEnd_7824648 : Nat := 1339268458747202420805035

theorem tailTrace_7824648 : CollatzResearch.WordTrace tailWord_7824648 prefixEnd_7824648 1339268458747202420805035 := by
  unfold tailWord_7824648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142694179078322057165885299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190258905437762742887847065 142694179078322057165885299)
  ·
    refine ⟨214041268617483085748827949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142694179078322057165885299 214041268617483085748827949)
    ·
      refine ⟨80265475731556157155810481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214041268617483085748827949 80265475731556157155810481)
      ·
        refine ⟨60199106798667117866857861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80265475731556157155810481 60199106798667117866857861)
        ·
          refine ⟨11287332524750084600035849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60199106798667117866857861 11287332524750084600035849)
          ·
            refine ⟨8465499393562563450026887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11287332524750084600035849 8465499393562563450026887)
            ·
              refine ⟨12698249090343845175040331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465499393562563450026887 12698249090343845175040331)
              ·
                refine ⟨19047373635515767762560497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698249090343845175040331 19047373635515767762560497)
                ·
                  refine ⟨14285530226636825821920373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19047373635515767762560497 14285530226636825821920373)
                  ·
                    refine ⟨1339268458747202420805035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14285530226636825821920373 1339268458747202420805035)
                    ·
                      rfl

theorem cell23_7824648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_7824648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824648 prefixEnd_7824648 := by exact prefixLift 7824648
  have htrace : WordTrace (prefixWord ++ tailWord_7824648) baseStart_7824648 baseEnd_7824648 := by
    simpa [prefixWord, tailWord_7824648, baseEnd_7824648] using wordTrace_append hprefix tailTrace_7824648
  have hstable : (prefixWord ++ tailWord_7824648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824648).length < 2 ^ (prefixWord ++ tailWord_7824648).sum := by decide
  have hdescent : baseEnd_7824648 < baseStart_7824648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7824651 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4]
def baseStart_7824651 : Nat := 118140960795 + 7824651 * 2 ^ 59
def prefixEnd_7824651 : Nat := 4983230072969 + 3 ^ 40 * 7824651 * 2
def baseEnd_7824651 : Nat := 4017806916683570750677591

theorem tailTrace_7824651 : CollatzResearch.WordTrace tailWord_7824651 prefixEnd_7824651 4017806916683570750677591 := by
  unfold tailWord_7824651
  simp only [CollatzResearch.WordTrace]
  refine ⟨285388467575633245844129807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190258978383755497229419871 285388467575633245844129807)
  ·
    refine ⟨428082701363449868766194711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285388467575633245844129807 428082701363449868766194711)
    ·
      refine ⟨642124052045174803149292067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428082701363449868766194711 642124052045174803149292067)
      ·
        refine ⟨963186078067762204723938101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642124052045174803149292067 963186078067762204723938101)
        ·
          refine ⟨90298694818852706692869197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 963186078067762204723938101 90298694818852706692869197)
          ·
            refine ⟨33862010557069765009825949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90298694818852706692869197 33862010557069765009825949)
            ·
              refine ⟨12698253958901161878684731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33862010557069765009825949 12698253958901161878684731)
              ·
                refine ⟨19047380938351742818027097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698253958901161878684731 19047380938351742818027097)
                ·
                  refine ⟨14285535703763807113520323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19047380938351742818027097 14285535703763807113520323)
                  ·
                    refine ⟨21428303555645710670280485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14285535703763807113520323 21428303555645710670280485)
                    ·
                      refine ⟨4017806916683570750677591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21428303555645710670280485 4017806916683570750677591)
                      ·
                        rfl

theorem cell23_7824651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].length) (baseStart_7824651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7824651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7824651 prefixEnd_7824651 := by exact prefixLift 7824651
  have htrace : WordTrace (prefixWord ++ tailWord_7824651) baseStart_7824651 baseEnd_7824651 := by
    simpa [prefixWord, tailWord_7824651, baseEnd_7824651] using wordTrace_append hprefix tailTrace_7824651
  have hstable : (prefixWord ++ tailWord_7824651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7824651).length < 2 ^ (prefixWord ++ tailWord_7824651).sum := by decide
  have hdescent : baseEnd_7824651 < baseStart_7824651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7824651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
