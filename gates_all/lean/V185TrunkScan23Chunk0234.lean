import V185TrunkScan23Chunk0233

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1384727 : List Nat := [1, 1, 3, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_1384727 : Nat := 118140960795 + 1384727 * 2 ^ 59
def prefixEnd_1384727 : Nat := 4983230072969 + 3 ^ 40 * 1384727 * 2
def baseEnd_1384727 : Nat := 711030526258508982944263

theorem tailTrace_1384727 : CollatzResearch.WordTrace tailWord_1384727 prefixEnd_1384727 711030526258508982944263 := by
  unfold tailWord_1384727
  simp only [CollatzResearch.WordTrace]
  refine ⟨50505142854378046388576435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33670095236252030925717623 50505142854378046388576435)
  ·
    refine ⟨75757714281567069582864653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50505142854378046388576435 75757714281567069582864653)
    ·
      refine ⟨28409142855587651093574245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75757714281567069582864653 28409142855587651093574245)
      ·
        refine ⟨5326714285422684580045171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28409142855587651093574245 5326714285422684580045171)
        ·
          refine ⟨7990071428134026870067757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326714285422684580045171 7990071428134026870067757)
          ·
            refine ⟨2996276785550260076275409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7990071428134026870067757 2996276785550260076275409)
            ·
              refine ⟨2247207589162695057206557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996276785550260076275409 2247207589162695057206557)
              ·
                refine ⟨842702845936010646452459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2247207589162695057206557 842702845936010646452459)
                ·
                  refine ⟨1264054268904015969678689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842702845936010646452459 1264054268904015969678689)
                  ·
                    refine ⟨948040701678011977259017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264054268904015969678689 948040701678011977259017)
                    ·
                      refine ⟨711030526258508982944263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948040701678011977259017 711030526258508982944263)
                      ·
                        rfl

theorem cell23_1384727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_1384727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384727 prefixEnd_1384727 := by exact prefixLift 1384727
  have htrace : WordTrace (prefixWord ++ tailWord_1384727) baseStart_1384727 baseEnd_1384727 := by
    simpa [prefixWord, tailWord_1384727, baseEnd_1384727] using wordTrace_append hprefix tailTrace_1384727
  have hstable : (prefixWord ++ tailWord_1384727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384727).length < 2 ^ (prefixWord ++ tailWord_1384727).sum := by decide
  have hdescent : baseEnd_1384727 < baseStart_1384727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384779 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_1384779 : Nat := 118140960795 + 1384779 * 2 ^ 59
def prefixEnd_1384779 : Nat := 4983230072969 + 3 ^ 40 * 1384779 * 2
def baseEnd_1384779 : Nat := 711057227252542779494023

theorem tailTrace_1384779 : CollatzResearch.WordTrace tailWord_1384779 prefixEnd_1384779 711057227252542779494023 := by
  unfold tailWord_1384779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50507039450189659269469391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33671359633459772846312927 50507039450189659269469391)
  ·
    refine ⟨75760559175284488904204087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50507039450189659269469391 75760559175284488904204087)
    ·
      refine ⟨113640838762926733356306131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75760559175284488904204087 113640838762926733356306131)
      ·
        refine ⟨170461258144390100034459197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113640838762926733356306131 170461258144390100034459197)
        ·
          refine ⟨63922971804146287512922199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170461258144390100034459197 63922971804146287512922199)
          ·
            refine ⟨95884457706219431269383299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63922971804146287512922199 95884457706219431269383299)
            ·
              refine ⟨143826686559329146904074949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95884457706219431269383299 143826686559329146904074949)
              ·
                refine ⟨26967503729874215044514053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143826686559329146904074949 26967503729874215044514053)
                ·
                  refine ⟨5056406949351415320846385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26967503729874215044514053 5056406949351415320846385)
                  ·
                    refine ⟨3792305212013561490634789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056406949351415320846385 3792305212013561490634789)
                    ·
                      refine ⟨711057227252542779494023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3792305212013561490634789 711057227252542779494023)
                      ·
                        rfl

theorem cell23_1384779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_1384779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384779 prefixEnd_1384779 := by exact prefixLift 1384779
  have htrace : WordTrace (prefixWord ++ tailWord_1384779) baseStart_1384779 baseEnd_1384779 := by
    simpa [prefixWord, tailWord_1384779, baseEnd_1384779] using wordTrace_append hprefix tailTrace_1384779
  have hstable : (prefixWord ++ tailWord_1384779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384779).length < 2 ^ (prefixWord ++ tailWord_1384779).sum := by decide
  have hdescent : baseEnd_1384779 < baseStart_1384779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384876 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_1384876 : Nat := 118140960795 + 1384876 * 2 ^ 59
def prefixEnd_1384876 : Nat := 4983230072969 + 3 ^ 40 * 1384876 * 2
def baseEnd_1384876 : Nat := 711107034876028899981077

theorem tailTrace_1384876 : CollatzResearch.WordTrace tailWord_1384876 prefixEnd_1384876 711107034876028899981077 := by
  unfold tailWord_1384876
  simp only [CollatzResearch.WordTrace]
  refine ⟨25255288665419122417875241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33673718220558829890500321 25255288665419122417875241)
  ·
    refine ⟨18941466499064341813406431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25255288665419122417875241 18941466499064341813406431)
    ·
      refine ⟨28412199748596512720109647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18941466499064341813406431 28412199748596512720109647)
      ·
        refine ⟨42618299622894769080164471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28412199748596512720109647 42618299622894769080164471)
        ·
          refine ⟨63927449434342153620246707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42618299622894769080164471 63927449434342153620246707)
          ·
            refine ⟨95891174151513230430370061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63927449434342153620246707 95891174151513230430370061)
            ·
              refine ⟨35959190306817461411388773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95891174151513230430370061 35959190306817461411388773)
              ·
                refine ⟨6742348182528274014635395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35959190306817461411388773 6742348182528274014635395)
                ·
                  refine ⟨10113522273792411021953093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742348182528274014635395 10113522273792411021953093)
                  ·
                    refine ⟨1896285426336077066616205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10113522273792411021953093 1896285426336077066616205)
                    ·
                      refine ⟨711107034876028899981077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1896285426336077066616205 711107034876028899981077)
                      ·
                        rfl

theorem cell23_1384876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_1384876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384876 prefixEnd_1384876 := by exact prefixLift 1384876
  have htrace : WordTrace (prefixWord ++ tailWord_1384876) baseStart_1384876 baseEnd_1384876 := by
    simpa [prefixWord, tailWord_1384876, baseEnd_1384876] using wordTrace_append hprefix tailTrace_1384876
  have hstable : (prefixWord ++ tailWord_1384876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384876).length < 2 ^ (prefixWord ++ tailWord_1384876).sum := by decide
  have hdescent : baseEnd_1384876 < baseStart_1384876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384879 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 12]
def baseStart_1384879 : Nat := 118140960795 + 1384879 * 2 ^ 59
def prefixEnd_1384879 : Nat := 4983230072969 + 3 ^ 40 * 1384879 * 2
def baseEnd_1384879 : Nat := 79012063924221376471507

theorem tailTrace_1384879 : CollatzResearch.WordTrace tailWord_1384879 prefixEnd_1384879 79012063924221376471507 := by
  unfold tailWord_1384879
  simp only [CollatzResearch.WordTrace]
  refine ⟨50510686749827376348109691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33673791166551584232073127 50510686749827376348109691)
  ·
    refine ⟨75766030124741064522164537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50510686749827376348109691 75766030124741064522164537)
    ·
      refine ⟨56824522593555798391623403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75766030124741064522164537 56824522593555798391623403)
      ·
        refine ⟨85236783890333697587435105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56824522593555798391623403 85236783890333697587435105)
        ·
          refine ⟨63927587917750273190576329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85236783890333697587435105 63927587917750273190576329)
          ·
            refine ⟨47945690938312704892932247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63927587917750273190576329 47945690938312704892932247)
            ·
              refine ⟨71918536407469057339398371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47945690938312704892932247 71918536407469057339398371)
              ·
                refine ⟨107877804611203586009097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71918536407469057339398371 107877804611203586009097557)
                ·
                  refine ⟨79012063924221376471507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 107877804611203586009097557 79012063924221376471507)
                  ·
                    rfl

theorem cell23_1384879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 12].length) (baseStart_1384879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384879 prefixEnd_1384879 := by exact prefixLift 1384879
  have htrace : WordTrace (prefixWord ++ tailWord_1384879) baseStart_1384879 baseEnd_1384879 := by
    simpa [prefixWord, tailWord_1384879, baseEnd_1384879] using wordTrace_append hprefix tailTrace_1384879
  have hstable : (prefixWord ++ tailWord_1384879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384879).length < 2 ^ (prefixWord ++ tailWord_1384879).sum := by decide
  have hdescent : baseEnd_1384879 < baseStart_1384879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384893 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1384893 : Nat := 118140960795 + 1384893 * 2 ^ 59
def prefixEnd_1384893 : Nat := 4983230072969 + 3 ^ 40 * 1384893 * 2
def baseEnd_1384893 : Nat := 711115764047155333468499

theorem tailTrace_1384893 : CollatzResearch.WordTrace tailWord_1384893 prefixEnd_1384893 711115764047155333468499 := by
  unfold tailWord_1384893
  simp only [CollatzResearch.WordTrace]
  refine ⟨50511197371776656739119333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33674131581184437826079555 50511197371776656739119333)
  ·
    refine ⟨9470849507208123138584875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50511197371776656739119333 9470849507208123138584875)
    ·
      refine ⟨14206274260812184707877313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9470849507208123138584875 14206274260812184707877313)
      ·
        refine ⟨10654705695609138530907985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14206274260812184707877313 10654705695609138530907985)
        ·
          refine ⟨7991029271706853898180989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10654705695609138530907985 7991029271706853898180989)
          ·
            refine ⟨2996635976890070211817871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7991029271706853898180989 2996635976890070211817871)
            ·
              refine ⟨4494953965335105317726807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996635976890070211817871 4494953965335105317726807)
              ·
                refine ⟨6742430948002657976590211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4494953965335105317726807 6742430948002657976590211)
                ·
                  refine ⟨10113646422003986964885317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742430948002657976590211 10113646422003986964885317)
                  ·
                    refine ⟨1896308704125747555915997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10113646422003986964885317 1896308704125747555915997)
                    ·
                      refine ⟨711115764047155333468499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1896308704125747555915997 711115764047155333468499)
                      ·
                        rfl

theorem cell23_1384893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1384893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384893 prefixEnd_1384893 := by exact prefixLift 1384893
  have htrace : WordTrace (prefixWord ++ tailWord_1384893) baseStart_1384893 baseEnd_1384893 := by
    simpa [prefixWord, tailWord_1384893, baseEnd_1384893] using wordTrace_append hprefix tailTrace_1384893
  have hstable : (prefixWord ++ tailWord_1384893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384893).length < 2 ^ (prefixWord ++ tailWord_1384893).sum := by decide
  have hdescent : baseEnd_1384893 < baseStart_1384893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384950 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1384950 : Nat := 118140960795 + 1384950 * 2 ^ 59
def prefixEnd_1384950 : Nat := 4983230072969 + 3 ^ 40 * 1384950 * 2
def baseEnd_1384950 : Nat := 711145032444461610455737

theorem tailTrace_1384950 : CollatzResearch.WordTrace tailWord_1384950 prefixEnd_1384950 711145032444461610455737 := by
  unfold tailWord_1384950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157079770785634717121519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33675517555046770315962869 3157079770785634717121519)
  ·
    refine ⟨4735619656178452075682279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157079770785634717121519 4735619656178452075682279)
    ·
      refine ⟨7103429484267678113523419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4735619656178452075682279 7103429484267678113523419)
      ·
        refine ⟨10655144226401517170285129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7103429484267678113523419 10655144226401517170285129)
        ·
          refine ⟨7991358169801137877713847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655144226401517170285129 7991358169801137877713847)
          ·
            refine ⟨11987037254701706816570771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991358169801137877713847 11987037254701706816570771)
            ·
              refine ⟨17980555882052560224856157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11987037254701706816570771 17980555882052560224856157)
              ·
                refine ⟨6742708455769710084321059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17980555882052560224856157 6742708455769710084321059)
                ·
                  refine ⟨10114062683654565126481589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742708455769710084321059 10114062683654565126481589)
                  ·
                    refine ⟨948193376592615480607649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10114062683654565126481589 948193376592615480607649)
                    ·
                      refine ⟨711145032444461610455737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948193376592615480607649 711145032444461610455737)
                      ·
                        rfl

theorem cell23_1384950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1384950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384950 prefixEnd_1384950 := by exact prefixLift 1384950
  have htrace : WordTrace (prefixWord ++ tailWord_1384950) baseStart_1384950 baseEnd_1384950 := by
    simpa [prefixWord, tailWord_1384950, baseEnd_1384950] using wordTrace_append hprefix tailTrace_1384950
  have hstable : (prefixWord ++ tailWord_1384950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384950).length < 2 ^ (prefixWord ++ tailWord_1384950).sum := by decide
  have hdescent : baseEnd_1384950 < baseStart_1384950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384956 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_1384956 : Nat := 118140960795 + 1384956 * 2 ^ 59
def prefixEnd_1384956 : Nat := 4983230072969 + 3 ^ 40 * 1384956 * 2
def baseEnd_1384956 : Nat := 237049371109462862326903

theorem tailTrace_1384956 : CollatzResearch.WordTrace tailWord_1384956 prefixEnd_1384956 237049371109462862326903 := by
  unfold tailWord_1384956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25256747585274209249331361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33675663447032278999108481 25256747585274209249331361)
  ·
    refine ⟨18942560688955656936998521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25256747585274209249331361 18942560688955656936998521)
    ·
      refine ⟨14206920516716742702748891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18942560688955656936998521 14206920516716742702748891)
      ·
        refine ⟨21310380775075114054123337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14206920516716742702748891 21310380775075114054123337)
        ·
          refine ⟨15982785581306335540592503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21310380775075114054123337 15982785581306335540592503)
          ·
            refine ⟨23974178371959503310888755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15982785581306335540592503 23974178371959503310888755)
            ·
              refine ⟨35961267557939254966333133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23974178371959503310888755 35961267557939254966333133)
              ·
                refine ⟨13485475334227220612374925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35961267557939254966333133 13485475334227220612374925)
                ·
                  refine ⟨5057053250335207729640597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13485475334227220612374925 5057053250335207729640597)
                  ·
                    refine ⟨237049371109462862326903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5057053250335207729640597 237049371109462862326903)
                    ·
                      rfl

theorem cell23_1384956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_1384956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384956 prefixEnd_1384956 := by exact prefixLift 1384956
  have htrace : WordTrace (prefixWord ++ tailWord_1384956) baseStart_1384956 baseEnd_1384956 := by
    simpa [prefixWord, tailWord_1384956, baseEnd_1384956] using wordTrace_append hprefix tailTrace_1384956
  have hstable : (prefixWord ++ tailWord_1384956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384956).length < 2 ^ (prefixWord ++ tailWord_1384956).sum := by decide
  have hdescent : baseEnd_1384956 < baseStart_1384956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384963 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 4]
def baseStart_1384963 : Nat := 118140960795 + 1384963 * 2 ^ 59
def prefixEnd_1384963 : Nat := 4983230072969 + 3 ^ 40 * 1384963 * 2
def baseEnd_1384963 : Nat := 711151707692970059593177

theorem tailTrace_1384963 : CollatzResearch.WordTrace tailWord_1384963 prefixEnd_1384963 711151707692970059593177 := by
  unfold tailWord_1384963
  simp only [CollatzResearch.WordTrace]
  refine ⟨50513750481523058694167543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33675833654348705796111695 50513750481523058694167543)
  ·
    refine ⟨75770625722284588041251315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50513750481523058694167543 75770625722284588041251315)
    ·
      refine ⟨113655938583426882061876973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75770625722284588041251315 113655938583426882061876973)
      ·
        refine ⟨42620976968785080773203865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113655938583426882061876973 42620976968785080773203865)
        ·
          refine ⟨31965732726588810579902899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42620976968785080773203865 31965732726588810579902899)
          ·
            refine ⟨47948599089883215869854349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31965732726588810579902899 47948599089883215869854349)
            ·
              refine ⟨17980724658706205951195381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47948599089883215869854349 17980724658706205951195381)
              ·
                refine ⟨1685692936753706807924567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17980724658706205951195381 1685692936753706807924567)
                ·
                  refine ⟨2528539405130560211886851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685692936753706807924567 2528539405130560211886851)
                  ·
                    refine ⟨3792809107695840317830277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528539405130560211886851 3792809107695840317830277)
                    ·
                      refine ⟨711151707692970059593177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3792809107695840317830277 711151707692970059593177)
                      ·
                        rfl

theorem cell23_1384963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_1384963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384963 prefixEnd_1384963 := by exact prefixLift 1384963
  have htrace : WordTrace (prefixWord ++ tailWord_1384963) baseStart_1384963 baseEnd_1384963 := by
    simpa [prefixWord, tailWord_1384963, baseEnd_1384963] using wordTrace_append hprefix tailTrace_1384963
  have hstable : (prefixWord ++ tailWord_1384963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384963).length < 2 ^ (prefixWord ++ tailWord_1384963).sum := by decide
  have hdescent : baseEnd_1384963 < baseStart_1384963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384967 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1384967 : Nat := 118140960795 + 1384967 * 2 ^ 59
def prefixEnd_1384967 : Nat := 4983230072969 + 3 ^ 40 * 1384967 * 2
def baseEnd_1384967 : Nat := 711153761615588043943159

theorem tailTrace_1384967 : CollatzResearch.WordTrace tailWord_1384967 prefixEnd_1384967 711153761615588043943159 := by
  unfold tailWord_1384967
  simp only [CollatzResearch.WordTrace]
  refine ⟨50513896373508567377313155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33675930915672378251542103 50513896373508567377313155)
  ·
    refine ⟨75770844560262851065969733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50513896373508567377313155 75770844560262851065969733)
    ·
      refine ⟨14207033355049284574869325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75770844560262851065969733 14207033355049284574869325)
      ·
        refine ⟨5327637508143481715575997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14207033355049284574869325 5327637508143481715575997)
        ·
          refine ⟨1997864065553805643340999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5327637508143481715575997 1997864065553805643340999)
          ·
            refine ⟨2996796098330708465011499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997864065553805643340999 2996796098330708465011499)
            ·
              refine ⟨4495194147496062697517249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996796098330708465011499 4495194147496062697517249)
              ·
                refine ⟨3371395610622047023137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495194147496062697517249 3371395610622047023137937)
                ·
                  refine ⟨2528546707966535267353453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371395610622047023137937 2528546707966535267353453)
                  ·
                    refine ⟨948205015487450725257545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528546707966535267353453 948205015487450725257545)
                    ·
                      refine ⟨711153761615588043943159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948205015487450725257545 711153761615588043943159)
                      ·
                        rfl

theorem cell23_1384967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1384967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384967 prefixEnd_1384967 := by exact prefixLift 1384967
  have htrace : WordTrace (prefixWord ++ tailWord_1384967) baseStart_1384967 baseEnd_1384967 := by
    simpa [prefixWord, tailWord_1384967, baseEnd_1384967] using wordTrace_append hprefix tailTrace_1384967
  have hstable : (prefixWord ++ tailWord_1384967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384967).length < 2 ^ (prefixWord ++ tailWord_1384967).sum := by decide
  have hdescent : baseEnd_1384967 < baseStart_1384967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384986 : List Nat := [3, 1, 1, 3, 1, 1, 3, 10]
def baseStart_1384986 : Nat := 118140960795 + 1384986 * 2 ^ 59
def prefixEnd_1384986 : Nat := 4983230072969 + 3 ^ 40 * 1384986 * 2
def baseEnd_1384986 : Nat := 26339389546223091466873

theorem tailTrace_1384986 : CollatzResearch.WordTrace tailWord_1384986 prefixEnd_1384986 26339389546223091466873 := by
  unfold tailWord_1384986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628647340109933405563703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33676392906959822414836541 12628647340109933405563703)
  ·
    refine ⟨18942971010164900108345555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12628647340109933405563703 18942971010164900108345555)
    ·
      refine ⟨28414456515247350162518333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18942971010164900108345555 28414456515247350162518333)
      ·
        refine ⟨10655421193217756310944375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28414456515247350162518333 10655421193217756310944375)
        ·
          refine ⟨15983131789826634466416563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10655421193217756310944375 15983131789826634466416563)
          ·
            refine ⟨23974697684739951699624845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983131789826634466416563 23974697684739951699624845)
            ·
              refine ⟨8990511631777481887359317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23974697684739951699624845 8990511631777481887359317)
              ·
                refine ⟨26339389546223091466873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8990511631777481887359317 26339389546223091466873)
                ·
                  rfl

theorem cell23_1384986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_1384986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384986 prefixEnd_1384986 := by exact prefixLift 1384986
  have htrace : WordTrace (prefixWord ++ tailWord_1384986) baseStart_1384986 baseEnd_1384986 := by
    simpa [prefixWord, tailWord_1384986, baseEnd_1384986] using wordTrace_append hprefix tailTrace_1384986
  have hstable : (prefixWord ++ tailWord_1384986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384986).length < 2 ^ (prefixWord ++ tailWord_1384986).sum := by decide
  have hdescent : baseEnd_1384986 < baseStart_1384986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1384993 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1384993 : Nat := 118140960795 + 1384993 * 2 ^ 59
def prefixEnd_1384993 : Nat := 4983230072969 + 3 ^ 40 * 1384993 * 2
def baseEnd_1384993 : Nat := 711167112112604942218039

theorem tailTrace_1384993 : CollatzResearch.WordTrace tailWord_1384993 prefixEnd_1384993 711167112112604942218039 := by
  unfold tailWord_1384993
  simp only [CollatzResearch.WordTrace]
  refine ⟨50514844671414373817759633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33676563114276249211839755 50514844671414373817759633)
  ·
    refine ⟨37886133503560780363319725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50514844671414373817759633 37886133503560780363319725)
    ·
      refine ⟨14207300063835292636244897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37886133503560780363319725 14207300063835292636244897)
      ·
        refine ⟨10655475047876469477183673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14207300063835292636244897 10655475047876469477183673)
        ·
          refine ⟨7991606285907352107887755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655475047876469477183673 7991606285907352107887755)
          ·
            refine ⟨11987409428861028161831633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991606285907352107887755 11987409428861028161831633)
            ·
              refine ⟨8990557071645771121373725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11987409428861028161831633 8990557071645771121373725)
              ·
                refine ⟨3371458901867164170515147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8990557071645771121373725 3371458901867164170515147)
                ·
                  refine ⟨5057188352800746255772721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371458901867164170515147 5057188352800746255772721)
                  ·
                    refine ⟨3792891264600559691829541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5057188352800746255772721 3792891264600559691829541)
                    ·
                      refine ⟨711167112112604942218039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3792891264600559691829541 711167112112604942218039)
                      ·
                        rfl

theorem cell23_1384993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1384993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1384993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1384993 prefixEnd_1384993 := by exact prefixLift 1384993
  have htrace : WordTrace (prefixWord ++ tailWord_1384993) baseStart_1384993 baseEnd_1384993 := by
    simpa [prefixWord, tailWord_1384993, baseEnd_1384993] using wordTrace_append hprefix tailTrace_1384993
  have hstable : (prefixWord ++ tailWord_1384993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1384993).length < 2 ^ (prefixWord ++ tailWord_1384993).sum := by decide
  have hdescent : baseEnd_1384993 < baseStart_1384993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1384993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385014 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1385014 : Nat := 118140960795 + 1385014 * 2 ^ 59
def prefixEnd_1385014 : Nat := 4983230072969 + 3 ^ 40 * 1385014 * 2
def baseEnd_1385014 : Nat := 711177895206349360055443

theorem tailTrace_1385014 : CollatzResearch.WordTrace tailWord_1385014 prefixEnd_1385014 711177895206349360055443 := by
  unfold tailWord_1385014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157225662771143400267131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33677073736225529602849397 3157225662771143400267131)
  ·
    refine ⟨4735838494156715100400697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157225662771143400267131 4735838494156715100400697)
    ·
      refine ⟨3551878870617536325300523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735838494156715100400697 3551878870617536325300523)
      ·
        refine ⟨5327818305926304487950785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551878870617536325300523 5327818305926304487950785)
        ·
          refine ⟨3995863729444728365963089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5327818305926304487950785 3995863729444728365963089)
          ·
            refine ⟨2996897797083546274472317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995863729444728365963089 2996897797083546274472317)
            ·
              refine ⟨1123836673906329852927119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2996897797083546274472317 1123836673906329852927119)
              ·
                refine ⟨1685755010859494779390679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123836673906329852927119 1685755010859494779390679)
                ·
                  refine ⟨2528632516289242169086019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685755010859494779390679 2528632516289242169086019)
                  ·
                    refine ⟨3792948774433863253629029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528632516289242169086019 3792948774433863253629029)
                    ·
                      refine ⟨711177895206349360055443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3792948774433863253629029 711177895206349360055443)
                      ·
                        rfl

theorem cell23_1385014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1385014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385014 prefixEnd_1385014 := by exact prefixLift 1385014
  have htrace : WordTrace (prefixWord ++ tailWord_1385014) baseStart_1385014 baseEnd_1385014 := by
    simpa [prefixWord, tailWord_1385014, baseEnd_1385014] using wordTrace_append hprefix tailTrace_1385014
  have hstable : (prefixWord ++ tailWord_1385014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385014).length < 2 ^ (prefixWord ++ tailWord_1385014).sum := by decide
  have hdescent : baseEnd_1385014 < baseStart_1385014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385017 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1385017 : Nat := 118140960795 + 1385017 * 2 ^ 59
def prefixEnd_1385017 : Nat := 4983230072969 + 3 ^ 40 * 1385017 * 2
def baseEnd_1385017 : Nat := 711179435648312848317929

theorem tailTrace_1385017 : CollatzResearch.WordTrace tailWord_1385017 prefixEnd_1385017 711179435648312848317929 := by
  unfold tailWord_1385017
  simp only [CollatzResearch.WordTrace]
  refine ⟨50515720023327425916633305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33677146682218283944422203 50515720023327425916633305)
  ·
    refine ⟨37886790017495569437474979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50515720023327425916633305 37886790017495569437474979)
    ·
      refine ⟨56830185026243354156212469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37886790017495569437474979 56830185026243354156212469)
      ·
        refine ⟨5327829846210314452144919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56830185026243354156212469 5327829846210314452144919)
        ·
          refine ⟨7991744769315471678217379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327829846210314452144919 7991744769315471678217379)
          ·
            refine ⟨11987617153973207517326069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991744769315471678217379 11987617153973207517326069)
            ·
              refine ⟨1123839108184988204749319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11987617153973207517326069 1123839108184988204749319)
              ·
                refine ⟨1685758662277482307123979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123839108184988204749319 1685758662277482307123979)
                ·
                  refine ⟨2528637993416223460685969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685758662277482307123979 2528637993416223460685969)
                  ·
                    refine ⟨1896478495062167595514477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528637993416223460685969 1896478495062167595514477)
                    ·
                      refine ⟨711179435648312848317929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1896478495062167595514477 711179435648312848317929)
                      ·
                        rfl

theorem cell23_1385017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1385017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385017 prefixEnd_1385017 := by exact prefixLift 1385017
  have htrace : WordTrace (prefixWord ++ tailWord_1385017) baseStart_1385017 baseEnd_1385017 := by
    simpa [prefixWord, tailWord_1385017, baseEnd_1385017] using wordTrace_append hprefix tailTrace_1385017
  have hstable : (prefixWord ++ tailWord_1385017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385017).length < 2 ^ (prefixWord ++ tailWord_1385017).sum := by decide
  have hdescent : baseEnd_1385017 < baseStart_1385017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385031 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_1385031 : Nat := 118140960795 + 1385031 * 2 ^ 59
def prefixEnd_1385031 : Nat := 4983230072969 + 3 ^ 40 * 1385031 * 2
def baseEnd_1385031 : Nat := 711186624377475793542865

theorem tailTrace_1385031 : CollatzResearch.WordTrace tailWord_1385031 prefixEnd_1385031 711186624377475793542865 := by
  unfold tailWord_1385031
  simp only [CollatzResearch.WordTrace]
  refine ⟨50516230645276706307642947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33677487096851137538428631 50516230645276706307642947)
  ·
    refine ⟨75774345967915059461464421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50516230645276706307642947 75774345967915059461464421)
    ·
      refine ⟨14207689868984073649024579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75774345967915059461464421 14207689868984073649024579)
      ·
        refine ⟨21311534803476110473536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14207689868984073649024579 21311534803476110473536869)
        ·
          refine ⟨3995912775651770713788163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21311534803476110473536869 3995912775651770713788163)
          ·
            refine ⟨5993869163477656070682245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995912775651770713788163 5993869163477656070682245)
            ·
              refine ⟨1123850468152060513252921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5993869163477656070682245 1123850468152060513252921)
              ·
                refine ⟨842887851114045384939691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123850468152060513252921 842887851114045384939691)
                ·
                  refine ⟨1264331776671068077409537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842887851114045384939691 1264331776671068077409537)
                  ·
                    refine ⟨948248832503301058057153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264331776671068077409537 948248832503301058057153)
                    ·
                      refine ⟨711186624377475793542865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948248832503301058057153 711186624377475793542865)
                      ·
                        rfl

theorem cell23_1385031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_1385031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385031 prefixEnd_1385031 := by exact prefixLift 1385031
  have htrace : WordTrace (prefixWord ++ tailWord_1385031) baseStart_1385031 baseEnd_1385031 := by
    simpa [prefixWord, tailWord_1385031, baseEnd_1385031] using wordTrace_append hprefix tailTrace_1385031
  have hstable : (prefixWord ++ tailWord_1385031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385031).length < 2 ^ (prefixWord ++ tailWord_1385031).sum := by decide
  have hdescent : baseEnd_1385031 < baseStart_1385031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385074 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_1385074 : Nat := 118140960795 + 1385074 * 2 ^ 59
def prefixEnd_1385074 : Nat := 4983230072969 + 3 ^ 40 * 1385074 * 2
def baseEnd_1385074 : Nat := 711208704045619125305167

theorem tailTrace_1385074 : CollatzResearch.WordTrace tailWord_1385074 prefixEnd_1385074 711208704045619125305167 := by
  unfold tailWord_1385074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629449746030231162864569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33678532656080616434305517 12629449746030231162864569)
  ·
    refine ⟨9472087309522673372148427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12629449746030231162864569 9472087309522673372148427)
    ·
      refine ⟨14208130964284010058222641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9472087309522673372148427 14208130964284010058222641)
      ·
        refine ⟨10656098223213007543666981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14208130964284010058222641 10656098223213007543666981)
        ·
          refine ⟨1998018416852438914437559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10656098223213007543666981 1998018416852438914437559)
          ·
            refine ⟨2997027625278658371656339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998018416852438914437559 2997027625278658371656339)
            ·
              refine ⟨4495541437917987557484509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997027625278658371656339 4495541437917987557484509)
              ·
                refine ⟨1685828039219245334056691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4495541437917987557484509 1685828039219245334056691)
                ·
                  refine ⟨2528742058828868001085037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685828039219245334056691 2528742058828868001085037)
                  ·
                    refine ⟨948278272060825500406889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528742058828868001085037 948278272060825500406889)
                    ·
                      refine ⟨711208704045619125305167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948278272060825500406889 711208704045619125305167)
                      ·
                        rfl

theorem cell23_1385074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_1385074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385074 prefixEnd_1385074 := by exact prefixLift 1385074
  have htrace : WordTrace (prefixWord ++ tailWord_1385074) baseStart_1385074 baseEnd_1385074 := by
    simpa [prefixWord, tailWord_1385074, baseEnd_1385074] using wordTrace_append hprefix tailTrace_1385074
  have hstable : (prefixWord ++ tailWord_1385074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385074).length < 2 ^ (prefixWord ++ tailWord_1385074).sum := by decide
  have hdescent : baseEnd_1385074 < baseStart_1385074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385087 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 2, 2, 2]
def baseStart_1385087 : Nat := 118140960795 + 1385087 * 2 ^ 59
def prefixEnd_1385087 : Nat := 4983230072969 + 3 ^ 40 * 1385087 * 2
def baseEnd_1385087 : Nat := 711215379294127574442607

theorem tailTrace_1385087 : CollatzResearch.WordTrace tailWord_1385087 prefixEnd_1385087 711215379294127574442607 := by
  unfold tailWord_1385087
  simp only [CollatzResearch.WordTrace]
  refine ⟨50518273133073827871681515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33678848755382551914454343 50518273133073827871681515)
  ·
    refine ⟨75777409699610741807522273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50518273133073827871681515 75777409699610741807522273)
    ·
      refine ⟨56833057274708056355641705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75777409699610741807522273 56833057274708056355641705)
      ·
        refine ⟨42624792956031042266731279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56833057274708056355641705 42624792956031042266731279)
        ·
          refine ⟨63937189434046563400096919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42624792956031042266731279 63937189434046563400096919)
          ·
            refine ⟨95905784151069845100145379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63937189434046563400096919 95905784151069845100145379)
            ·
              refine ⟨143858676226604767650218069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95905784151069845100145379 143858676226604767650218069)
              ·
                refine ⟨1685843862030524620900993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 143858676226604767650218069 1685843862030524620900993)
                ·
                  refine ⟨1264382896522893465675745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1685843862030524620900993 1264382896522893465675745)
                  ·
                    refine ⟨948287172392170099256809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264382896522893465675745 948287172392170099256809)
                    ·
                      refine ⟨711215379294127574442607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948287172392170099256809 711215379294127574442607)
                      ·
                        rfl

theorem cell23_1385087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_1385087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385087 prefixEnd_1385087 := by exact prefixLift 1385087
  have htrace : WordTrace (prefixWord ++ tailWord_1385087) baseStart_1385087 baseEnd_1385087 := by
    simpa [prefixWord, tailWord_1385087, baseEnd_1385087] using wordTrace_append hprefix tailTrace_1385087
  have hstable : (prefixWord ++ tailWord_1385087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385087).length < 2 ^ (prefixWord ++ tailWord_1385087).sum := by decide
  have hdescent : baseEnd_1385087 < baseStart_1385087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385093 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 7]
def baseStart_1385093 : Nat := 118140960795 + 1385093 * 2 ^ 59
def prefixEnd_1385093 : Nat := 4983230072969 + 3 ^ 40 * 1385093 * 2
def baseEnd_1385093 : Nat := 79024273353117172329731

theorem tailTrace_1385093 : CollatzResearch.WordTrace tailWord_1385093 prefixEnd_1385093 79024273353117172329731 := by
  unfold tailWord_1385093
  simp only [CollatzResearch.WordTrace]
  refine ⟨50518491971052090896399933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33678994647368060597599955 50518491971052090896399933)
  ·
    refine ⟨18944434489144534086149975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50518491971052090896399933 18944434489144534086149975)
    ·
      refine ⟨28416651733716801129224963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18944434489144534086149975 28416651733716801129224963)
      ·
        refine ⟨42624977600575201693837445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28416651733716801129224963 42624977600575201693837445)
        ·
          refine ⟨7992183300107850317594521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42624977600575201693837445 7992183300107850317594521)
          ·
            refine ⟨5994137475080887738195891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992183300107850317594521 5994137475080887738195891)
            ·
              refine ⟨8991206212621331607293837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994137475080887738195891 8991206212621331607293837)
              ·
                refine ⟨3371702329732999352735189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8991206212621331607293837 3371702329732999352735189)
                ·
                  refine ⟨79024273353117172329731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3371702329732999352735189 79024273353117172329731)
                  ·
                    rfl

theorem cell23_1385093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_1385093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385093 prefixEnd_1385093 := by exact prefixLift 1385093
  have htrace : WordTrace (prefixWord ++ tailWord_1385093) baseStart_1385093 baseEnd_1385093 := by
    simpa [prefixWord, tailWord_1385093, baseEnd_1385093] using wordTrace_append hprefix tailTrace_1385093
  have hstable : (prefixWord ++ tailWord_1385093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385093).length < 2 ^ (prefixWord ++ tailWord_1385093).sum := by decide
  have hdescent : baseEnd_1385093 < baseStart_1385093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385150 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1385150 : Nat := 118140960795 + 1385150 * 2 ^ 59
def prefixEnd_1385150 : Nat := 4983230072969 + 3 ^ 40 * 1385150 * 2
def baseEnd_1385150 : Nat := 711247728575360827954817

theorem tailTrace_1385150 : CollatzResearch.WordTrace tailWord_1385150 prefixEnd_1385150 711247728575360827954817 := by
  unfold tailWord_1385150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6315071366480698703903113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33680380621230393087483269 6315071366480698703903113)
  ·
    refine ⟨4736303524860524027927335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6315071366480698703903113 4736303524860524027927335)
    ·
      refine ⟨7104455287290786041891003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736303524860524027927335 7104455287290786041891003)
      ·
        refine ⟨10656682930936179062836505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104455287290786041891003 10656682930936179062836505)
        ·
          refine ⟨7992512198202134297127379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10656682930936179062836505 7992512198202134297127379)
          ·
            refine ⟨11988768297303201445691069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7992512198202134297127379 11988768297303201445691069)
            ·
              refine ⟨4495788111488700542134151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11988768297303201445691069 4495788111488700542134151)
              ·
                refine ⟨6743682167233050813201227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495788111488700542134151 6743682167233050813201227)
                ·
                  refine ⟨10115523250849576219801841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6743682167233050813201227 10115523250849576219801841)
                  ·
                    refine ⟨7586642438137182164851381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10115523250849576219801841 7586642438137182164851381)
                    ·
                      refine ⟨711247728575360827954817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7586642438137182164851381 711247728575360827954817)
                      ·
                        rfl

theorem cell23_1385150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1385150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385150 prefixEnd_1385150 := by exact prefixLift 1385150
  have htrace : WordTrace (prefixWord ++ tailWord_1385150) baseStart_1385150 baseEnd_1385150 := by
    simpa [prefixWord, tailWord_1385150, baseEnd_1385150] using wordTrace_append hprefix tailTrace_1385150
  have hstable : (prefixWord ++ tailWord_1385150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385150).length < 2 ^ (prefixWord ++ tailWord_1385150).sum := by decide
  have hdescent : baseEnd_1385150 < baseStart_1385150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385197 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1385197 : Nat := 118140960795 + 1385197 * 2 ^ 59
def prefixEnd_1385197 : Nat := 4983230072969 + 3 ^ 40 * 1385197 * 2
def baseEnd_1385197 : Nat := 711271862166122144067101

theorem tailTrace_1385197 : CollatzResearch.WordTrace tailWord_1385197 prefixEnd_1385197 711271862166122144067101 := by
  unfold tailWord_1385197
  simp only [CollatzResearch.WordTrace]
  refine ⟨50522285162675316658185845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33681523441783544438790563 50522285162675316658185845)
  ·
    refine ⟨4736464234000810936704923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50522285162675316658185845 4736464234000810936704923)
    ·
      refine ⟨7104696351001216405057385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736464234000810936704923 7104696351001216405057385)
      ·
        refine ⟨5328522263250912303793039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7104696351001216405057385 5328522263250912303793039)
        ·
          refine ⟨7992783394876368455689559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328522263250912303793039 7992783394876368455689559)
          ·
            refine ⟨11989175092314552683534339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7992783394876368455689559 11989175092314552683534339)
            ·
              refine ⟨17983762638471829025301509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11989175092314552683534339 17983762638471829025301509)
              ·
                refine ⟨3371955494713467942244033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17983762638471829025301509 3371955494713467942244033)
                ·
                  refine ⟨2528966621035100956683025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371955494713467942244033 2528966621035100956683025)
                  ·
                    refine ⟨1896724965776325717512269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2528966621035100956683025 1896724965776325717512269)
                    ·
                      refine ⟨711271862166122144067101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1896724965776325717512269 711271862166122144067101)
                      ·
                        rfl

theorem cell23_1385197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1385197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385197 prefixEnd_1385197 := by exact prefixLift 1385197
  have htrace : WordTrace (prefixWord ++ tailWord_1385197) baseStart_1385197 baseEnd_1385197 := by
    simpa [prefixWord, tailWord_1385197, baseEnd_1385197] using wordTrace_append hprefix tailTrace_1385197
  have hstable : (prefixWord ++ tailWord_1385197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385197).length < 2 ^ (prefixWord ++ tailWord_1385197).sum := by decide
  have hdescent : baseEnd_1385197 < baseStart_1385197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385200 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 6]
def baseStart_1385200 : Nat := 118140960795 + 1385200 * 2 ^ 59
def prefixEnd_1385200 : Nat := 4983230072969 + 3 ^ 40 * 1385200 * 2
def baseEnd_1385200 : Nat := 79030378067565070258843

theorem tailTrace_1385200 : CollatzResearch.WordTrace tailWord_1385200 prefixEnd_1385200 79030378067565070258843 := by
  unfold tailWord_1385200
  simp only [CollatzResearch.WordTrace]
  refine ⟨25261197290832224085272527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33681596387776298780363369 25261197290832224085272527)
  ·
    refine ⟨37891795936248336127908791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25261197290832224085272527 37891795936248336127908791)
    ·
      refine ⟨56837693904372504191863187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37891795936248336127908791 56837693904372504191863187)
      ·
        refine ⟨85256540856558756287794781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56837693904372504191863187 85256540856558756287794781)
        ·
          refine ⟨31971202821209533607923043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85256540856558756287794781 31971202821209533607923043)
          ·
            refine ⟨47956804231814300411884565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31971202821209533607923043 47956804231814300411884565)
            ·
              refine ⟨2247975198366295331807089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47956804231814300411884565 2247975198366295331807089)
              ·
                refine ⟨1685981398774721498855317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247975198366295331807089 1685981398774721498855317)
                ·
                  refine ⟨79030378067565070258843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1685981398774721498855317 79030378067565070258843)
                  ·
                    rfl

theorem cell23_1385200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_1385200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385200 prefixEnd_1385200 := by exact prefixLift 1385200
  have htrace : WordTrace (prefixWord ++ tailWord_1385200) baseStart_1385200 baseEnd_1385200 := by
    simpa [prefixWord, tailWord_1385200, baseEnd_1385200] using wordTrace_append hprefix tailTrace_1385200
  have hstable : (prefixWord ++ tailWord_1385200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385200).length < 2 ^ (prefixWord ++ tailWord_1385200).sum := by decide
  have hdescent : baseEnd_1385200 < baseStart_1385200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385203 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_1385203 : Nat := 118140960795 + 1385203 * 2 ^ 59
def prefixEnd_1385203 : Nat := 4983230072969 + 3 ^ 40 * 1385203 * 2
def baseEnd_1385203 : Nat := 711274943050049120592073

theorem tailTrace_1385203 : CollatzResearch.WordTrace tailWord_1385203 prefixEnd_1385203 711274943050049120592073 := by
  unfold tailWord_1385203
  simp only [CollatzResearch.WordTrace]
  refine ⟨50522504000653579682904263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33681669333769053121936175 50522504000653579682904263)
  ·
    refine ⟨75783756000980369524356395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50522504000653579682904263 75783756000980369524356395)
    ·
      refine ⟨113675634001470554286534593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75783756000980369524356395 113675634001470554286534593)
      ·
        refine ⟨85256725501102915714900945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113675634001470554286534593 85256725501102915714900945)
        ·
          refine ⟨63942544125827186786175709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85256725501102915714900945 63942544125827186786175709)
          ·
            refine ⟨23978454047185195044815891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63942544125827186786175709 23978454047185195044815891)
            ·
              refine ⟨35967681070777792567223837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23978454047185195044815891 35967681070777792567223837)
              ·
                refine ⟨13487880401541672212708939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35967681070777792567223837 13487880401541672212708939)
                ·
                  refine ⟨20231820602312508319063409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13487880401541672212708939 20231820602312508319063409)
                  ·
                    refine ⟨15173865451734381239297557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20231820602312508319063409 15173865451734381239297557)
                    ·
                      refine ⟨711274943050049120592073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15173865451734381239297557 711274943050049120592073)
                      ·
                        rfl

theorem cell23_1385203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_1385203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385203 prefixEnd_1385203 := by exact prefixLift 1385203
  have htrace : WordTrace (prefixWord ++ tailWord_1385203) baseStart_1385203 baseEnd_1385203 := by
    simpa [prefixWord, tailWord_1385203, baseEnd_1385203] using wordTrace_append hprefix tailTrace_1385203
  have hstable : (prefixWord ++ tailWord_1385203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385203).length < 2 ^ (prefixWord ++ tailWord_1385203).sum := by decide
  have hdescent : baseEnd_1385203 < baseStart_1385203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385237 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_1385237 : Nat := 118140960795 + 1385237 * 2 ^ 59
def prefixEnd_1385237 : Nat := 4983230072969 + 3 ^ 40 * 1385237 * 2
def baseEnd_1385237 : Nat := 711292401392301987566917

theorem tailTrace_1385237 : CollatzResearch.WordTrace tailWord_1385237 prefixEnd_1385237 711292401392301987566917 := by
  unfold tailWord_1385237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50523744082530403489641965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33682496055020268993094643 50523744082530403489641965)
  ·
    refine ⟨18946404030948901308615737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50523744082530403489641965 18946404030948901308615737)
    ·
      refine ⟨14209803023211675981461803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18946404030948901308615737 14209803023211675981461803)
      ·
        refine ⟨21314704534817513972192705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14209803023211675981461803 21314704534817513972192705)
        ·
          refine ⟨15986028401113135479144529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21314704534817513972192705 15986028401113135479144529)
          ·
            refine ⟨11989521300834851609358397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15986028401113135479144529 11989521300834851609358397)
            ·
              refine ⟨4496070487813069353509399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11989521300834851609358397 4496070487813069353509399)
              ·
                refine ⟨6744105731719604030264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496070487813069353509399 6744105731719604030264099)
                ·
                  refine ⟨10116158597579406045396149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744105731719604030264099 10116158597579406045396149)
                  ·
                    refine ⟨948389868523069316755889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10116158597579406045396149 948389868523069316755889)
                    ·
                      refine ⟨711292401392301987566917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948389868523069316755889 711292401392301987566917)
                      ·
                        rfl

theorem cell23_1385237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_1385237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385237 prefixEnd_1385237 := by exact prefixLift 1385237
  have htrace : WordTrace (prefixWord ++ tailWord_1385237) baseStart_1385237 baseEnd_1385237 := by
    simpa [prefixWord, tailWord_1385237, baseEnd_1385237] using wordTrace_append hprefix tailTrace_1385237
  have hstable : (prefixWord ++ tailWord_1385237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385237).length < 2 ^ (prefixWord ++ tailWord_1385237).sum := by decide
  have hdescent : baseEnd_1385237 < baseStart_1385237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385247 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 1, 5]
def baseStart_1385247 : Nat := 118140960795 + 1385247 * 2 ^ 59
def prefixEnd_1385247 : Nat := 4983230072969 + 3 ^ 40 * 1385247 * 2
def baseEnd_1385247 : Nat := 237099178732948982813957

theorem tailTrace_1385247 : CollatzResearch.WordTrace tailWord_1385247 prefixEnd_1385247 237099178732948982813957 := by
  unfold tailWord_1385247
  simp only [CollatzResearch.WordTrace]
  refine ⟨50524108812494175197505995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33682739208329450131670663 50524108812494175197505995)
  ·
    refine ⟨75786163218741262796258993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50524108812494175197505995 75786163218741262796258993)
    ·
      refine ⟨56839622414055947097194245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75786163218741262796258993 56839622414055947097194245)
      ·
        refine ⟨10657429202635490080723921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56839622414055947097194245 10657429202635490080723921)
        ·
          refine ⟨7993071901976617560542941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10657429202635490080723921 7993071901976617560542941)
          ·
            refine ⟨2997401963241231585203603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7993071901976617560542941 2997401963241231585203603)
            ·
              refine ⟨4496102944861847377805405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997401963241231585203603 4496102944861847377805405)
              ·
                refine ⟨1686038604323192766677027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4496102944861847377805405 1686038604323192766677027)
                ·
                  refine ⟨2529057906484789150015541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686038604323192766677027 2529057906484789150015541)
                  ·
                    refine ⟨237099178732948982813957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2529057906484789150015541 237099178732948982813957)
                    ·
                      rfl

theorem cell23_1385247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_1385247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385247 prefixEnd_1385247 := by exact prefixLift 1385247
  have htrace : WordTrace (prefixWord ++ tailWord_1385247) baseStart_1385247 baseEnd_1385247 := by
    simpa [prefixWord, tailWord_1385247, baseEnd_1385247] using wordTrace_append hprefix tailTrace_1385247
  have hstable : (prefixWord ++ tailWord_1385247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385247).length < 2 ^ (prefixWord ++ tailWord_1385247).sum := by decide
  have hdescent : baseEnd_1385247 < baseStart_1385247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385281 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1385281 : Nat := 118140960795 + 1385281 * 2 ^ 59
def prefixEnd_1385281 : Nat := 4983230072969 + 3 ^ 40 * 1385281 * 2
def baseEnd_1385281 : Nat := 237104998180366605138905

theorem tailTrace_1385281 : CollatzResearch.WordTrace tailWord_1385281 prefixEnd_1385281 237104998180366605138905 := by
  unfold tailWord_1385281
  simp only [CollatzResearch.WordTrace]
  refine ⟨50525348894370999004243697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33683565929580666002829131 50525348894370999004243697)
  ·
    refine ⟨37894011670778249253182773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50525348894370999004243697 37894011670778249253182773)
    ·
      refine ⟨3552563594135460867485885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37894011670778249253182773 3552563594135460867485885)
      ·
        refine ⟨1332211347800797825307207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3552563594135460867485885 1332211347800797825307207)
        ·
          refine ⟨1998317021701196737960811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332211347800797825307207 1998317021701196737960811)
          ·
            refine ⟨2997475532551795106941217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998317021701196737960811 2997475532551795106941217)
            ·
              refine ⟨2248106649413846330205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997475532551795106941217 2248106649413846330205913)
              ·
                refine ⟨1686079987060384747654435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248106649413846330205913 1686079987060384747654435)
                ·
                  refine ⟨2529119980590577121481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686079987060384747654435 2529119980590577121481653)
                  ·
                    refine ⟨237104998180366605138905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2529119980590577121481653 237104998180366605138905)
                    ·
                      rfl

theorem cell23_1385281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1385281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385281 prefixEnd_1385281 := by exact prefixLift 1385281
  have htrace : WordTrace (prefixWord ++ tailWord_1385281) baseStart_1385281 baseEnd_1385281 := by
    simpa [prefixWord, tailWord_1385281, baseEnd_1385281] using wordTrace_append hprefix tailTrace_1385281
  have hstable : (prefixWord ++ tailWord_1385281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385281).length < 2 ^ (prefixWord ++ tailWord_1385281).sum := by decide
  have hdescent : baseEnd_1385281 < baseStart_1385281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385344 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2]
def baseStart_1385344 : Nat := 118140960795 + 1385344 * 2 ^ 59
def prefixEnd_1385344 : Nat := 4983230072969 + 3 ^ 40 * 1385344 * 2
def baseEnd_1385344 : Nat := 711347343822333068928925

theorem tailTrace_1385344 : CollatzResearch.WordTrace tailWord_1385344 prefixEnd_1385344 711347343822333068928925 := by
  unfold tailWord_1385344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25263823346571380381893543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33685097795428507175858057 25263823346571380381893543)
  ·
    refine ⟨37895735019857070572840315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25263823346571380381893543 37895735019857070572840315)
    ·
      refine ⟨56843602529785605859260473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37895735019857070572840315 56843602529785605859260473)
      ·
        refine ⟨42632701897339204394445355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56843602529785605859260473 42632701897339204394445355)
        ·
          refine ⟨63949052846008806591668033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42632701897339204394445355 63949052846008806591668033)
          ·
            refine ⟨47961789634506604943751025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63949052846008806591668033 47961789634506604943751025)
            ·
              refine ⟨35971342225879953707813269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47961789634506604943751025 35971342225879953707813269)
              ·
                refine ⟨1686156666838122830053747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35971342225879953707813269 1686156666838122830053747)
                ·
                  refine ⟨2529235000257184245080621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686156666838122830053747 2529235000257184245080621)
                  ·
                    refine ⟨948463125096444091905233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529235000257184245080621 948463125096444091905233)
                    ·
                      refine ⟨711347343822333068928925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948463125096444091905233 711347343822333068928925)
                      ·
                        rfl

theorem cell23_1385344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_1385344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385344 prefixEnd_1385344 := by exact prefixLift 1385344
  have htrace : WordTrace (prefixWord ++ tailWord_1385344) baseStart_1385344 baseEnd_1385344 := by
    simpa [prefixWord, tailWord_1385344, baseEnd_1385344] using wordTrace_append hprefix tailTrace_1385344
  have hstable : (prefixWord ++ tailWord_1385344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385344).length < 2 ^ (prefixWord ++ tailWord_1385344).sum := by decide
  have hdescent : baseEnd_1385344 < baseStart_1385344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385360 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_1385360 : Nat := 118140960795 + 1385360 * 2 ^ 59
def prefixEnd_1385360 : Nat := 4983230072969 + 3 ^ 40 * 1385360 * 2
def baseEnd_1385360 : Nat := 711355559512805006328851

theorem tailTrace_1385360 : CollatzResearch.WordTrace tailWord_1385360 prefixEnd_1385360 711355559512805006328851 := by
  unfold tailWord_1385360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25264115130542397748184767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33685486840723196997579689 25264115130542397748184767)
  ·
    refine ⟨37896172695813596622277151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25264115130542397748184767 37896172695813596622277151)
    ·
      refine ⟨56844259043720394933415727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37896172695813596622277151 56844259043720394933415727)
      ·
        refine ⟨85266388565580592400123591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56844259043720394933415727 85266388565580592400123591)
        ·
          refine ⟨127899582848370888600185387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85266388565580592400123591 127899582848370888600185387)
          ·
            refine ⟨191849374272556332900278081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127899582848370888600185387 191849374272556332900278081)
            ·
              refine ⟨143887030704417249675208561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191849374272556332900278081 143887030704417249675208561)
              ·
                refine ⟨107915273028312937256406421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143887030704417249675208561 107915273028312937256406421)
                ·
                  refine ⟨5058528423202168933894051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107915273028312937256406421 5058528423202168933894051)
                  ·
                    refine ⟨7587792634803253400841077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058528423202168933894051 7587792634803253400841077)
                    ·
                      refine ⟨711355559512805006328851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7587792634803253400841077 711355559512805006328851)
                      ·
                        rfl

theorem cell23_1385360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_1385360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385360 prefixEnd_1385360 := by exact prefixLift 1385360
  have htrace : WordTrace (prefixWord ++ tailWord_1385360) baseStart_1385360 baseEnd_1385360 := by
    simpa [prefixWord, tailWord_1385360, baseEnd_1385360] using wordTrace_append hprefix tailTrace_1385360
  have hstable : (prefixWord ++ tailWord_1385360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385360).length < 2 ^ (prefixWord ++ tailWord_1385360).sum := by decide
  have hdescent : baseEnd_1385360 < baseStart_1385360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385397 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 7]
def baseStart_1385397 : Nat := 118140960795 + 1385397 * 2 ^ 59
def prefixEnd_1385397 : Nat := 4983230072969 + 3 ^ 40 * 1385397 * 2
def baseEnd_1385397 : Nat := 79041617588557929062909

theorem tailTrace_1385397 : CollatzResearch.WordTrace tailWord_1385397 prefixEnd_1385397 79041617588557929062909 := by
  unfold tailWord_1385397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50529579761950750815466445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33686386507967167210310963 50529579761950750815466445)
  ·
    refine ⟨18948592410731531555799917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50529579761950750815466445 18948592410731531555799917)
    ·
      refine ⟨7105722154024324333424969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18948592410731531555799917 7105722154024324333424969)
      ·
        refine ⟨5329291615518243250068727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105722154024324333424969 5329291615518243250068727)
        ·
          refine ⟨7993937423277364875103091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329291615518243250068727 7993937423277364875103091)
          ·
            refine ⟨11990906134916047312654637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993937423277364875103091 11990906134916047312654637)
            ·
              refine ⟨4496589800593517742245489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11990906134916047312654637 4496589800593517742245489)
              ·
                refine ⟨3372442350445138306684117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4496589800593517742245489 3372442350445138306684117)
                ·
                  refine ⟨79041617588557929062909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3372442350445138306684117 79041617588557929062909)
                  ·
                    rfl

theorem cell23_1385397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_1385397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385397 prefixEnd_1385397 := by exact prefixLift 1385397
  have htrace : WordTrace (prefixWord ++ tailWord_1385397) baseStart_1385397 baseEnd_1385397 := by
    simpa [prefixWord, tailWord_1385397, baseEnd_1385397] using wordTrace_append hprefix tailTrace_1385397
  have hstable : (prefixWord ++ tailWord_1385397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385397).length < 2 ^ (prefixWord ++ tailWord_1385397).sum := by decide
  have hdescent : baseEnd_1385397 < baseStart_1385397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385412 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1385412 : Nat := 118140960795 + 1385412 * 2 ^ 59
def prefixEnd_1385412 : Nat := 4983230072969 + 3 ^ 40 * 1385412 * 2
def baseEnd_1385412 : Nat := 711382260506838802878613

theorem tailTrace_1385412 : CollatzResearch.WordTrace tailWord_1385412 prefixEnd_1385412 711382260506838802878613 := by
  unfold tailWord_1385412
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265063428448204188631245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33686751237930938918174993 25265063428448204188631245)
  ·
    refine ⟨9474398785668076570736717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25265063428448204188631245 9474398785668076570736717)
    ·
      refine ⟨3552899544625528714026269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9474398785668076570736717 3552899544625528714026269)
      ·
        refine ⟨1332337329234573267759851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3552899544625528714026269 1332337329234573267759851)
        ·
          refine ⟨1998505993851859901639777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332337329234573267759851 1998505993851859901639777)
          ·
            refine ⟨1498879495388894926229833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998505993851859901639777 1498879495388894926229833)
            ·
              refine ⟨1124159621541671194672375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498879495388894926229833 1124159621541671194672375)
              ·
                refine ⟨1686239432312506792008563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124159621541671194672375 1686239432312506792008563)
                ·
                  refine ⟨2529359148468760188012845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686239432312506792008563 2529359148468760188012845)
                  ·
                    refine ⟨948509680675785070504817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529359148468760188012845 948509680675785070504817)
                    ·
                      refine ⟨711382260506838802878613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948509680675785070504817 711382260506838802878613)
                      ·
                        rfl

theorem cell23_1385412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1385412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385412 prefixEnd_1385412 := by exact prefixLift 1385412
  have htrace : WordTrace (prefixWord ++ tailWord_1385412) baseStart_1385412 baseEnd_1385412 := by
    simpa [prefixWord, tailWord_1385412, baseEnd_1385412] using wordTrace_append hprefix tailTrace_1385412
  have hstable : (prefixWord ++ tailWord_1385412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385412).length < 2 ^ (prefixWord ++ tailWord_1385412).sum := by decide
  have hdescent : baseEnd_1385412 < baseStart_1385412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385442 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1385442 : Nat := 118140960795 + 1385442 * 2 ^ 59
def prefixEnd_1385442 : Nat := 4983230072969 + 3 ^ 40 * 1385442 * 2
def baseEnd_1385442 : Nat := 711397664926473685503475

theorem tailTrace_1385442 : CollatzResearch.WordTrace tailWord_1385442 prefixEnd_1385442 711397664926473685503475 := by
  unfold tailWord_1385442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632805261696930875213645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33687480697858482333903053 12632805261696930875213645)
  ·
    refine ⟨4737301973136349078205117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12632805261696930875213645 4737301973136349078205117)
    ·
      refine ⟨1776488239926130904326919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4737301973136349078205117 1776488239926130904326919)
      ·
        refine ⟨2664732359889196356490379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776488239926130904326919 2664732359889196356490379)
        ·
          refine ⟨3997098539833794534735569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664732359889196356490379 3997098539833794534735569)
          ·
            refine ⟨2997823904875345901051677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3997098539833794534735569 2997823904875345901051677)
            ·
              refine ⟨1124183964328254712894379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2997823904875345901051677 1124183964328254712894379)
              ·
                refine ⟨1686275946492382069341569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124183964328254712894379 1686275946492382069341569)
                ·
                  refine ⟨1264706959869286552006177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686275946492382069341569 1264706959869286552006177)
                  ·
                    refine ⟨948530219901964914004633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264706959869286552006177 948530219901964914004633)
                    ·
                      refine ⟨711397664926473685503475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948530219901964914004633 711397664926473685503475)
                      ·
                        rfl

theorem cell23_1385442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1385442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385442 prefixEnd_1385442 := by exact prefixLift 1385442
  have htrace : WordTrace (prefixWord ++ tailWord_1385442) baseStart_1385442 baseEnd_1385442 := by
    simpa [prefixWord, tailWord_1385442, baseEnd_1385442] using wordTrace_append hprefix tailTrace_1385442
  have hstable : (prefixWord ++ tailWord_1385442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385442).length < 2 ^ (prefixWord ++ tailWord_1385442).sum := by decide
  have hdescent : baseEnd_1385442 < baseStart_1385442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385484 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1385484 : Nat := 118140960795 + 1385484 * 2 ^ 59
def prefixEnd_1385484 : Nat := 4983230072969 + 3 ^ 40 * 1385484 * 2
def baseEnd_1385484 : Nat := 711419231113962521178281

theorem tailTrace_1385484 : CollatzResearch.WordTrace tailWord_1385484 prefixEnd_1385484 711419231113962521178281 := by
  unfold tailWord_1385484
  simp only [CollatzResearch.WordTrace]
  refine ⟨25266376456317782336941753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33688501941757043115922337 25266376456317782336941753)
  ·
    refine ⟨18949782342238336752706315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25266376456317782336941753 18949782342238336752706315)
    ·
      refine ⟨28424673513357505129059473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18949782342238336752706315 28424673513357505129059473)
      ·
        refine ⟨21318505135018128846794605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28424673513357505129059473 21318505135018128846794605)
        ·
          refine ⟨7994439425631798317547977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21318505135018128846794605 7994439425631798317547977)
          ·
            refine ⟨5995829569223848738160983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7994439425631798317547977 5995829569223848738160983)
            ·
              refine ⟨8993744353835773107241475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995829569223848738160983 8993744353835773107241475)
              ·
                refine ⟨13490616530753659660862213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993744353835773107241475 13490616530753659660862213)
                ·
                  refine ⟨2529490599516311186411665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13490616530753659660862213 2529490599516311186411665)
                  ·
                    refine ⟨1897117949637233389808749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529490599516311186411665 1897117949637233389808749)
                    ·
                      refine ⟨711419231113962521178281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897117949637233389808749 711419231113962521178281)
                      ·
                        rfl

theorem cell23_1385484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1385484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385484 prefixEnd_1385484 := by exact prefixLift 1385484
  have htrace : WordTrace (prefixWord ++ tailWord_1385484) baseStart_1385484 baseEnd_1385484 := by
    simpa [prefixWord, tailWord_1385484, baseEnd_1385484] using wordTrace_append hprefix tailTrace_1385484
  have hstable : (prefixWord ++ tailWord_1385484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385484).length < 2 ^ (prefixWord ++ tailWord_1385484).sum := by decide
  have hdescent : baseEnd_1385484 < baseStart_1385484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385541 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_1385541 : Nat := 118140960795 + 1385541 * 2 ^ 59
def prefixEnd_1385541 : Nat := 4983230072969 + 3 ^ 40 * 1385541 * 2
def baseEnd_1385541 : Nat := 711448499511268798165519

theorem tailTrace_1385541 : CollatzResearch.WordTrace tailWord_1385541 prefixEnd_1385541 711448499511268798165519 := by
  unfold tailWord_1385541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50534831873429063408708477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33689887915619375605805651 50534831873429063408708477)
  ·
    refine ⟨18950561952535898778265679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50534831873429063408708477 18950561952535898778265679)
    ·
      refine ⟨28425842928803848167398519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18950561952535898778265679 28425842928803848167398519)
      ·
        refine ⟨42638764393205772251097779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28425842928803848167398519 42638764393205772251097779)
        ·
          refine ⟨63958146589808658376646669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42638764393205772251097779 63958146589808658376646669)
          ·
            refine ⟨23984304971178246891242501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63958146589808658376646669 23984304971178246891242501)
            ·
              refine ⟨4497057182095921292107969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23984304971178246891242501 4497057182095921292107969)
              ·
                refine ⟨3372792886571940969080977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497057182095921292107969 3372792886571940969080977)
                ·
                  refine ⟨2529594664928955726810733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3372792886571940969080977 2529594664928955726810733)
                  ·
                    refine ⟨948597999348358397554025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529594664928955726810733 948597999348358397554025)
                    ·
                      refine ⟨711448499511268798165519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948597999348358397554025 711448499511268798165519)
                      ·
                        rfl

theorem cell23_1385541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_1385541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385541 prefixEnd_1385541 := by exact prefixLift 1385541
  have htrace : WordTrace (prefixWord ++ tailWord_1385541) baseStart_1385541 baseEnd_1385541 := by
    simpa [prefixWord, tailWord_1385541, baseEnd_1385541] using wordTrace_append hprefix tailTrace_1385541
  have hstable : (prefixWord ++ tailWord_1385541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385541).length < 2 ^ (prefixWord ++ tailWord_1385541).sum := by decide
  have hdescent : baseEnd_1385541 < baseStart_1385541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385542 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1385542 : Nat := 118140960795 + 1385542 * 2 ^ 59
def prefixEnd_1385542 : Nat := 4983230072969 + 3 ^ 40 * 1385542 * 2
def baseEnd_1385542 : Nat := 237149670997307764751005

theorem tailTrace_1385542 : CollatzResearch.WordTrace tailWord_1385542 prefixEnd_1385542 237149670997307764751005 := by
  unfold tailWord_1385542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579214635825795018109215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33689912230950293719663253 1579214635825795018109215)
  ·
    refine ⟨2368821953738692527163823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579214635825795018109215 2368821953738692527163823)
    ·
      refine ⟨3553232930608038790745735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368821953738692527163823 3553232930608038790745735)
      ·
        refine ⟨5329849395912058186118603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553232930608038790745735 5329849395912058186118603)
        ·
          refine ⟨7994774093868087279177905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329849395912058186118603 7994774093868087279177905)
          ·
            refine ⟨5996080570401065459383429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7994774093868087279177905 5996080570401065459383429)
            ·
              refine ⟨1124265106950199773634393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5996080570401065459383429 1124265106950199773634393)
              ·
                refine ⟨843198830212649830225795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124265106950199773634393 843198830212649830225795)
                ·
                  refine ⟨1264798245318974745338693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843198830212649830225795 1264798245318974745338693)
                  ·
                    refine ⟨237149670997307764751005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264798245318974745338693 237149670997307764751005)
                    ·
                      rfl

theorem cell23_1385542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1385542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385542 prefixEnd_1385542 := by exact prefixLift 1385542
  have htrace : WordTrace (prefixWord ++ tailWord_1385542) baseStart_1385542 baseEnd_1385542 := by
    simpa [prefixWord, tailWord_1385542, baseEnd_1385542] using wordTrace_append hprefix tailTrace_1385542
  have hstable : (prefixWord ++ tailWord_1385542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385542).length < 2 ^ (prefixWord ++ tailWord_1385542).sum := by decide
  have hdescent : baseEnd_1385542 < baseStart_1385542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385565 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1385565 : Nat := 118140960795 + 1385565 * 2 ^ 59
def prefixEnd_1385565 : Nat := 4983230072969 + 3 ^ 40 * 1385565 * 2
def baseEnd_1385565 : Nat := 711460823046976704265409

theorem tailTrace_1385565 : CollatzResearch.WordTrace tailWord_1385565 prefixEnd_1385565 711460823046976704265409 := by
  unfold tailWord_1385565
  simp only [CollatzResearch.WordTrace]
  refine ⟨50535707225342115507582149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33690471483561410338388099 50535707225342115507582149)
  ·
    refine ⟨9475445104751646657671653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50535707225342115507582149 9475445104751646657671653)
    ·
      refine ⟨1776645957140933748313435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9475445104751646657671653 1776645957140933748313435)
      ·
        refine ⟨2664968935711400622470153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776645957140933748313435 2664968935711400622470153)
        ·
          refine ⟨1998726701783550466852615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2664968935711400622470153 1998726701783550466852615)
          ·
            refine ⟨2998090052675325700278923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998726701783550466852615 2998090052675325700278923)
            ·
              refine ⟨4497135079012988550418385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998090052675325700278923 4497135079012988550418385)
              ·
                refine ⟨3372851309259741412813789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497135079012988550418385 3372851309259741412813789)
                ·
                  refine ⟨1264819240972403029805171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3372851309259741412813789 1264819240972403029805171)
                  ·
                    refine ⟨1897228861458604544707757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1264819240972403029805171 1897228861458604544707757)
                    ·
                      refine ⟨711460823046976704265409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897228861458604544707757 711460823046976704265409)
                      ·
                        rfl

theorem cell23_1385565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1385565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385565 prefixEnd_1385565 := by exact prefixLift 1385565
  have htrace : WordTrace (prefixWord ++ tailWord_1385565) baseStart_1385565 baseEnd_1385565 := by
    simpa [prefixWord, tailWord_1385565, baseEnd_1385565] using wordTrace_append hprefix tailTrace_1385565
  have hstable : (prefixWord ++ tailWord_1385565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385565).length < 2 ^ (prefixWord ++ tailWord_1385565).sum := by decide
  have hdescent : baseEnd_1385565 < baseStart_1385565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385584 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_1385584 : Nat := 118140960795 + 1385584 * 2 ^ 59
def prefixEnd_1385584 : Nat := 4983230072969 + 3 ^ 40 * 1385584 * 2
def baseEnd_1385584 : Nat := 711470579179412129927821

theorem tailTrace_1385584 : CollatzResearch.WordTrace tailWord_1385584 prefixEnd_1385584 711470579179412129927821 := by
  unfold tailWord_1385584
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268200106136640876261903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33690933474848854501682537 25268200106136640876261903)
  ·
    refine ⟨37902300159204961314392855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25268200106136640876261903 37902300159204961314392855)
    ·
      refine ⟨56853450238807441971589283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37902300159204961314392855 56853450238807441971589283)
      ·
        refine ⟨85280175358211162957383925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56853450238807441971589283 85280175358211162957383925)
        ·
          refine ⟨7995016439832296527254743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85280175358211162957383925 7995016439832296527254743)
          ·
            refine ⟨11992524659748444790882115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995016439832296527254743 11992524659748444790882115)
            ·
              refine ⟨17988786989622667186323173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11992524659748444790882115 17988786989622667186323173)
              ·
                refine ⟨3372897560554250097435595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17988786989622667186323173 3372897560554250097435595)
                ·
                  refine ⟨5059346340831375146153393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372897560554250097435595 5059346340831375146153393)
                  ·
                    refine ⟨3794509755623531359615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059346340831375146153393 3794509755623531359615045)
                    ·
                      refine ⟨711470579179412129927821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3794509755623531359615045 711470579179412129927821)
                      ·
                        rfl

theorem cell23_1385584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_1385584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385584 prefixEnd_1385584 := by exact prefixLift 1385584
  have htrace : WordTrace (prefixWord ++ tailWord_1385584) baseStart_1385584 baseEnd_1385584 := by
    simpa [prefixWord, tailWord_1385584, baseEnd_1385584] using wordTrace_append hprefix tailTrace_1385584
  have hstable : (prefixWord ++ tailWord_1385584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385584).length < 2 ^ (prefixWord ++ tailWord_1385584).sum := by decide
  have hdescent : baseEnd_1385584 < baseStart_1385584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385591 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_1385591 : Nat := 118140960795 + 1385591 * 2 ^ 59
def prefixEnd_1385591 : Nat := 4983230072969 + 3 ^ 40 * 1385591 * 2
def baseEnd_1385591 : Nat := 711474173543993602540289

theorem tailTrace_1385591 : CollatzResearch.WordTrace tailWord_1385591 prefixEnd_1385591 711474173543993602540289 := by
  unfold tailWord_1385591
  simp only [CollatzResearch.WordTrace]
  refine ⟨50536655523247921948028627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33691103682165281298685751 50536655523247921948028627)
  ·
    refine ⟨75804983284871882922042941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50536655523247921948028627 75804983284871882922042941)
    ·
      refine ⟨28426868731826956095766103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75804983284871882922042941 28426868731826956095766103)
      ·
        refine ⟨42640303097740434143649155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28426868731826956095766103 42640303097740434143649155)
        ·
          refine ⟨63960454646610651215473733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42640303097740434143649155 63960454646610651215473733)
          ·
            refine ⟨11992585246239497102901325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63960454646610651215473733 11992585246239497102901325)
            ·
              refine ⟨4497219467339811413587997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11992585246239497102901325 4497219467339811413587997)
              ·
                refine ⟨1686457300252429280095499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497219467339811413587997 1686457300252429280095499)
                ·
                  refine ⟨2529685950378643920143249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686457300252429280095499 2529685950378643920143249)
                  ·
                    refine ⟨1897264462783982940107437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2529685950378643920143249 1897264462783982940107437)
                    ·
                      refine ⟨711474173543993602540289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897264462783982940107437 711474173543993602540289)
                      ·
                        rfl

theorem cell23_1385591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_1385591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385591 prefixEnd_1385591 := by exact prefixLift 1385591
  have htrace : WordTrace (prefixWord ++ tailWord_1385591) baseStart_1385591 baseEnd_1385591 := by
    simpa [prefixWord, tailWord_1385591, baseEnd_1385591] using wordTrace_append hprefix tailTrace_1385591
  have hstable : (prefixWord ++ tailWord_1385591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385591).length < 2 ^ (prefixWord ++ tailWord_1385591).sum := by decide
  have hdescent : baseEnd_1385591 < baseStart_1385591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385605 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_1385605 : Nat := 118140960795 + 1385605 * 2 ^ 59
def prefixEnd_1385605 : Nat := 4983230072969 + 3 ^ 40 * 1385605 * 2
def baseEnd_1385605 : Nat := 711481362273156547765225

theorem tailTrace_1385605 : CollatzResearch.WordTrace tailWord_1385605 prefixEnd_1385605 711481362273156547765225 := by
  unfold tailWord_1385605
  simp only [CollatzResearch.WordTrace]
  refine ⟨50537166145197202339038269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33691444096798134892692179 50537166145197202339038269)
  ·
    refine ⟨18951437304448950877139351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50537166145197202339038269 18951437304448950877139351)
    ·
      refine ⟨28427155956673426315709027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18951437304448950877139351 28427155956673426315709027)
      ·
        refine ⟨42640733935010139473563541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28427155956673426315709027 42640733935010139473563541)
        ·
          refine ⟨1998784403203600287823291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42640733935010139473563541 1998784403203600287823291)
          ·
            refine ⟨2998176604805400431734937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998784403203600287823291 2998176604805400431734937)
            ·
              refine ⟨2248632453604050323801203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998176604805400431734937 2248632453604050323801203)
              ·
                refine ⟨3372948680406075485701805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248632453604050323801203 3372948680406075485701805)
                ·
                  refine ⟨1264855755152278307138177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3372948680406075485701805 1264855755152278307138177)
                  ·
                    refine ⟨948641816364208730353633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264855755152278307138177 948641816364208730353633)
                    ·
                      refine ⟨711481362273156547765225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948641816364208730353633 711481362273156547765225)
                      ·
                        rfl

theorem cell23_1385605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_1385605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385605 prefixEnd_1385605 := by exact prefixLift 1385605
  have htrace : WordTrace (prefixWord ++ tailWord_1385605) baseStart_1385605 baseEnd_1385605 := by
    simpa [prefixWord, tailWord_1385605, baseEnd_1385605] using wordTrace_append hprefix tailTrace_1385605
  have hstable : (prefixWord ++ tailWord_1385605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385605).length < 2 ^ (prefixWord ++ tailWord_1385605).sum := by decide
  have hdescent : baseEnd_1385605 < baseStart_1385605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385618 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1385618 : Nat := 118140960795 + 1385618 * 2 ^ 59
def prefixEnd_1385618 : Nat := 4983230072969 + 3 ^ 40 * 1385618 * 2
def baseEnd_1385618 : Nat := 711488037521664996902665

theorem tailTrace_1385618 : CollatzResearch.WordTrace tailWord_1385618 prefixEnd_1385618 711488037521664996902665 := by
  unfold tailWord_1385618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634410073537526389815377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33691760196100070372841005 12634410073537526389815377)
  ·
    refine ⟨9475807555153144792361533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12634410073537526389815377 9475807555153144792361533)
    ·
      refine ⟨3553427833182429297135575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9475807555153144792361533 3553427833182429297135575)
      ·
        refine ⟨5330141749773643945703363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553427833182429297135575 5330141749773643945703363)
        ·
          refine ⟨7995212624660465918555045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330141749773643945703363 7995212624660465918555045)
          ·
            refine ⟨1499102367123837359729071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7995212624660465918555045 1499102367123837359729071)
            ·
              refine ⟨2248653550685756039593607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499102367123837359729071 2248653550685756039593607)
              ·
                refine ⟨3372980326028634059390411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248653550685756039593607 3372980326028634059390411)
                ·
                  refine ⟨5059470489042951089085617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372980326028634059390411 5059470489042951089085617)
                  ·
                    refine ⟨3794602866782213316814213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059470489042951089085617 3794602866782213316814213)
                    ·
                      refine ⟨711488037521664996902665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3794602866782213316814213 711488037521664996902665)
                      ·
                        rfl

theorem cell23_1385618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1385618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385618 prefixEnd_1385618 := by exact prefixLift 1385618
  have htrace : WordTrace (prefixWord ++ tailWord_1385618) baseStart_1385618 baseEnd_1385618 := by
    simpa [prefixWord, tailWord_1385618, baseEnd_1385618] using wordTrace_append hprefix tailTrace_1385618
  have hstable : (prefixWord ++ tailWord_1385618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385618).length < 2 ^ (prefixWord ++ tailWord_1385618).sum := by decide
  have hdescent : baseEnd_1385618 < baseStart_1385618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385627 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_1385627 : Nat := 118140960795 + 1385627 * 2 ^ 59
def prefixEnd_1385627 : Nat := 4983230072969 + 3 ^ 40 * 1385627 * 2
def baseEnd_1385627 : Nat := 711492658847555461690123

theorem tailTrace_1385627 : CollatzResearch.WordTrace tailWord_1385627 prefixEnd_1385627 711492658847555461690123 := by
  unfold tailWord_1385627
  simp only [CollatzResearch.WordTrace]
  refine ⟨50537968551117500096339135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33691979034078333397559423 50537968551117500096339135)
  ·
    refine ⟨75806952826676250144508703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50537968551117500096339135 75806952826676250144508703)
    ·
      refine ⟨113710429240014375216763055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75806952826676250144508703 113710429240014375216763055)
      ·
        refine ⟨170565643860021562825144583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113710429240014375216763055 170565643860021562825144583)
        ·
          refine ⟨255848465790032344237716875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170565643860021562825144583 255848465790032344237716875)
          ·
            refine ⟨383772698685048516356575313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255848465790032344237716875 383772698685048516356575313)
            ·
              refine ⟨287829524013786387267431485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383772698685048516356575313 287829524013786387267431485)
              ·
                refine ⟨107936071505169895225286807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287829524013786387267431485 107936071505169895225286807)
                ·
                  refine ⟨161904107257754842837930211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107936071505169895225286807 161904107257754842837930211)
                  ·
                    refine ⟨242856160886632264256895317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161904107257754842837930211 242856160886632264256895317)
                    ·
                      refine ⟨711492658847555461690123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 242856160886632264256895317 711492658847555461690123)
                      ·
                        rfl

theorem cell23_1385627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_1385627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385627 prefixEnd_1385627 := by exact prefixLift 1385627
  have htrace : WordTrace (prefixWord ++ tailWord_1385627) baseStart_1385627 baseEnd_1385627 := by
    simpa [prefixWord, tailWord_1385627, baseEnd_1385627] using wordTrace_append hprefix tailTrace_1385627
  have hstable : (prefixWord ++ tailWord_1385627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385627).length < 2 ^ (prefixWord ++ tailWord_1385627).sum := by decide
  have hdescent : baseEnd_1385627 < baseStart_1385627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385639 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1385639 : Nat := 118140960795 + 1385639 * 2 ^ 59
def prefixEnd_1385639 : Nat := 4983230072969 + 3 ^ 40 * 1385639 * 2
def baseEnd_1385639 : Nat := 711498820615409414740069

theorem tailTrace_1385639 : CollatzResearch.WordTrace tailWord_1385639 prefixEnd_1385639 711498820615409414740069 := by
  unfold tailWord_1385639
  simp only [CollatzResearch.WordTrace]
  refine ⟨50538406227074026145775971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33692270818049350763850647 50538406227074026145775971)
  ·
    refine ⟨75807609340611039218663957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50538406227074026145775971 75807609340611039218663957)
    ·
      refine ⟨3553481687841142463374873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75807609340611039218663957 3553481687841142463374873)
      ·
        refine ⟨2665111265880856847531155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553481687841142463374873 2665111265880856847531155)
        ·
          refine ⟨3997666898821285271296733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665111265880856847531155 3997666898821285271296733)
          ·
            refine ⟨1499125087057981976736275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3997666898821285271296733 1499125087057981976736275)
            ·
              refine ⟨2248687630586972965104413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499125087057981976736275 2248687630586972965104413)
              ·
                refine ⟨843257861470114861914155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2248687630586972965104413 843257861470114861914155)
                ·
                  refine ⟨1264886792205172292871233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843257861470114861914155 1264886792205172292871233)
                  ·
                    refine ⟨948665094153879219653425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1264886792205172292871233 948665094153879219653425)
                    ·
                      refine ⟨711498820615409414740069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948665094153879219653425 711498820615409414740069)
                      ·
                        rfl

theorem cell23_1385639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1385639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385639 prefixEnd_1385639 := by exact prefixLift 1385639
  have htrace : WordTrace (prefixWord ++ tailWord_1385639) baseStart_1385639 baseEnd_1385639 := by
    simpa [prefixWord, tailWord_1385639, baseEnd_1385639] using wordTrace_append hprefix tailTrace_1385639
  have hstable : (prefixWord ++ tailWord_1385639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385639).length < 2 ^ (prefixWord ++ tailWord_1385639).sum := by decide
  have hdescent : baseEnd_1385639 < baseStart_1385639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385666 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1385666 : Nat := 118140960795 + 1385666 * 2 ^ 59
def prefixEnd_1385666 : Nat := 4983230072969 + 3 ^ 40 * 1385666 * 2
def baseEnd_1385666 : Nat := 237170894864360269700815

theorem tailTrace_1385666 : CollatzResearch.WordTrace tailWord_1385666 prefixEnd_1385666 237170894864360269700815 := by
  unfold tailWord_1385666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634847749494052439252213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33692927331984139838005901 12634847749494052439252213)
  ·
    refine ⟨1184516976515067416179895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12634847749494052439252213 1184516976515067416179895)
    ·
      refine ⟨1776775464772601124269843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184516976515067416179895 1776775464772601124269843)
      ·
        refine ⟨2665163197158901686404765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776775464772601124269843 2665163197158901686404765)
        ·
          refine ⟨999436198934588132401787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2665163197158901686404765 999436198934588132401787)
          ·
            refine ⟨1499154298401882198602681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999436198934588132401787 1499154298401882198602681)
            ·
              refine ⟨1124365723801411648952011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499154298401882198602681 1124365723801411648952011)
              ·
                refine ⟨1686548585702117473428017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124365723801411648952011 1686548585702117473428017)
                ·
                  refine ⟨1264911439276588105071013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686548585702117473428017 1264911439276588105071013)
                  ·
                    refine ⟨237170894864360269700815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264911439276588105071013 237170894864360269700815)
                    ·
                      rfl

theorem cell23_1385666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1385666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385666 prefixEnd_1385666 := by exact prefixLift 1385666
  have htrace : WordTrace (prefixWord ++ tailWord_1385666) baseStart_1385666 baseEnd_1385666 := by
    simpa [prefixWord, tailWord_1385666, baseEnd_1385666] using wordTrace_append hprefix tailTrace_1385666
  have hstable : (prefixWord ++ tailWord_1385666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385666).length < 2 ^ (prefixWord ++ tailWord_1385666).sum := by decide
  have hdescent : baseEnd_1385666 < baseStart_1385666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385721 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 7, 2]
def baseStart_1385721 : Nat := 118140960795 + 1385721 * 2 ^ 59
def prefixEnd_1385721 : Nat := 4983230072969 + 3 ^ 40 * 1385721 * 2
def baseEnd_1385721 : Nat := 711540926029078093914691

theorem tailTrace_1385721 : CollatzResearch.WordTrace tailWord_1385721 prefixEnd_1385721 711540926029078093914691 := by
  unfold tailWord_1385721
  simp only [CollatzResearch.WordTrace]
  refine ⟨50541397012776954150261017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33694264675184636100174011 50541397012776954150261017)
  ·
    refine ⟨37906047759582715612695763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50541397012776954150261017 37906047759582715612695763)
    ·
      refine ⟨56859071639374073419043645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37906047759582715612695763 56859071639374073419043645)
      ·
        refine ⟨21322151864765277532141367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56859071639374073419043645 21322151864765277532141367)
        ·
          refine ⟨31983227797147916298212051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21322151864765277532141367 31983227797147916298212051)
          ·
            refine ⟨47974841695721874447318077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31983227797147916298212051 47974841695721874447318077)
            ·
              refine ⟨17990565635895702917744279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47974841695721874447318077 17990565635895702917744279)
              ·
                refine ⟨26985848453843554376616419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17990565635895702917744279 26985848453843554376616419)
                ·
                  refine ⟨40478772680765331564924629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26985848453843554376616419 40478772680765331564924629)
                  ·
                    refine ⟨948721234705437458552921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40478772680765331564924629 948721234705437458552921)
                    ·
                      refine ⟨711540926029078093914691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948721234705437458552921 711540926029078093914691)
                      ·
                        rfl

theorem cell23_1385721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_1385721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385721 prefixEnd_1385721 := by exact prefixLift 1385721
  have htrace : WordTrace (prefixWord ++ tailWord_1385721) baseStart_1385721 baseEnd_1385721 := by
    simpa [prefixWord, tailWord_1385721, baseEnd_1385721] using wordTrace_append hprefix tailTrace_1385721
  have hstable : (prefixWord ++ tailWord_1385721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385721).length < 2 ^ (prefixWord ++ tailWord_1385721).sum := by decide
  have hdescent : baseEnd_1385721 < baseStart_1385721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385751 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1385751 : Nat := 118140960795 + 1385751 * 2 ^ 59
def prefixEnd_1385751 : Nat := 4983230072969 + 3 ^ 40 * 1385751 * 2
def baseEnd_1385751 : Nat := 711556330448712976539553

theorem tailTrace_1385751 : CollatzResearch.WordTrace tailWord_1385751 prefixEnd_1385751 711556330448712976539553 := by
  unfold tailWord_1385751
  simp only [CollatzResearch.WordTrace]
  refine ⟨50542491202668269273853107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33694994135112179515902071 50542491202668269273853107)
  ·
    refine ⟨75813736804002403910779661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50542491202668269273853107 75813736804002403910779661)
    ·
      refine ⟨28430151301500901466542373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75813736804002403910779661 28430151301500901466542373)
      ·
        refine ⟨5330653369031419024976695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28430151301500901466542373 5330653369031419024976695)
        ·
          refine ⟨7995980053547128537465043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330653369031419024976695 7995980053547128537465043)
          ·
            refine ⟨11993970080320692806197565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995980053547128537465043 11993970080320692806197565)
            ·
              refine ⟨4497738780120259802324087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11993970080320692806197565 4497738780120259802324087)
              ·
                refine ⟨6746608170180389703486131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497738780120259802324087 6746608170180389703486131)
                ·
                  refine ⟨10119912255270584555229197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6746608170180389703486131 10119912255270584555229197)
                  ·
                    refine ⟨3794967095726469208210949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10119912255270584555229197 3794967095726469208210949)
                    ·
                      refine ⟨711556330448712976539553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3794967095726469208210949 711556330448712976539553)
                      ·
                        rfl

theorem cell23_1385751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1385751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385751 prefixEnd_1385751 := by exact prefixLift 1385751
  have htrace : WordTrace (prefixWord ++ tailWord_1385751) baseStart_1385751 baseEnd_1385751 := by
    simpa [prefixWord, tailWord_1385751, baseEnd_1385751] using wordTrace_append hprefix tailTrace_1385751
  have hstable : (prefixWord ++ tailWord_1385751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385751).length < 2 ^ (prefixWord ++ tailWord_1385751).sum := by decide
  have hdescent : baseEnd_1385751 < baseStart_1385751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385761 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1385761 : Nat := 118140960795 + 1385761 * 2 ^ 59
def prefixEnd_1385761 : Nat := 4983230072969 + 3 ^ 40 * 1385761 * 2
def baseEnd_1385761 : Nat := 237187155085085979138169

theorem tailTrace_1385761 : CollatzResearch.WordTrace tailWord_1385761 prefixEnd_1385761 237187155085085979138169 := by
  unfold tailWord_1385761
  simp only [CollatzResearch.WordTrace]
  refine ⟨50542855932632040981717137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33695237288421360654478091 50542855932632040981717137)
  ·
    refine ⟨37907141949474030736287853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50542855932632040981717137 37907141949474030736287853)
    ·
      refine ⟨14215178231052761526107945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37907141949474030736287853 14215178231052761526107945)
      ·
        refine ⟨10661383673289571144580959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14215178231052761526107945 10661383673289571144580959)
        ·
          refine ⟨15992075509934356716871439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10661383673289571144580959 15992075509934356716871439)
          ·
            refine ⟨23988113264901535075307159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15992075509934356716871439 23988113264901535075307159)
            ·
              refine ⟨35982169897352302612960739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23988113264901535075307159 35982169897352302612960739)
              ·
                refine ⟨53973254846028453919441109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35982169897352302612960739 53973254846028453919441109)
                ·
                  refine ⟨1264998160453791888736901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 53973254846028453919441109 1264998160453791888736901)
                  ·
                    refine ⟨237187155085085979138169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264998160453791888736901 237187155085085979138169)
                    ·
                      rfl

theorem cell23_1385761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1385761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385761 prefixEnd_1385761 := by exact prefixLift 1385761
  have htrace : WordTrace (prefixWord ++ tailWord_1385761) baseStart_1385761 baseEnd_1385761 := by
    simpa [prefixWord, tailWord_1385761, baseEnd_1385761] using wordTrace_append hprefix tailTrace_1385761
  have hstable : (prefixWord ++ tailWord_1385761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385761).length < 2 ^ (prefixWord ++ tailWord_1385761).sum := by decide
  have hdescent : baseEnd_1385761 < baseStart_1385761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385778 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_1385778 : Nat := 118140960795 + 1385778 * 2 ^ 59
def prefixEnd_1385778 : Nat := 4983230072969 + 3 ^ 40 * 1385778 * 2
def baseEnd_1385778 : Nat := 237190064808794790300643

theorem tailTrace_1385778 : CollatzResearch.WordTrace tailWord_1385778 prefixEnd_1385778 237190064808794790300643 := by
  unfold tailWord_1385778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635868993392613221271497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33695650649046968590057325 12635868993392613221271497)
  ·
    refine ⟨9476901745044459915953623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12635868993392613221271497 9476901745044459915953623)
    ·
      refine ⟨14215352617566689873930435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9476901745044459915953623 14215352617566689873930435)
      ·
        refine ⟨21323028926350034810895653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14215352617566689873930435 21323028926350034810895653)
        ·
          refine ⟨3998067923690631527042935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21323028926350034810895653 3998067923690631527042935)
          ·
            refine ⟨5997101885535947290564403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998067923690631527042935 5997101885535947290564403)
            ·
              refine ⟨8995652828303920935846605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997101885535947290564403 8995652828303920935846605)
              ·
                refine ⟨3373369810613970350942477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8995652828303920935846605 3373369810613970350942477)
                ·
                  refine ⟨1265013678980238881603429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3373369810613970350942477 1265013678980238881603429)
                  ·
                    refine ⟨237190064808794790300643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265013678980238881603429 237190064808794790300643)
                    ·
                      rfl

theorem cell23_1385778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_1385778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385778 prefixEnd_1385778 := by exact prefixLift 1385778
  have htrace : WordTrace (prefixWord ++ tailWord_1385778) baseStart_1385778 baseEnd_1385778 := by
    simpa [prefixWord, tailWord_1385778, baseEnd_1385778] using wordTrace_append hprefix tailTrace_1385778
  have hstable : (prefixWord ++ tailWord_1385778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385778).length < 2 ^ (prefixWord ++ tailWord_1385778).sum := by decide
  have hdescent : baseEnd_1385778 < baseStart_1385778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385818 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1385818 : Nat := 118140960795 + 1385818 * 2 ^ 59
def prefixEnd_1385818 : Nat := 4983230072969 + 3 ^ 40 * 1385818 * 2
def baseEnd_1385818 : Nat := 711590733652564214401745

theorem tailTrace_1385818 : CollatzResearch.WordTrace tailWord_1385818 prefixEnd_1385818 711590733652564214401745 := by
  unfold tailWord_1385818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12636233723356384929135527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33696623262283693144361405 12636233723356384929135527)
  ·
    refine ⟨18954350585034577393703291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12636233723356384929135527 18954350585034577393703291)
    ·
      refine ⟨28431525877551866090554937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18954350585034577393703291 28431525877551866090554937)
      ·
        refine ⟨21323644408163899567916203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28431525877551866090554937 21323644408163899567916203)
        ·
          refine ⟨31985466612245849351874305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21323644408163899567916203 31985466612245849351874305)
          ·
            refine ⟨23989099959184387013905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31985466612245849351874305 23989099959184387013905729)
            ·
              refine ⟨17991824969388290260429297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23989099959184387013905729 17991824969388290260429297)
              ·
                refine ⟨13493868727041217695321973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17991824969388290260429297 13493868727041217695321973)
                ·
                  refine ⟨1265050193160114158936435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13493868727041217695321973 1265050193160114158936435)
                  ·
                    refine ⟨1897575289740171238404653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265050193160114158936435 1897575289740171238404653)
                    ·
                      refine ⟨711590733652564214401745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897575289740171238404653 711590733652564214401745)
                      ·
                        rfl

theorem cell23_1385818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1385818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385818 prefixEnd_1385818 := by exact prefixLift 1385818
  have htrace : WordTrace (prefixWord ++ tailWord_1385818) baseStart_1385818 baseEnd_1385818 := by
    simpa [prefixWord, tailWord_1385818, baseEnd_1385818] using wordTrace_append hprefix tailTrace_1385818
  have hstable : (prefixWord ++ tailWord_1385818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385818).length < 2 ^ (prefixWord ++ tailWord_1385818).sum := by decide
  have hdescent : baseEnd_1385818 < baseStart_1385818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385851 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 6]
def baseStart_1385851 : Nat := 118140960795 + 1385851 * 2 ^ 59
def prefixEnd_1385851 : Nat := 4983230072969 + 3 ^ 40 * 1385851 * 2
def baseEnd_1385851 : Nat := 237202559504720861763031

theorem tailTrace_1385851 : CollatzResearch.WordTrace tailWord_1385851 prefixEnd_1385851 237202559504720861763031 := by
  unfold tailWord_1385851
  simp only [CollatzResearch.WordTrace]
  refine ⟨50546138502305986352493407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33697425668203990901662271 50546138502305986352493407)
  ·
    refine ⟨75819207753458979528740111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50546138502305986352493407 75819207753458979528740111)
    ·
      refine ⟨113728811630188469293110167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75819207753458979528740111 113728811630188469293110167)
      ·
        refine ⟨170593217445282703939665251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113728811630188469293110167 170593217445282703939665251)
        ·
          refine ⟨255889826167924055909497877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170593217445282703939665251 255889826167924055909497877)
          ·
            refine ⟨11994835601621440120757713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255889826167924055909497877 11994835601621440120757713)
            ·
              refine ⟨8996126701216080090568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11994835601621440120757713 8996126701216080090568285)
              ·
                refine ⟨3373547512956030033963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8996126701216080090568285 3373547512956030033963107)
                ·
                  refine ⟨5060321269434045050944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373547512956030033963107 5060321269434045050944661)
                  ·
                    refine ⟨237202559504720861763031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5060321269434045050944661 237202559504720861763031)
                    ·
                      rfl

theorem cell23_1385851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_1385851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385851 prefixEnd_1385851 := by exact prefixLift 1385851
  have htrace : WordTrace (prefixWord ++ tailWord_1385851) baseStart_1385851 baseEnd_1385851 := by
    simpa [prefixWord, tailWord_1385851, baseEnd_1385851] using wordTrace_append hprefix tailTrace_1385851
  have hstable : (prefixWord ++ tailWord_1385851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385851).length < 2 ^ (prefixWord ++ tailWord_1385851).sum := by decide
  have hdescent : baseEnd_1385851 < baseStart_1385851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385861 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_1385861 : Nat := 118140960795 + 1385861 * 2 ^ 59
def prefixEnd_1385861 : Nat := 4983230072969 + 3 ^ 40 * 1385861 * 2
def baseEnd_1385861 : Nat := 711612813320707546164047

theorem tailTrace_1385861 : CollatzResearch.WordTrace tailWord_1385861 prefixEnd_1385861 711612813320707546164047 := by
  unfold tailWord_1385861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50546503232269758060357437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33697668821513172040238291 50546503232269758060357437)
  ·
    refine ⟨18954938712101159272634039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50546503232269758060357437 18954938712101159272634039)
    ·
      refine ⟨28432408068151738908951059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18954938712101159272634039 28432408068151738908951059)
      ·
        refine ⟨42648612102227608363426589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28432408068151738908951059 42648612102227608363426589)
        ·
          refine ⟨15993229538335353136284971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42648612102227608363426589 15993229538335353136284971)
          ·
            refine ⟨23989844307503029704427457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15993229538335353136284971 23989844307503029704427457)
            ·
              refine ⟨17992383230627272278320593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23989844307503029704427457 17992383230627272278320593)
              ·
                refine ⟨13494287422970454208740445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17992383230627272278320593 13494287422970454208740445)
                ·
                  refine ⟨5060357783613920328277667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13494287422970454208740445 5060357783613920328277667)
                  ·
                    refine ⟨7590536675420880492416501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060357783613920328277667 7590536675420880492416501)
                    ·
                      refine ⟨711612813320707546164047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7590536675420880492416501 711612813320707546164047)
                      ·
                        rfl

theorem cell23_1385861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_1385861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385861 prefixEnd_1385861 := by exact prefixLift 1385861
  have htrace : WordTrace (prefixWord ++ tailWord_1385861) baseStart_1385861 baseEnd_1385861 := by
    simpa [prefixWord, tailWord_1385861, baseEnd_1385861] using wordTrace_append hprefix tailTrace_1385861
  have hstable : (prefixWord ++ tailWord_1385861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385861).length < 2 ^ (prefixWord ++ tailWord_1385861).sum := by decide
  have hdescent : baseEnd_1385861 < baseStart_1385861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385885 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1385885 : Nat := 118140960795 + 1385885 * 2 ^ 59
def prefixEnd_1385885 : Nat := 4983230072969 + 3 ^ 40 * 1385885 * 2
def baseEnd_1385885 : Nat := 237208378952138484087979

theorem tailTrace_1385885 : CollatzResearch.WordTrace tailWord_1385885 prefixEnd_1385885 237208378952138484087979 := by
  unfold tailWord_1385885
  simp only [CollatzResearch.WordTrace]
  refine ⟨50547378584182810159231109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33698252389455206772820739 50547378584182810159231109)
  ·
    refine ⟨9477633484534276904855833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50547378584182810159231109 9477633484534276904855833)
    ·
      refine ⟨7108225113400707678641875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9477633484534276904855833 7108225113400707678641875)
      ·
        refine ⟨10662337670101061517962813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108225113400707678641875 10662337670101061517962813)
        ·
          refine ⟨3998376626287898069236055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10662337670101061517962813 3998376626287898069236055)
          ·
            refine ⟨5997564939431847103854083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998376626287898069236055 5997564939431847103854083)
            ·
              refine ⟨8996347409147770655781125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997564939431847103854083 8996347409147770655781125)
              ·
                refine ⟨1686815139215206997958961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8996347409147770655781125 1686815139215206997958961)
                ·
                  refine ⟨1265111354411405248469221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686815139215206997958961 1265111354411405248469221)
                  ·
                    refine ⟨237208378952138484087979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265111354411405248469221 237208378952138484087979)
                    ·
                      rfl

theorem cell23_1385885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1385885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385885 prefixEnd_1385885 := by exact prefixLift 1385885
  have htrace : WordTrace (prefixWord ++ tailWord_1385885) baseStart_1385885 baseEnd_1385885 := by
    simpa [prefixWord, tailWord_1385885, baseEnd_1385885] using wordTrace_append hprefix tailTrace_1385885
  have hstable : (prefixWord ++ tailWord_1385885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385885).length < 2 ^ (prefixWord ++ tailWord_1385885).sum := by decide
  have hdescent : baseEnd_1385885 < baseStart_1385885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385886 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1385886 : Nat := 118140960795 + 1385886 * 2 ^ 59
def prefixEnd_1385886 : Nat := 4983230072969 + 3 ^ 40 * 1385886 * 2
def baseEnd_1385886 : Nat := 711625650337069948351433

theorem tailTrace_1385886 : CollatzResearch.WordTrace tailWord_1385886 prefixEnd_1385886 711625650337069948351433 := by
  unfold tailWord_1385886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318426882147398416252189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33698276704786124886678341 6318426882147398416252189)
  ·
    refine ⟨2369410080805274406094571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6318426882147398416252189 2369410080805274406094571)
    ·
      refine ⟨3554115121207911609141857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369410080805274406094571 3554115121207911609141857)
      ·
        refine ⟨2665586340905933706856393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3554115121207911609141857 2665586340905933706856393)
        ·
          refine ⟨1999189755679450280142295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665586340905933706856393 1999189755679450280142295)
          ·
            refine ⟨2998784633519175420213443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999189755679450280142295 2998784633519175420213443)
            ·
              refine ⟨4498176950278763130320165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998784633519175420213443 4498176950278763130320165)
              ·
                refine ⟨843408178177268086935031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4498176950278763130320165 843408178177268086935031)
                ·
                  refine ⟨1265112267265902130402547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843408178177268086935031 1265112267265902130402547)
                  ·
                    refine ⟨1897668400898853195603821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265112267265902130402547 1897668400898853195603821)
                    ·
                      refine ⟨711625650337069948351433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897668400898853195603821 711625650337069948351433)
                      ·
                        rfl

theorem cell23_1385886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1385886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385886 prefixEnd_1385886 := by exact prefixLift 1385886
  have htrace : WordTrace (prefixWord ++ tailWord_1385886) baseStart_1385886 baseEnd_1385886 := by
    simpa [prefixWord, tailWord_1385886, baseEnd_1385886] using wordTrace_append hprefix tailTrace_1385886
  have hstable : (prefixWord ++ tailWord_1385886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385886).length < 2 ^ (prefixWord ++ tailWord_1385886).sum := by decide
  have hdescent : baseEnd_1385886 < baseStart_1385886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385911 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 7]
def baseStart_1385911 : Nat := 118140960795 + 1385911 * 2 ^ 59
def prefixEnd_1385911 : Nat := 4983230072969 + 3 ^ 40 * 1385911 * 2
def baseEnd_1385911 : Nat := 237212829117810783512939

theorem tailTrace_1385911 : CollatzResearch.WordTrace tailWord_1385911 prefixEnd_1385911 237212829117810783512939 := by
  unfold tailWord_1385911
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548326882088616599677587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33698884588059077733118391 50548326882088616599677587)
  ·
    refine ⟨75822490323132924899516381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50548326882088616599677587 75822490323132924899516381)
    ·
      refine ⟨28433433871174846837318643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75822490323132924899516381 28433433871174846837318643)
      ·
        refine ⟨42650150806762270255977965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28433433871174846837318643 42650150806762270255977965)
        ·
          refine ⟨15993806552535851345991737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42650150806762270255977965 15993806552535851345991737)
          ·
            refine ⟨11995354914401888509493803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15993806552535851345991737 11995354914401888509493803)
            ·
              refine ⟨17993032371602832764240705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995354914401888509493803 17993032371602832764240705)
              ·
                refine ⟨13494774278702124573180529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17993032371602832764240705 13494774278702124573180529)
                ·
                  refine ⟨10121080709026593429885397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13494774278702124573180529 10121080709026593429885397)
                  ·
                    refine ⟨237212829117810783512939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10121080709026593429885397 237212829117810783512939)
                    ·
                      rfl

theorem cell23_1385911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_1385911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385911 prefixEnd_1385911 := by exact prefixLift 1385911
  have htrace : WordTrace (prefixWord ++ tailWord_1385911) baseStart_1385911 baseEnd_1385911 := by
    simpa [prefixWord, tailWord_1385911, baseEnd_1385911] using wordTrace_append hprefix tailTrace_1385911
  have hstable : (prefixWord ++ tailWord_1385911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385911).length < 2 ^ (prefixWord ++ tailWord_1385911).sum := by decide
  have hdescent : baseEnd_1385911 < baseStart_1385911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385959 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1385959 : Nat := 118140960795 + 1385959 * 2 ^ 59
def prefixEnd_1385959 : Nat := 4983230072969 + 3 ^ 40 * 1385959 * 2
def baseEnd_1385959 : Nat := 711663134424848162738597

theorem tailTrace_1385959 : CollatzResearch.WordTrace tailWord_1385959 prefixEnd_1385959 711663134424848162738597 := by
  unfold tailWord_1385959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50550077585914720797424931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33700051723943147198283287 50550077585914720797424931)
  ·
    refine ⟨75825116378872081196137397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50550077585914720797424931 75825116378872081196137397)
    ·
      refine ⟨7108604660519257612137881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75825116378872081196137397 7108604660519257612137881)
      ·
        refine ⟨5331453495389443209103411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7108604660519257612137881 5331453495389443209103411)
        ·
          refine ⟨7997180243084164813655117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331453495389443209103411 7997180243084164813655117)
          ·
            refine ⟨2998942591156561805120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7997180243084164813655117 2998942591156561805120669)
            ·
              refine ⟨1124603471683710676920251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2998942591156561805120669 1124603471683710676920251)
              ·
                refine ⟨1686905207525566015380377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124603471683710676920251 1686905207525566015380377)
                ·
                  refine ⟨1265178905644174511535283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686905207525566015380377 1265178905644174511535283)
                  ·
                    refine ⟨1897768358466261767302925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265178905644174511535283 1897768358466261767302925)
                    ·
                      refine ⟨711663134424848162738597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1897768358466261767302925 711663134424848162738597)
                      ·
                        rfl

theorem cell23_1385959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1385959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385959 prefixEnd_1385959 := by exact prefixLift 1385959
  have htrace : WordTrace (prefixWord ++ tailWord_1385959) baseStart_1385959 baseEnd_1385959 := by
    simpa [prefixWord, tailWord_1385959, baseEnd_1385959] using wordTrace_append hprefix tailTrace_1385959
  have hstable : (prefixWord ++ tailWord_1385959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385959).length < 2 ^ (prefixWord ++ tailWord_1385959).sum := by decide
  have hdescent : baseEnd_1385959 < baseStart_1385959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385971 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 9]
def baseStart_1385971 : Nat := 118140960795 + 1385971 * 2 ^ 59
def prefixEnd_1385971 : Nat := 4983230072969 + 3 ^ 40 * 1385971 * 2
def baseEnd_1385971 : Nat := 79074366243633568420949

theorem tailTrace_1385971 : CollatzResearch.WordTrace tailWord_1385971 prefixEnd_1385971 79074366243633568420949 := by
  unfold tailWord_1385971
  simp only [CollatzResearch.WordTrace]
  refine ⟨50550515261871246846861767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33700343507914164564574511 50550515261871246846861767)
  ·
    refine ⟨75825772892806870270292651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50550515261871246846861767 75825772892806870270292651)
    ·
      refine ⟨113738659339210305405438977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75825772892806870270292651 113738659339210305405438977)
      ·
        refine ⟨85303994504407729054079233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113738659339210305405438977 85303994504407729054079233)
        ·
          refine ⟨63977995878305796790559425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85303994504407729054079233 63977995878305796790559425)
          ·
            refine ⟨47983496908729347592919569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63977995878305796790559425 47983496908729347592919569)
            ·
              refine ⟨35987622681547010694689677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47983496908729347592919569 35987622681547010694689677)
              ·
                refine ⟨13495358505580129010508629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35987622681547010694689677 13495358505580129010508629)
                ·
                  refine ⟨79074366243633568420949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13495358505580129010508629 79074366243633568420949)
                  ·
                    rfl

theorem cell23_1385971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 9].length) (baseStart_1385971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385971 prefixEnd_1385971 := by exact prefixLift 1385971
  have htrace : WordTrace (prefixWord ++ tailWord_1385971) baseStart_1385971 baseEnd_1385971 := by
    simpa [prefixWord, tailWord_1385971, baseEnd_1385971] using wordTrace_append hprefix tailTrace_1385971
  have hstable : (prefixWord ++ tailWord_1385971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385971).length < 2 ^ (prefixWord ++ tailWord_1385971).sum := by decide
  have hdescent : baseEnd_1385971 < baseStart_1385971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1385985 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1385985 : Nat := 118140960795 + 1385985 * 2 ^ 59
def prefixEnd_1385985 : Nat := 4983230072969 + 3 ^ 40 * 1385985 * 2
def baseEnd_1385985 : Nat := 711676484921865061013477

theorem tailTrace_1385985 : CollatzResearch.WordTrace tailWord_1385985 prefixEnd_1385985 711676484921865061013477 := by
  unfold tailWord_1385985
  simp only [CollatzResearch.WordTrace]
  refine ⟨50551025883820527237871409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33700683922547018158580939 50551025883820527237871409)
  ·
    refine ⟨37913269412865395428403557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50551025883820527237871409 37913269412865395428403557)
    ·
      refine ⟨7108738014912261642825667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37913269412865395428403557 7108738014912261642825667)
      ·
        refine ⟨10663107022368392464238501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108738014912261642825667 10663107022368392464238501)
        ·
          refine ⟨1999332566694073587044719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10663107022368392464238501 1999332566694073587044719)
          ·
            refine ⟨2998998850041110380567079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999332566694073587044719 2998998850041110380567079)
            ·
              refine ⟨4498498275061665570850619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998998850041110380567079 4498498275061665570850619)
              ·
                refine ⟨6747747412592498356275929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4498498275061665570850619 6747747412592498356275929)
                ·
                  refine ⟨5060810559444373767206947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6747747412592498356275929 5060810559444373767206947)
                  ·
                    refine ⟨7591215839166560650810421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060810559444373767206947 7591215839166560650810421)
                    ·
                      refine ⟨711676484921865061013477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7591215839166560650810421 711676484921865061013477)
                      ·
                        rfl

theorem cell23_1385985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1385985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1385985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1385985 prefixEnd_1385985 := by exact prefixLift 1385985
  have htrace : WordTrace (prefixWord ++ tailWord_1385985) baseStart_1385985 baseEnd_1385985 := by
    simpa [prefixWord, tailWord_1385985, baseEnd_1385985] using wordTrace_append hprefix tailTrace_1385985
  have hstable : (prefixWord ++ tailWord_1385985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1385985).length < 2 ^ (prefixWord ++ tailWord_1385985).sum := by decide
  have hdescent : baseEnd_1385985 < baseStart_1385985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1385985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386005 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 7]
def baseStart_1386005 : Nat := 118140960795 + 1386005 * 2 ^ 59
def prefixEnd_1386005 : Nat := 4983230072969 + 3 ^ 40 * 1386005 * 2
def baseEnd_1386005 : Nat := 79076306059439442529265

theorem tailTrace_1386005 : CollatzResearch.WordTrace tailWord_1386005 prefixEnd_1386005 79076306059439442529265 := by
  unfold tailWord_1386005
  simp only [CollatzResearch.WordTrace]
  refine ⟨50551755343748070653599469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33701170229165380435732979 50551755343748070653599469)
  ·
    refine ⟨18956908253905526495099801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50551755343748070653599469 18956908253905526495099801)
    ·
      refine ⟨14217681190429144871324851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18956908253905526495099801 14217681190429144871324851)
      ·
        refine ⟨21326521785643717306987277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217681190429144871324851 21326521785643717306987277)
        ·
          refine ⟨7997445669616393990120229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21326521785643717306987277 7997445669616393990120229)
          ·
            refine ⟨1499521063053073873147543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7997445669616393990120229 1499521063053073873147543)
            ·
              refine ⟨2249281594579610809721315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499521063053073873147543 2249281594579610809721315)
              ·
                refine ⟨3373922391869416214581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249281594579610809721315 3373922391869416214581973)
                ·
                  refine ⟨79076306059439442529265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3373922391869416214581973 79076306059439442529265)
                  ·
                    rfl

theorem cell23_1386005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_1386005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386005 prefixEnd_1386005 := by exact prefixLift 1386005
  have htrace : WordTrace (prefixWord ++ tailWord_1386005) baseStart_1386005 baseEnd_1386005 := by
    simpa [prefixWord, tailWord_1386005, baseEnd_1386005] using wordTrace_append hprefix tailTrace_1386005
  have hstable : (prefixWord ++ tailWord_1386005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386005).length < 2 ^ (prefixWord ++ tailWord_1386005).sum := by decide
  have hdescent : baseEnd_1386005 < baseStart_1386005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386016 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1386016 : Nat := 118140960795 + 1386016 * 2 ^ 59
def prefixEnd_1386016 : Nat := 4983230072969 + 3 ^ 40 * 1386016 * 2
def baseEnd_1386016 : Nat := 711692402822154439725835

theorem tailTrace_1386016 : CollatzResearch.WordTrace tailWord_1386016 prefixEnd_1386016 711692402822154439725835 := by
  unfold tailWord_1386016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25276078273354109766124951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33701437697805479688166601 25276078273354109766124951)
  ·
    refine ⟨37914117410031164649187427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25276078273354109766124951 37914117410031164649187427)
    ·
      refine ⟨56871176115046746973781141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37914117410031164649187427 56871176115046746973781141)
      ·
        refine ⟨2665836380392816264395991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56871176115046746973781141 2665836380392816264395991)
        ·
          refine ⟨3998754570589224396593987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665836380392816264395991 3998754570589224396593987)
          ·
            refine ⟨5998131855883836594890981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998754570589224396593987 5998131855883836594890981)
            ·
              refine ⟨1124649722978219361542059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5998131855883836594890981 1124649722978219361542059)
              ·
                refine ⟨1686974584467329042313089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124649722978219361542059 1686974584467329042313089)
                ·
                  refine ⟨1265230938350496781734817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1686974584467329042313089 1265230938350496781734817)
                  ·
                    refine ⟨948923203762872586301113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1265230938350496781734817 948923203762872586301113)
                    ·
                      refine ⟨711692402822154439725835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 948923203762872586301113 711692402822154439725835)
                      ·
                        rfl

theorem cell23_1386016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1386016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386016 prefixEnd_1386016 := by exact prefixLift 1386016
  have htrace : WordTrace (prefixWord ++ tailWord_1386016) baseStart_1386016 baseEnd_1386016 := by
    simpa [prefixWord, tailWord_1386016, baseEnd_1386016] using wordTrace_append hprefix tailTrace_1386016
  have hstable : (prefixWord ++ tailWord_1386016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386016).length < 2 ^ (prefixWord ++ tailWord_1386016).sum := by decide
  have hdescent : baseEnd_1386016 < baseStart_1386016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386018 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1386018 : Nat := 118140960795 + 1386018 * 2 ^ 59
def prefixEnd_1386018 : Nat := 4983230072969 + 3 ^ 40 * 1386018 * 2
def baseEnd_1386018 : Nat := 237231143261154477300275

theorem tailTrace_1386018 : CollatzResearch.WordTrace tailWord_1386018 prefixEnd_1386018 237231143261154477300275 := by
  unfold tailWord_1386018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638057373175243468455677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33701486328467315915881805 12638057373175243468455677)
  ·
    refine ⟨4739271514940716300670879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12638057373175243468455677 4739271514940716300670879)
    ·
      refine ⟨7108907272411074451006319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739271514940716300670879 7108907272411074451006319)
      ·
        refine ⟨10663360908616611676509479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108907272411074451006319 10663360908616611676509479)
        ·
          refine ⟨15995041362924917514764219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10663360908616611676509479 15995041362924917514764219)
          ·
            refine ⟨23992562044387376272146329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995041362924917514764219 23992562044387376272146329)
            ·
              refine ⟨17994421533290532204109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23992562044387376272146329 17994421533290532204109747)
              ·
                refine ⟨26991632299935798306164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17994421533290532204109747 26991632299935798306164621)
                ·
                  refine ⟨10121862112475924364811733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26991632299935798306164621 10121862112475924364811733)
                  ·
                    refine ⟨237231143261154477300275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10121862112475924364811733 237231143261154477300275)
                    ·
                      rfl

theorem cell23_1386018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1386018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386018 prefixEnd_1386018 := by exact prefixLift 1386018
  have htrace : WordTrace (prefixWord ++ tailWord_1386018) baseStart_1386018 baseEnd_1386018 := by
    simpa [prefixWord, tailWord_1386018, baseEnd_1386018] using wordTrace_append hprefix tailTrace_1386018
  have hstable : (prefixWord ++ tailWord_1386018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386018).length < 2 ^ (prefixWord ++ tailWord_1386018).sum := by decide
  have hdescent : baseEnd_1386018 < baseStart_1386018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386035 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 2, 5]
def baseStart_1386035 : Nat := 118140960795 + 1386035 * 2 ^ 59
def prefixEnd_1386035 : Nat := 4983230072969 + 3 ^ 40 * 1386035 * 2
def baseEnd_1386035 : Nat := 237234052984863288462749

theorem tailTrace_1386035 : CollatzResearch.WordTrace tailWord_1386035 prefixEnd_1386035 237234052984863288462749 := by
  unfold tailWord_1386035
  simp only [CollatzResearch.WordTrace]
  refine ⟨50552849533639385777191559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33701899689092923851461039 50552849533639385777191559)
  ·
    refine ⟨75829274300459078665787339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50552849533639385777191559 75829274300459078665787339)
    ·
      refine ⟨113743911450688617998681009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75829274300459078665787339 113743911450688617998681009)
      ·
        refine ⟨85307933588016463499010757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113743911450688617998681009 85307933588016463499010757)
        ·
          refine ⟨15995237547753086906064517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85307933588016463499010757 15995237547753086906064517)
          ·
            refine ⟨2999107040203703794887097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15995237547753086906064517 2999107040203703794887097)
            ·
              refine ⟨2249330280152777846165323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999107040203703794887097 2249330280152777846165323)
              ·
                refine ⟨3373995420229166769247985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249330280152777846165323 3373995420229166769247985)
                ·
                  refine ⟨2530496565171875076935989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3373995420229166769247985 2530496565171875076935989)
                  ·
                    refine ⟨237234052984863288462749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2530496565171875076935989 237234052984863288462749)
                    ·
                      rfl

theorem cell23_1386035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 5].length) (baseStart_1386035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386035 prefixEnd_1386035 := by exact prefixLift 1386035
  have htrace : WordTrace (prefixWord ++ tailWord_1386035) baseStart_1386035 baseEnd_1386035 := by
    simpa [prefixWord, tailWord_1386035, baseEnd_1386035] using wordTrace_append hprefix tailTrace_1386035
  have hstable : (prefixWord ++ tailWord_1386035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386035).length < 2 ^ (prefixWord ++ tailWord_1386035).sum := by decide
  have hdescent : baseEnd_1386035 < baseStart_1386035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386058 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1386058 : Nat := 118140960795 + 1386058 * 2 ^ 59
def prefixEnd_1386058 : Nat := 4983230072969 + 3 ^ 40 * 1386058 * 2
def baseEnd_1386058 : Nat := 711713969009643275400641

theorem tailTrace_1386058 : CollatzResearch.WordTrace tailWord_1386058 prefixEnd_1386058 711713969009643275400641 := by
  unfold tailWord_1386058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638422103139015176319707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33702458941704040470185885 12638422103139015176319707)
  ·
    refine ⟨18957633154708522764479561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12638422103139015176319707 18957633154708522764479561)
    ·
      refine ⟨14218224866031392073359671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18957633154708522764479561 14218224866031392073359671)
      ·
        refine ⟨21327337299047088110039507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14218224866031392073359671 21327337299047088110039507)
        ·
          refine ⟨31991005948570632165059261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21327337299047088110039507 31991005948570632165059261)
          ·
            refine ⟨11996627230713987061897223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31991005948570632165059261 11996627230713987061897223)
            ·
              refine ⟨17994940846070980592845835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11996627230713987061897223 17994940846070980592845835)
              ·
                refine ⟨26992411269106470889268753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17994940846070980592845835 26992411269106470889268753)
                ·
                  refine ⟨20244308451829853166951565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26992411269106470889268753 20244308451829853166951565)
                  ·
                    refine ⟨7591615669436194937606837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20244308451829853166951565 7591615669436194937606837)
                    ·
                      refine ⟨711713969009643275400641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7591615669436194937606837 711713969009643275400641)
                      ·
                        rfl

theorem cell23_1386058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1386058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386058 prefixEnd_1386058 := by exact prefixLift 1386058
  have htrace : WordTrace (prefixWord ++ tailWord_1386058) baseStart_1386058 baseEnd_1386058 := by
    simpa [prefixWord, tailWord_1386058, baseEnd_1386058] using wordTrace_append hprefix tailTrace_1386058
  have hstable : (prefixWord ++ tailWord_1386058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386058).length < 2 ^ (prefixWord ++ tailWord_1386058).sum := by decide
  have hdescent : baseEnd_1386058 < baseStart_1386058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386065 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_1386065 : Nat := 118140960795 + 1386065 * 2 ^ 59
def prefixEnd_1386065 : Nat := 4983230072969 + 3 ^ 40 * 1386065 * 2
def baseEnd_1386065 : Nat := 237239187791408249337703

theorem tailTrace_1386065 : CollatzResearch.WordTrace tailWord_1386065 prefixEnd_1386065 237239187791408249337703 := by
  unfold tailWord_1386065
  simp only [CollatzResearch.WordTrace]
  refine ⟨50553943723530700900783649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33702629149020467267189099 50553943723530700900783649)
  ·
    refine ⟨37915457792648025675587737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50553943723530700900783649 37915457792648025675587737)
    ·
      refine ⟨28436593344486019256690803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37915457792648025675587737 28436593344486019256690803)
      ·
        refine ⟨42654890016729028885036205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28436593344486019256690803 42654890016729028885036205)
        ·
          refine ⟨15995583756273385831888577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42654890016729028885036205 15995583756273385831888577)
          ·
            refine ⟨11996687817205039373916433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15995583756273385831888577 11996687817205039373916433)
            ·
              refine ⟨8997515862903779530437325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11996687817205039373916433 8997515862903779530437325)
              ·
                refine ⟨3374068448588917323913997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8997515862903779530437325 3374068448588917323913997)
                ·
                  refine ⟨1265275668220843996467749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3374068448588917323913997 1265275668220843996467749)
                  ·
                    refine ⟨237239187791408249337703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265275668220843996467749 237239187791408249337703)
                    ·
                      rfl

theorem cell23_1386065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_1386065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386065 prefixEnd_1386065 := by exact prefixLift 1386065
  have htrace : WordTrace (prefixWord ++ tailWord_1386065) baseStart_1386065 baseEnd_1386065 := by
    simpa [prefixWord, tailWord_1386065, baseEnd_1386065] using wordTrace_append hprefix tailTrace_1386065
  have hstable : (prefixWord ++ tailWord_1386065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386065).length < 2 ^ (prefixWord ++ tailWord_1386065).sum := by decide
  have hdescent : baseEnd_1386065 < baseStart_1386065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386162 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_1386162 : Nat := 118140960795 + 1386162 * 2 ^ 59
def prefixEnd_1386162 : Nat := 4983230072969 + 3 ^ 40 * 1386162 * 2
def baseEnd_1386162 : Nat := 711767370997710868500163

theorem tailTrace_1386162 : CollatzResearch.WordTrace tailWord_1386162 prefixEnd_1386162 711767370997710868500163 := by
  unfold tailWord_1386162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639370401044821616766185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33704987736119524311376493 12639370401044821616766185)
  ·
    refine ⟨9479527800783616212574639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12639370401044821616766185 9479527800783616212574639)
    ·
      refine ⟨14219291701175424318861959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479527800783616212574639 14219291701175424318861959)
      ·
        refine ⟨21328937551763136478292939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14219291701175424318861959 21328937551763136478292939)
        ·
          refine ⟨31993406327644704717439409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21328937551763136478292939 31993406327644704717439409)
          ·
            refine ⟨23995054745733528538079557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31993406327644704717439409 23995054745733528538079557)
            ·
              refine ⟨4499072764825036600889917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23995054745733528538079557 4499072764825036600889917)
              ·
                refine ⟨1687152286809388725333719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4499072764825036600889917 1687152286809388725333719)
                ·
                  refine ⟨2530728430214083088000579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687152286809388725333719 2530728430214083088000579)
                  ·
                    refine ⟨3796092645321124632000869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530728430214083088000579 3796092645321124632000869)
                    ·
                      refine ⟨711767370997710868500163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3796092645321124632000869 711767370997710868500163)
                      ·
                        rfl

theorem cell23_1386162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_1386162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386162 prefixEnd_1386162 := by exact prefixLift 1386162
  have htrace : WordTrace (prefixWord ++ tailWord_1386162) baseStart_1386162 baseEnd_1386162 := by
    simpa [prefixWord, tailWord_1386162, baseEnd_1386162] using wordTrace_append hprefix tailTrace_1386162
  have hstable : (prefixWord ++ tailWord_1386162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386162).length < 2 ^ (prefixWord ++ tailWord_1386162).sum := by decide
  have hdescent : baseEnd_1386162 < baseStart_1386162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386166 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1386166 : Nat := 118140960795 + 1386166 * 2 ^ 59
def prefixEnd_1386166 : Nat := 4983230072969 + 3 ^ 40 * 1386166 * 2
def baseEnd_1386166 : Nat := 711769424920328852850145

theorem tailTrace_1386166 : CollatzResearch.WordTrace tailWord_1386166 prefixEnd_1386166 711769424920328852850145 := by
  unfold tailWord_1386166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159851718510299696888147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33705084997443196766806901 3159851718510299696888147)
  ·
    refine ⟨4739777577765449545332221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159851718510299696888147 4739777577765449545332221)
    ·
      refine ⟨1777416591662043579499583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4739777577765449545332221 1777416591662043579499583)
      ·
        refine ⟨2666124887493065369249375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777416591662043579499583 2666124887493065369249375)
        ·
          refine ⟨3999187331239598053874063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666124887493065369249375 3999187331239598053874063)
          ·
            refine ⟨5998780996859397080811095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999187331239598053874063 5998780996859397080811095)
            ·
              refine ⟨8998171495289095621216643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998780996859397080811095 8998171495289095621216643)
              ·
                refine ⟨13497257242933643431824965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998171495289095621216643 13497257242933643431824965)
                ·
                  refine ⟨2530735733050058143467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13497257242933643431824965 2530735733050058143467181)
                  ·
                    refine ⟨949025899893771803800193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530735733050058143467181 949025899893771803800193)
                    ·
                      refine ⟨711769424920328852850145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949025899893771803800193 711769424920328852850145)
                      ·
                        rfl

theorem cell23_1386166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1386166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386166 prefixEnd_1386166 := by exact prefixLift 1386166
  have htrace : WordTrace (prefixWord ++ tailWord_1386166) baseStart_1386166 baseEnd_1386166 := by
    simpa [prefixWord, tailWord_1386166, baseEnd_1386166] using wordTrace_append hprefix tailTrace_1386166
  have hstable : (prefixWord ++ tailWord_1386166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386166).length < 2 ^ (prefixWord ++ tailWord_1386166).sum := by decide
  have hdescent : baseEnd_1386166 < baseStart_1386166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386172 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1386172 : Nat := 118140960795 + 1386172 * 2 ^ 59
def prefixEnd_1386172 : Nat := 4983230072969 + 3 ^ 40 * 1386172 * 2
def baseEnd_1386172 : Nat := 237257501934751943125039

theorem tailTrace_1386172 : CollatzResearch.WordTrace tailWord_1386172 prefixEnd_1386172 237257501934751943125039 := by
  unfold tailWord_1386172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25278923167071529087464385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33705230889428705449952513 25278923167071529087464385)
  ·
    refine ⟨18959192375303646815598289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25278923167071529087464385 18959192375303646815598289)
    ·
      refine ⟨14219394281477735111698717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18959192375303646815598289 14219394281477735111698717)
      ·
        refine ⟨5332272855554150666887019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14219394281477735111698717 5332272855554150666887019)
        ·
          refine ⟨7998409283331226000330529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332272855554150666887019 7998409283331226000330529)
          ·
            refine ⟨5998806962498419500247897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7998409283331226000330529 5998806962498419500247897)
            ·
              refine ⟨4499105221873814625185923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998806962498419500247897 4499105221873814625185923)
              ·
                refine ⟨6748657832810721937778885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499105221873814625185923 6748657832810721937778885)
                ·
                  refine ⟨1265373343652010363333541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6748657832810721937778885 1265373343652010363333541)
                  ·
                    refine ⟨237257501934751943125039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265373343652010363333541 237257501934751943125039)
                    ·
                      rfl

theorem cell23_1386172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1386172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386172 prefixEnd_1386172 := by exact prefixLift 1386172
  have htrace : WordTrace (prefixWord ++ tailWord_1386172) baseStart_1386172 baseEnd_1386172 := by
    simpa [prefixWord, tailWord_1386172, baseEnd_1386172] using wordTrace_append hprefix tailTrace_1386172
  have hstable : (prefixWord ++ tailWord_1386172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386172).length < 2 ^ (prefixWord ++ tailWord_1386172).sum := by decide
  have hdescent : baseEnd_1386172 < baseStart_1386172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386196 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1386196 : Nat := 118140960795 + 1386196 * 2 ^ 59
def prefixEnd_1386196 : Nat := 4983230072969 + 3 ^ 40 * 1386196 * 2
def baseEnd_1386196 : Nat := 711784829339963735475007

theorem tailTrace_1386196 : CollatzResearch.WordTrace tailWord_1386196 prefixEnd_1386196 711784829339963735475007 := by
  unfold tailWord_1386196
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279360843028055136901221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33705814457370740182534961 25279360843028055136901221)
  ·
    refine ⟨4739880158067760338168979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25279360843028055136901221 4739880158067760338168979)
    ·
      refine ⟨7109820237101640507253469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739880158067760338168979 7109820237101640507253469)
      ·
        refine ⟨2666182588913115190220051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7109820237101640507253469 2666182588913115190220051)
        ·
          refine ⟨3999273883369672785330077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666182588913115190220051 3999273883369672785330077)
          ·
            refine ⟨1499727706263627294498779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3999273883369672785330077 1499727706263627294498779)
            ·
              refine ⟨2249591559395440941748169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499727706263627294498779 2249591559395440941748169)
              ·
                refine ⟨1687193669546580706311127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249591559395440941748169 1687193669546580706311127)
                ·
                  refine ⟨2530790504319871059466691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687193669546580706311127 2530790504319871059466691)
                  ·
                    refine ⟨3796185756479806589200037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2530790504319871059466691 3796185756479806589200037)
                    ·
                      refine ⟨711784829339963735475007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3796185756479806589200037 711784829339963735475007)
                      ·
                        rfl

theorem cell23_1386196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1386196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386196 prefixEnd_1386196 := by exact prefixLift 1386196
  have htrace : WordTrace (prefixWord ++ tailWord_1386196) baseStart_1386196 baseEnd_1386196 := by
    simpa [prefixWord, tailWord_1386196, baseEnd_1386196] using wordTrace_append hprefix tailTrace_1386196
  have hstable : (prefixWord ++ tailWord_1386196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386196).length < 2 ^ (prefixWord ++ tailWord_1386196).sum := by decide
  have hdescent : baseEnd_1386196 < baseStart_1386196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386212 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_1386212 : Nat := 118140960795 + 1386212 * 2 ^ 59
def prefixEnd_1386212 : Nat := 4983230072969 + 3 ^ 40 * 1386212 * 2
def baseEnd_1386212 : Nat := 711793045030435672874933

theorem tailTrace_1386212 : CollatzResearch.WordTrace tailWord_1386212 prefixEnd_1386212 711793045030435672874933 := by
  unfold tailWord_1386212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279652626999072503192445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33706203502665430004256593 25279652626999072503192445)
  ·
    refine ⟨9479869735124652188697167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25279652626999072503192445 9479869735124652188697167)
    ·
      refine ⟨14219804602686978283045751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479869735124652188697167 14219804602686978283045751)
      ·
        refine ⟨21329706904030467424568627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14219804602686978283045751 21329706904030467424568627)
        ·
          refine ⟨31994560356045701136852941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21329706904030467424568627 31994560356045701136852941)
          ·
            refine ⟨11997960133517137926319853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31994560356045701136852941 11997960133517137926319853)
            ·
              refine ⟨4499235050068926722369945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11997960133517137926319853 4499235050068926722369945)
              ·
                refine ⟨3374426287551695041777459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499235050068926722369945 3374426287551695041777459)
                ·
                  refine ⟨5061639431327542562666189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374426287551695041777459 5061639431327542562666189)
                  ·
                    refine ⟨1898114786747828460999821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5061639431327542562666189 1898114786747828460999821)
                    ·
                      refine ⟨711793045030435672874933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898114786747828460999821 711793045030435672874933)
                      ·
                        rfl

theorem cell23_1386212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_1386212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386212 prefixEnd_1386212 := by exact prefixLift 1386212
  have htrace : WordTrace (prefixWord ++ tailWord_1386212) baseStart_1386212 baseEnd_1386212 := by
    simpa [prefixWord, tailWord_1386212, baseEnd_1386212] using wordTrace_append hprefix tailTrace_1386212
  have hstable : (prefixWord ++ tailWord_1386212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386212).length < 2 ^ (prefixWord ++ tailWord_1386212).sum := by decide
  have hdescent : baseEnd_1386212 < baseStart_1386212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386216 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1386216 : Nat := 118140960795 + 1386216 * 2 ^ 59
def prefixEnd_1386216 : Nat := 4983230072969 + 3 ^ 40 * 1386216 * 2
def baseEnd_1386216 : Nat := 711795098953053657224915

theorem tailTrace_1386216 : CollatzResearch.WordTrace tailWord_1386216 prefixEnd_1386216 711795098953053657224915 := by
  unfold tailWord_1386216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279725572991826844765251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33706300763989102459687001 25279725572991826844765251)
  ·
    refine ⟨37919588359487740267147877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25279725572991826844765251 37919588359487740267147877)
    ·
      refine ⟨7109922817403951300090227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37919588359487740267147877 7109922817403951300090227)
      ·
        refine ⟨10664884226105926950135341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7109922817403951300090227 10664884226105926950135341)
        ·
          refine ⟨3999331584789722606300753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10664884226105926950135341 3999331584789722606300753)
          ·
            refine ⟨2999498688592291954725565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999331584789722606300753 2999498688592291954725565)
            ·
              refine ⟨1124812008222109483022087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2999498688592291954725565 1124812008222109483022087)
              ·
                refine ⟨1687218012333164224533131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124812008222109483022087 1687218012333164224533131)
                ·
                  refine ⟨2530827018499746336799697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687218012333164224533131 2530827018499746336799697)
                  ·
                    refine ⟨1898120263874809752599773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2530827018499746336799697 1898120263874809752599773)
                    ·
                      refine ⟨711795098953053657224915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898120263874809752599773 711795098953053657224915)
                      ·
                        rfl

theorem cell23_1386216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1386216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386216 prefixEnd_1386216 := by exact prefixLift 1386216
  have htrace : WordTrace (prefixWord ++ tailWord_1386216) baseStart_1386216 baseEnd_1386216 := by
    simpa [prefixWord, tailWord_1386216, baseEnd_1386216] using wordTrace_append hprefix tailTrace_1386216
  have hstable : (prefixWord ++ tailWord_1386216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386216).length < 2 ^ (prefixWord ++ tailWord_1386216).sum := by decide
  have hdescent : baseEnd_1386216 < baseStart_1386216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386230 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1386230 : Nat := 118140960795 + 1386230 * 2 ^ 59
def prefixEnd_1386230 : Nat := 4983230072969 + 3 ^ 40 * 1386230 * 2
def baseEnd_1386230 : Nat := 711802287682216602449851

theorem tailTrace_1386230 : CollatzResearch.WordTrace tailWord_1386230 prefixEnd_1386230 711802287682216602449851 := by
  unfold tailWord_1386230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159997610495808380033759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33706641178621956053693429 3159997610495808380033759)
  ·
    refine ⟨4739996415743712570050639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159997610495808380033759 4739996415743712570050639)
    ·
      refine ⟨7109994623615568855075959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739996415743712570050639 7109994623615568855075959)
      ·
        refine ⟨10664991935423353282613939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7109994623615568855075959 10664991935423353282613939)
        ·
          refine ⟨15997487903135029923920909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10664991935423353282613939 15997487903135029923920909)
          ·
            refine ⟨5999057963675636221470341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15997487903135029923920909 5999057963675636221470341)
            ·
              refine ⟨1124823368189181791525689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5999057963675636221470341 1124823368189181791525689)
              ·
                refine ⟨843617526141886343644267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124823368189181791525689 843617526141886343644267)
                ·
                  refine ⟨1265426289212829515466401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843617526141886343644267 1265426289212829515466401)
                  ·
                    refine ⟨949069716909622136599801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1265426289212829515466401 949069716909622136599801)
                    ·
                      refine ⟨711802287682216602449851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949069716909622136599801 711802287682216602449851)
                      ·
                        rfl

theorem cell23_1386230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1386230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386230 prefixEnd_1386230 := by exact prefixLift 1386230
  have htrace : WordTrace (prefixWord ++ tailWord_1386230) baseStart_1386230 baseEnd_1386230 := by
    simpa [prefixWord, tailWord_1386230, baseEnd_1386230] using wordTrace_append hprefix tailTrace_1386230
  have hstable : (prefixWord ++ tailWord_1386230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386230).length < 2 ^ (prefixWord ++ tailWord_1386230).sum := by decide
  have hdescent : baseEnd_1386230 < baseStart_1386230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386255 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_1386255 : Nat := 118140960795 + 1386255 * 2 ^ 59
def prefixEnd_1386255 : Nat := 4983230072969 + 3 ^ 40 * 1386255 * 2
def baseEnd_1386255 : Nat := 711815124698579004637235

theorem tailTrace_1386255 : CollatzResearch.WordTrace tailWord_1386255 prefixEnd_1386255 711815124698579004637235 := by
  unfold tailWord_1386255
  simp only [CollatzResearch.WordTrace]
  refine ⟨50560873592842363350200219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33707249061894908900133479 50560873592842363350200219)
  ·
    refine ⟨75841310389263545025300329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50560873592842363350200219 75841310389263545025300329)
    ·
      refine ⟨56880982791947658768975247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75841310389263545025300329 56880982791947658768975247)
      ·
        refine ⟨85321474187921488153462871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56880982791947658768975247 85321474187921488153462871)
        ·
          refine ⟨127982211281882232230194307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85321474187921488153462871 127982211281882232230194307)
          ·
            refine ⟨191973316922823348345291461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127982211281882232230194307 191973316922823348345291461)
            ·
              refine ⟨35994996923029377814742149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191973316922823348345291461 35994996923029377814742149)
              ·
                refine ⟨6749061923068008340264153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35994996923029377814742149 6749061923068008340264153)
                ·
                  refine ⟨5061796442301006255198115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749061923068008340264153 5061796442301006255198115)
                  ·
                    refine ⟨7592694663451509382797173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061796442301006255198115 7592694663451509382797173)
                    ·
                      refine ⟨711815124698579004637235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7592694663451509382797173 711815124698579004637235)
                      ·
                        rfl

theorem cell23_1386255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_1386255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386255 prefixEnd_1386255 := by exact prefixLift 1386255
  have htrace : WordTrace (prefixWord ++ tailWord_1386255) baseStart_1386255 baseEnd_1386255 := by
    simpa [prefixWord, tailWord_1386255, baseEnd_1386255] using wordTrace_append hprefix tailTrace_1386255
  have hstable : (prefixWord ++ tailWord_1386255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386255).length < 2 ^ (prefixWord ++ tailWord_1386255).sum := by decide
  have hdescent : baseEnd_1386255 < baseStart_1386255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386273 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1386273 : Nat := 118140960795 + 1386273 * 2 ^ 59
def prefixEnd_1386273 : Nat := 4983230072969 + 3 ^ 40 * 1386273 * 2
def baseEnd_1386273 : Nat := 711824367350359934212153

theorem tailTrace_1386273 : CollatzResearch.WordTrace tailWord_1386273 prefixEnd_1386273 711824367350359934212153 := by
  unfold tailWord_1386273
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561530106777152424355473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33707686737851434949570315 50561530106777152424355473)
  ·
    refine ⟨37921147580082864318266605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50561530106777152424355473 37921147580082864318266605)
    ·
      refine ⟨14220430342531074119349977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37921147580082864318266605 14220430342531074119349977)
      ·
        refine ⟨10665322756898305589512483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14220430342531074119349977 10665322756898305589512483)
        ·
          refine ⟨15997984135347458384268725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665322756898305589512483 15997984135347458384268725)
          ·
            refine ⟨1499811012688824223525193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15997984135347458384268725 1499811012688824223525193)
            ·
              refine ⟨1124858259516618167643895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499811012688824223525193 1124858259516618167643895)
              ·
                refine ⟨1687287389274927251465843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124858259516618167643895 1687287389274927251465843)
                ·
                  refine ⟨2530931083912390877198765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687287389274927251465843 2530931083912390877198765)
                  ·
                    refine ⟨949099156467146578949537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530931083912390877198765 949099156467146578949537)
                    ·
                      refine ⟨711824367350359934212153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949099156467146578949537 711824367350359934212153)
                      ·
                        rfl

theorem cell23_1386273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1386273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386273 prefixEnd_1386273 := by exact prefixLift 1386273
  have htrace : WordTrace (prefixWord ++ tailWord_1386273) baseStart_1386273 baseEnd_1386273 := by
    simpa [prefixWord, tailWord_1386273, baseEnd_1386273] using wordTrace_append hprefix tailTrace_1386273
  have hstable : (prefixWord ++ tailWord_1386273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386273).length < 2 ^ (prefixWord ++ tailWord_1386273).sum := by decide
  have hdescent : baseEnd_1386273 < baseStart_1386273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386303 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 4, 2]
def baseStart_1386303 : Nat := 118140960795 + 1386303 * 2 ^ 59
def prefixEnd_1386303 : Nat := 4983230072969 + 3 ^ 40 * 1386303 * 2
def baseEnd_1386303 : Nat := 711839771769994816837015

theorem tailTrace_1386303 : CollatzResearch.WordTrace tailWord_1386303 prefixEnd_1386303 711839771769994816837015 := by
  unfold tailWord_1386303
  simp only [CollatzResearch.WordTrace]
  refine ⟨50562624296668467547947563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33708416197778978365298375 50562624296668467547947563)
  ·
    refine ⟨75843936445002701321921345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50562624296668467547947563 75843936445002701321921345)
    ·
      refine ⟨56882952333752025991441009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75843936445002701321921345 56882952333752025991441009)
      ·
        refine ⟨42662214250314019493580757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56882952333752025991441009 42662214250314019493580757)
        ·
          refine ⟨999895646491734831880799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42662214250314019493580757 999895646491734831880799)
          ·
            refine ⟨1499843469737602247821199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999895646491734831880799 1499843469737602247821199)
            ·
              refine ⟨2249765204606403371731799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499843469737602247821199 2249765204606403371731799)
              ·
                refine ⟨3374647806909605057597699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249765204606403371731799 3374647806909605057597699)
                ·
                  refine ⟨5061971710364407586396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374647806909605057597699 5061971710364407586396549)
                  ·
                    refine ⟨949119695693326422449353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061971710364407586396549 949119695693326422449353)
                    ·
                      refine ⟨711839771769994816837015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949119695693326422449353 711839771769994816837015)
                      ·
                        rfl

theorem cell23_1386303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_1386303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386303 prefixEnd_1386303 := by exact prefixLift 1386303
  have htrace : WordTrace (prefixWord ++ tailWord_1386303) baseStart_1386303 baseEnd_1386303 := by
    simpa [prefixWord, tailWord_1386303, baseEnd_1386303] using wordTrace_append hprefix tailTrace_1386303
  have hstable : (prefixWord ++ tailWord_1386303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386303).length < 2 ^ (prefixWord ++ tailWord_1386303).sum := by decide
  have hdescent : baseEnd_1386303 < baseStart_1386303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386322 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1386322 : Nat := 118140960795 + 1386322 * 2 ^ 59
def prefixEnd_1386322 : Nat := 4983230072969 + 3 ^ 40 * 1386322 * 2
def baseEnd_1386322 : Nat := 237283175967476747499809

theorem tailTrace_1386322 : CollatzResearch.WordTrace tailWord_1386322 prefixEnd_1386322 237283175967476747499809 := by
  unfold tailWord_1386322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12640829320899908448222305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33708878189066422528592813 12640829320899908448222305)
  ·
    refine ⟨9480621990674931336166729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12640829320899908448222305 9480621990674931336166729)
    ·
      refine ⟨7110466493006198502125047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9480621990674931336166729 7110466493006198502125047)
      ·
        refine ⟨10665699739509297753187571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110466493006198502125047 10665699739509297753187571)
        ·
          refine ⟨15998549609263946629781357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665699739509297753187571 15998549609263946629781357)
          ·
            refine ⟨5999456103473979986168009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15998549609263946629781357 5999456103473979986168009)
            ·
              refine ⟨4499592077605484989626007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999456103473979986168009 4499592077605484989626007)
              ·
                refine ⟨6749388116408227484439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499592077605484989626007 6749388116408227484439011)
                ·
                  refine ⟨10124082174612341226658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749388116408227484439011 10124082174612341226658517)
                  ·
                    refine ⟨237283175967476747499809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10124082174612341226658517 237283175967476747499809)
                    ·
                      rfl

theorem cell23_1386322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1386322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386322 prefixEnd_1386322 := by exact prefixLift 1386322
  have htrace : WordTrace (prefixWord ++ tailWord_1386322) baseStart_1386322 baseEnd_1386322 := by
    simpa [prefixWord, tailWord_1386322, baseEnd_1386322] using wordTrace_append hprefix tailTrace_1386322
  have hstable : (prefixWord ++ tailWord_1386322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386322).length < 2 ^ (prefixWord ++ tailWord_1386322).sum := by decide
  have hdescent : baseEnd_1386322 < baseStart_1386322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386339 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 2, 5]
def baseStart_1386339 : Nat := 118140960795 + 1386339 * 2 ^ 59
def prefixEnd_1386339 : Nat := 4983230072969 + 3 ^ 40 * 1386339 * 2
def baseEnd_1386339 : Nat := 237286085691185558662283

theorem tailTrace_1386339 : CollatzResearch.WordTrace tailWord_1386339 prefixEnd_1386339 237286085691185558662283 := by
  unfold tailWord_1386339
  simp only [CollatzResearch.WordTrace]
  refine ⟨50563937324538045696258071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33709291549692030464172047 50563937324538045696258071)
  ·
    refine ⟨75845905986807068544387107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50563937324538045696258071 75845905986807068544387107)
    ·
      refine ⟨113768858980210602816580661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75845905986807068544387107 113768858980210602816580661)
      ·
        refine ⟨10665830529394744014054437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113768858980210602816580661 10665830529394744014054437)
        ·
          refine ⟨1999843224261514502635207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10665830529394744014054437 1999843224261514502635207)
          ·
            refine ⟨2999764836392271753952811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999843224261514502635207 2999764836392271753952811)
            ·
              refine ⟨4499647254588407630929217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999764836392271753952811 4499647254588407630929217)
              ·
                refine ⟨3374735440941305723196913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499647254588407630929217 3374735440941305723196913)
                ·
                  refine ⟨2531051580705979292397685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374735440941305723196913 2531051580705979292397685)
                  ·
                    refine ⟨237286085691185558662283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2531051580705979292397685 237286085691185558662283)
                    ·
                      rfl

theorem cell23_1386339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 5].length) (baseStart_1386339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386339 prefixEnd_1386339 := by exact prefixLift 1386339
  have htrace : WordTrace (prefixWord ++ tailWord_1386339) baseStart_1386339 baseEnd_1386339 := by
    simpa [prefixWord, tailWord_1386339, baseEnd_1386339] using wordTrace_append hprefix tailTrace_1386339
  have hstable : (prefixWord ++ tailWord_1386339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386339).length < 2 ^ (prefixWord ++ tailWord_1386339).sum := by decide
  have hdescent : baseEnd_1386339 < baseStart_1386339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386362 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_1386362 : Nat := 118140960795 + 1386362 * 2 ^ 59
def prefixEnd_1386362 : Nat := 4983230072969 + 3 ^ 40 * 1386362 * 2
def baseEnd_1386362 : Nat := 711870067128610085999243

theorem tailTrace_1386362 : CollatzResearch.WordTrace tailWord_1386362 prefixEnd_1386362 711870067128610085999243 := by
  unfold tailWord_1386362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641194050863680156086335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33709850802303147082896893 12641194050863680156086335)
  ·
    refine ⟨18961791076295520234129503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641194050863680156086335 18961791076295520234129503)
    ·
      refine ⟨28442686614443280351194255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18961791076295520234129503 28442686614443280351194255)
      ·
        refine ⟨42664029921664920526791383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28442686614443280351194255 42664029921664920526791383)
        ·
          refine ⟨63996044882497380790187075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42664029921664920526791383 63996044882497380790187075)
          ·
            refine ⟨95994067323746071185280613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63996044882497380790187075 95994067323746071185280613)
            ·
              refine ⟨17998887623202388347240115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95994067323746071185280613 17998887623202388347240115)
              ·
                refine ⟨26998331434803582520860173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17998887623202388347240115 26998331434803582520860173)
                ·
                  refine ⟨10124374288051343445322565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26998331434803582520860173 10124374288051343445322565)
                  ·
                    refine ⟨1898320179009626895997981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10124374288051343445322565 1898320179009626895997981)
                    ·
                      refine ⟨711870067128610085999243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898320179009626895997981 711870067128610085999243)
                      ·
                        rfl

theorem cell23_1386362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_1386362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386362 prefixEnd_1386362 := by exact prefixLift 1386362
  have htrace : WordTrace (prefixWord ++ tailWord_1386362) baseStart_1386362 baseEnd_1386362 := by
    simpa [prefixWord, tailWord_1386362, baseEnd_1386362] using wordTrace_append hprefix tailTrace_1386362
  have hstable : (prefixWord ++ tailWord_1386362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386362).length < 2 ^ (prefixWord ++ tailWord_1386362).sum := by decide
  have hdescent : baseEnd_1386362 < baseStart_1386362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386372 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1386372 : Nat := 118140960795 + 1386372 * 2 ^ 59
def prefixEnd_1386372 : Nat := 4983230072969 + 3 ^ 40 * 1386372 * 2
def baseEnd_1386372 : Nat := 711875201935155046874197

theorem tailTrace_1386372 : CollatzResearch.WordTrace tailWord_1386372 prefixEnd_1386372 711875201935155046874197 := by
  unfold tailWord_1386372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282570466709246166104685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33710093955612328221472913 25282570466709246166104685)
  ·
    refine ⟨9480963925015967312289257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25282570466709246166104685 9480963925015967312289257)
    ·
      refine ⟨7110722943761975484216943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9480963925015967312289257 7110722943761975484216943)
      ·
        refine ⟨10666084415642963226325415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110722943761975484216943 10666084415642963226325415)
        ·
          refine ⟨15999126623464444839488123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666084415642963226325415 15999126623464444839488123)
          ·
            refine ⟨23998689935196667259232185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15999126623464444839488123 23998689935196667259232185)
            ·
              refine ⟨17999017451397500444424139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23998689935196667259232185 17999017451397500444424139)
              ·
                refine ⟨26998526177096250666636209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17999017451397500444424139 26998526177096250666636209)
                ·
                  refine ⟨20248894632822187999977157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26998526177096250666636209 20248894632822187999977157)
                  ·
                    refine ⟨3796667743654160249995717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20248894632822187999977157 3796667743654160249995717)
                    ·
                      refine ⟨711875201935155046874197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3796667743654160249995717 711875201935155046874197)
                      ·
                        rfl

theorem cell23_1386372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1386372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386372 prefixEnd_1386372 := by exact prefixLift 1386372
  have htrace : WordTrace (prefixWord ++ tailWord_1386372) baseStart_1386372 baseEnd_1386372 := by
    simpa [prefixWord, tailWord_1386372, baseEnd_1386372] using wordTrace_append hprefix tailTrace_1386372
  have hstable : (prefixWord ++ tailWord_1386372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386372).length < 2 ^ (prefixWord ++ tailWord_1386372).sum := by decide
  have hdescent : baseEnd_1386372 < baseStart_1386372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386376 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1386376 : Nat := 118140960795 + 1386376 * 2 ^ 59
def prefixEnd_1386376 : Nat := 4983230072969 + 3 ^ 40 * 1386376 * 2
def baseEnd_1386376 : Nat := 711877255857773031224179

theorem tailTrace_1386376 : CollatzResearch.WordTrace tailWord_1386376 prefixEnd_1386376 711877255857773031224179 := by
  unfold tailWord_1386376
  simp only [CollatzResearch.WordTrace]
  refine ⟨25282643412702000507677491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33710191216936000676903321 25282643412702000507677491)
  ·
    refine ⟨37923965119053000761516237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25282643412702000507677491 37923965119053000761516237)
    ·
      refine ⟨14221486919644875285568589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37923965119053000761516237 14221486919644875285568589)
      ·
        refine ⟨5333057594866828232088221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14221486919644875285568589 5333057594866828232088221)
        ·
          refine ⟨1999896598075060587033083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5333057594866828232088221 1999896598075060587033083)
          ·
            refine ⟨2999844897112590880549625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999896598075060587033083 2999844897112590880549625)
            ·
              refine ⟨2249883672834443160412219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999844897112590880549625 2249883672834443160412219)
              ·
                refine ⟨3374825509251664740618329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249883672834443160412219 3374825509251664740618329)
                ·
                  refine ⟨2531119131938748555463747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374825509251664740618329 2531119131938748555463747)
                  ·
                    refine ⟨3796678697908122833195621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2531119131938748555463747 3796678697908122833195621)
                    ·
                      refine ⟨711877255857773031224179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3796678697908122833195621 711877255857773031224179)
                      ·
                        rfl

theorem cell23_1386376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1386376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386376 prefixEnd_1386376 := by exact prefixLift 1386376
  have htrace : WordTrace (prefixWord ++ tailWord_1386376) baseStart_1386376 baseEnd_1386376 := by
    simpa [prefixWord, tailWord_1386376, baseEnd_1386376] using wordTrace_append hprefix tailTrace_1386376
  have hstable : (prefixWord ++ tailWord_1386376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386376).length < 2 ^ (prefixWord ++ tailWord_1386376).sum := by decide
  have hdescent : baseEnd_1386376 < baseStart_1386376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386396 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1386396 : Nat := 118140960795 + 1386396 * 2 ^ 59
def prefixEnd_1386396 : Nat := 4983230072969 + 3 ^ 40 * 1386396 * 2
def baseEnd_1386396 : Nat := 711887525470862952974087

theorem tailTrace_1386396 : CollatzResearch.WordTrace tailWord_1386396 prefixEnd_1386396 711887525470862952974087 := by
  unfold tailWord_1386396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25283008142665772215541521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33710677523554362954055361 25283008142665772215541521)
  ·
    refine ⟨18962256106999329161656141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25283008142665772215541521 18962256106999329161656141)
    ·
      refine ⟨7110846040124748435621053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18962256106999329161656141 7110846040124748435621053)
      ·
        refine ⟨2666567265046780663357895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7110846040124748435621053 2666567265046780663357895)
        ·
          refine ⟨3999850897570170995036843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666567265046780663357895 3999850897570170995036843)
          ·
            refine ⟨5999776346355256492555265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999850897570170995036843 5999776346355256492555265)
            ·
              refine ⟨4499832259766442369416449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999776346355256492555265 4499832259766442369416449)
              ·
                refine ⟨3374874194824831777062337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499832259766442369416449 3374874194824831777062337)
                ·
                  refine ⟨2531155646118623832796753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374874194824831777062337 2531155646118623832796753)
                  ·
                    refine ⟨1898366734588967874597565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531155646118623832796753 1898366734588967874597565)
                    ·
                      refine ⟨711887525470862952974087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898366734588967874597565 711887525470862952974087)
                      ·
                        rfl

theorem cell23_1386396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1386396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386396 prefixEnd_1386396 := by exact prefixLift 1386396
  have htrace : WordTrace (prefixWord ++ tailWord_1386396) baseStart_1386396 baseEnd_1386396 := by
    simpa [prefixWord, tailWord_1386396, baseEnd_1386396] using wordTrace_append hprefix tailTrace_1386396
  have hstable : (prefixWord ++ tailWord_1386396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386396).length < 2 ^ (prefixWord ++ tailWord_1386396).sum := by decide
  have hdescent : baseEnd_1386396 < baseStart_1386396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386419 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 5, 2]
def baseStart_1386419 : Nat := 118140960795 + 1386419 * 2 ^ 59
def prefixEnd_1386419 : Nat := 4983230072969 + 3 ^ 40 * 1386419 * 2
def baseEnd_1386419 : Nat := 711899335525916362986481

theorem tailTrace_1386419 : CollatzResearch.WordTrace tailWord_1386419 prefixEnd_1386419 711899335525916362986481 := by
  unfold tailWord_1386419
  simp only [CollatzResearch.WordTrace]
  refine ⟨50566855164248219359170311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33711236776165479572780207 50566855164248219359170311)
  ·
    refine ⟨75850282746372329038755467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50566855164248219359170311 75850282746372329038755467)
    ·
      refine ⟨113775424119558493558133201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75850282746372329038755467 113775424119558493558133201)
      ·
        refine ⟨85331568089668870168599901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113775424119558493558133201 85331568089668870168599901)
        ·
          refine ⟨31999338033625826313224963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85331568089668870168599901 31999338033625826313224963)
          ·
            refine ⟨47999007050438739469837445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31999338033625826313224963 47999007050438739469837445)
            ·
              refine ⟨8999813821957263650594521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47999007050438739469837445 8999813821957263650594521)
              ·
                refine ⟨6749860366467947737945891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8999813821957263650594521 6749860366467947737945891)
                ·
                  refine ⟨10124790549701921606918837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749860366467947737945891 10124790549701921606918837)
                  ·
                    refine ⟨949199114034555150648641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10124790549701921606918837 949199114034555150648641)
                    ·
                      refine ⟨711899335525916362986481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949199114034555150648641 711899335525916362986481)
                      ·
                        rfl

theorem cell23_1386419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5, 2].length) (baseStart_1386419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386419 prefixEnd_1386419 := by exact prefixLift 1386419
  have htrace : WordTrace (prefixWord ++ tailWord_1386419) baseStart_1386419 baseEnd_1386419 := by
    simpa [prefixWord, tailWord_1386419, baseEnd_1386419] using wordTrace_append hprefix tailTrace_1386419
  have hstable : (prefixWord ++ tailWord_1386419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386419).length < 2 ^ (prefixWord ++ tailWord_1386419).sum := by decide
  have hdescent : baseEnd_1386419 < baseStart_1386419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386429 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1386429 : Nat := 118140960795 + 1386429 * 2 ^ 59
def prefixEnd_1386429 : Nat := 4983230072969 + 3 ^ 40 * 1386429 * 2
def baseEnd_1386429 : Nat := 237301490110820441287145

theorem tailTrace_1386429 : CollatzResearch.WordTrace tailWord_1386429 prefixEnd_1386429 237301490110820441287145 := by
  unfold tailWord_1386429
  simp only [CollatzResearch.WordTrace]
  refine ⟨50567219894211991067034341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33711479929474660711356227 50567219894211991067034341)
  ·
    refine ⟨9481353730164748325068939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50567219894211991067034341 9481353730164748325068939)
    ·
      refine ⟨14222030595247122487603409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481353730164748325068939 14222030595247122487603409)
      ·
        refine ⟨10666522946435341865702557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14222030595247122487603409 10666522946435341865702557)
        ·
          refine ⟨3999946104913253199638459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10666522946435341865702557 3999946104913253199638459)
          ·
            refine ⟨5999919157369879799457689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999946104913253199638459 5999919157369879799457689)
            ·
              refine ⟨4499939368027409849593267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999919157369879799457689 4499939368027409849593267)
              ·
                refine ⟨6749909052041114774389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499939368027409849593267 6749909052041114774389901)
                ·
                  refine ⟨2531215894515418040396213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6749909052041114774389901 2531215894515418040396213)
                  ·
                    refine ⟨237301490110820441287145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2531215894515418040396213 237301490110820441287145)
                    ·
                      rfl

theorem cell23_1386429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1386429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386429 prefixEnd_1386429 := by exact prefixLift 1386429
  have htrace : WordTrace (prefixWord ++ tailWord_1386429) baseStart_1386429 baseEnd_1386429 := by
    simpa [prefixWord, tailWord_1386429, baseEnd_1386429] using wordTrace_append hprefix tailTrace_1386429
  have hstable : (prefixWord ++ tailWord_1386429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386429).length < 2 ^ (prefixWord ++ tailWord_1386429).sum := by decide
  have hdescent : baseEnd_1386429 < baseStart_1386429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386443 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 1, 1, 3]
def baseStart_1386443 : Nat := 118140960795 + 1386443 * 2 ^ 59
def prefixEnd_1386443 : Nat := 4983230072969 + 3 ^ 40 * 1386443 * 2
def baseEnd_1386443 : Nat := 711911659061624269086371

theorem tailTrace_1386443 : CollatzResearch.WordTrace tailWord_1386443 prefixEnd_1386443 711911659061624269086371 := by
  unfold tailWord_1386443
  simp only [CollatzResearch.WordTrace]
  refine ⟨50567730516161271458043983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33711820344107514305362655 50567730516161271458043983)
  ·
    refine ⟨75851595774241907187065975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50567730516161271458043983 75851595774241907187065975)
    ·
      refine ⟨113777393661362860780598963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75851595774241907187065975 113777393661362860780598963)
      ·
        refine ⟨170666090492044291170898445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113777393661362860780598963 170666090492044291170898445)
        ·
          refine ⟨63999783934516609189086917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170666090492044291170898445 63999783934516609189086917)
          ·
            refine ⟨11999959487721864222953797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63999783934516609189086917 11999959487721864222953797)
            ·
              refine ⟨2249992403947849541803837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11999959487721864222953797 2249992403947849541803837)
              ·
                refine ⟨843747151480443578176439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2249992403947849541803837 843747151480443578176439)
                ·
                  refine ⟨1265620727220665367264659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843747151480443578176439 1265620727220665367264659)
                  ·
                    refine ⟨1898431090830998050896989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265620727220665367264659 1898431090830998050896989)
                    ·
                      refine ⟨711911659061624269086371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898431090830998050896989 711911659061624269086371)
                      ·
                        rfl

theorem cell23_1386443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 1, 3].length) (baseStart_1386443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386443 prefixEnd_1386443 := by exact prefixLift 1386443
  have htrace : WordTrace (prefixWord ++ tailWord_1386443) baseStart_1386443 baseEnd_1386443 := by
    simpa [prefixWord, tailWord_1386443, baseEnd_1386443] using wordTrace_append hprefix tailTrace_1386443
  have hstable : (prefixWord ++ tailWord_1386443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386443).length < 2 ^ (prefixWord ++ tailWord_1386443).sum := by decide
  have hdescent : baseEnd_1386443 < baseStart_1386443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386472 : List Nat := [2, 1, 4, 1, 1, 1, 1, 12]
def baseStart_1386472 : Nat := 118140960795 + 1386472 * 2 ^ 59
def prefixEnd_1386472 : Nat := 4983230072969 + 3 ^ 40 * 1386472 * 2
def baseEnd_1386472 : Nat := 26367650000022394652731

theorem tailTrace_1386472 : CollatzResearch.WordTrace tailWord_1386472 prefixEnd_1386472 26367650000022394652731 := by
  unfold tailWord_1386472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25284394116528104705424835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33712525488704139607233113 25284394116528104705424835)
  ·
    refine ⟨37926591174792157058137253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25284394116528104705424835 37926591174792157058137253)
    ·
      refine ⟨7111235845273529448400735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37926591174792157058137253 7111235845273529448400735)
      ·
        refine ⟨10666853767910294172601103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7111235845273529448400735 10666853767910294172601103)
        ·
          refine ⟨16000280651865441258901655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666853767910294172601103 16000280651865441258901655)
          ·
            refine ⟨24000420977798161888352483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16000280651865441258901655 24000420977798161888352483)
            ·
              refine ⟨36000631466697242832528725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24000420977798161888352483 36000631466697242832528725)
              ·
                refine ⟨26367650000022394652731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 36000631466697242832528725 26367650000022394652731)
                ·
                  rfl

theorem cell23_1386472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 12].length) (baseStart_1386472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386472 prefixEnd_1386472 := by exact prefixLift 1386472
  have htrace : WordTrace (prefixWord ++ tailWord_1386472) baseStart_1386472 baseEnd_1386472 := by
    simpa [prefixWord, tailWord_1386472, baseEnd_1386472] using wordTrace_append hprefix tailTrace_1386472
  have hstable : (prefixWord ++ tailWord_1386472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386472).length < 2 ^ (prefixWord ++ tailWord_1386472).sum := by decide
  have hdescent : baseEnd_1386472 < baseStart_1386472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386489 : List Nat := [1, 2, 1, 3, 1, 4, 4, 7]
def baseStart_1386489 : Nat := 118140960795 + 1386489 * 2 ^ 59
def prefixEnd_1386489 : Nat := 4983230072969 + 3 ^ 40 * 1386489 * 2
def baseEnd_1386489 : Nat := 26367973302656707004117

theorem tailTrace_1386489 : CollatzResearch.WordTrace tailWord_1386489 prefixEnd_1386489 26367973302656707004117 := by
  unfold tailWord_1386489
  simp only [CollatzResearch.WordTrace]
  refine ⟨50569408273994621314218521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33712938849329747542812347 50569408273994621314218521)
  ·
    refine ⟨37927056205495965985663891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50569408273994621314218521 37927056205495965985663891)
    ·
      refine ⟨56890584308243948978495837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37927056205495965985663891 56890584308243948978495837)
      ·
        refine ⟨21333969115591480866935939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56890584308243948978495837 21333969115591480866935939)
        ·
          refine ⟨32000953673387221300403909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21333969115591480866935939 32000953673387221300403909)
          ·
            refine ⟨6000178813760103993825733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32000953673387221300403909 6000178813760103993825733)
            ·
              refine ⟨1125033527580019498842325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6000178813760103993825733 1125033527580019498842325)
              ·
                refine ⟨26367973302656707004117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1125033527580019498842325 26367973302656707004117)
                ·
                  rfl

theorem cell23_1386489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 7].length) (baseStart_1386489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386489 prefixEnd_1386489 := by exact prefixLift 1386489
  have htrace : WordTrace (prefixWord ++ tailWord_1386489) baseStart_1386489 baseEnd_1386489 := by
    simpa [prefixWord, tailWord_1386489, baseEnd_1386489] using wordTrace_append hprefix tailTrace_1386489
  have hstable : (prefixWord ++ tailWord_1386489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386489).length < 2 ^ (prefixWord ++ tailWord_1386489).sum := by decide
  have hdescent : baseEnd_1386489 < baseStart_1386489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386499 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3]
def baseStart_1386499 : Nat := 118140960795 + 1386499 * 2 ^ 59
def prefixEnd_1386499 : Nat := 4983230072969 + 3 ^ 40 * 1386499 * 2
def baseEnd_1386499 : Nat := 711940413978276049986113

theorem tailTrace_1386499 : CollatzResearch.WordTrace tailWord_1386499 prefixEnd_1386499 711940413978276049986113 := by
  unfold tailWord_1386499
  simp only [CollatzResearch.WordTrace]
  refine ⟨50569773003958393022082551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33713182002638928681388367 50569773003958393022082551)
  ·
    refine ⟨75854659505937589533123827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50569773003958393022082551 75854659505937589533123827)
    ·
      refine ⟨113781989258906384299685741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75854659505937589533123827 113781989258906384299685741)
      ·
        refine ⟨42668245972089894112382153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113781989258906384299685741 42668245972089894112382153)
        ·
          refine ⟨32001184479067420584286615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42668245972089894112382153 32001184479067420584286615)
          ·
            refine ⟨48001776718601130876429923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32001184479067420584286615 48001776718601130876429923)
            ·
              refine ⟨72002665077901696314644885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48001776718601130876429923 72002665077901696314644885)
              ·
                refine ⟨3375124925526642014748979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72002665077901696314644885 3375124925526642014748979)
                ·
                  refine ⟨5062687388289963022123469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375124925526642014748979 5062687388289963022123469)
                  ·
                    refine ⟨1898507770608736133296301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5062687388289963022123469 1898507770608736133296301)
                    ·
                      refine ⟨711940413978276049986113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898507770608736133296301 711940413978276049986113)
                      ·
                        rfl

theorem cell23_1386499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_1386499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386499 prefixEnd_1386499 := by exact prefixLift 1386499
  have htrace : WordTrace (prefixWord ++ tailWord_1386499) baseStart_1386499 baseEnd_1386499 := by
    simpa [prefixWord, tailWord_1386499, baseEnd_1386499] using wordTrace_append hprefix tailTrace_1386499
  have hstable : (prefixWord ++ tailWord_1386499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386499).length < 2 ^ (prefixWord ++ tailWord_1386499).sum := by decide
  have hdescent : baseEnd_1386499 < baseStart_1386499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386506 : List Nat := [3, 1, 2, 2, 5, 1, 9]
def baseStart_1386506 : Nat := 118140960795 + 1386506 * 2 ^ 59
def prefixEnd_1386506 : Nat := 4983230072969 + 3 ^ 40 * 1386506 * 2
def baseEnd_1386506 : Nat := 8789432201763673118501

theorem tailTrace_1386506 : CollatzResearch.WordTrace tailWord_1386506 prefixEnd_1386506 8789432201763673118501 := by
  unfold tailWord_1386506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642507078733258304396843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33713352209955355478391581 12642507078733258304396843)
  ·
    refine ⟨18963760618099887456595265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12642507078733258304396843 18963760618099887456595265)
    ·
      refine ⟨14222820463574915592446449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18963760618099887456595265 14222820463574915592446449)
      ·
        refine ⟨10667115347681186694334837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14222820463574915592446449 10667115347681186694334837)
        ·
          refine ⟨1000042063845111252593891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10667115347681186694334837 1000042063845111252593891)
          ·
            refine ⟨1500063095767666878890837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000042063845111252593891 1500063095767666878890837)
            ·
              refine ⟨8789432201763673118501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1500063095767666878890837 8789432201763673118501)
              ·
                rfl

theorem cell23_1386506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 9].length) (baseStart_1386506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386506 prefixEnd_1386506 := by exact prefixLift 1386506
  have htrace : WordTrace (prefixWord ++ tailWord_1386506) baseStart_1386506 baseEnd_1386506 := by
    simpa [prefixWord, tailWord_1386506, baseEnd_1386506] using wordTrace_append hprefix tailTrace_1386506
  have hstable : (prefixWord ++ tailWord_1386506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386506).length < 2 ^ (prefixWord ++ tailWord_1386506).sum := by decide
  have hdescent : baseEnd_1386506 < baseStart_1386506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386517 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_1386517 : Nat := 118140960795 + 1386517 * 2 ^ 59
def prefixEnd_1386517 : Nat := 4983230072969 + 3 ^ 40 * 1386517 * 2
def baseEnd_1386517 : Nat := 711949656630056979561031

theorem tailTrace_1386517 : CollatzResearch.WordTrace tailWord_1386517 prefixEnd_1386517 711949656630056979561031 := by
  unfold tailWord_1386517
  simp only [CollatzResearch.WordTrace]
  refine ⟨50570429517893182096237805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33713619678595454730825203 50570429517893182096237805)
  ·
    refine ⟨18963911069209943286089177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50570429517893182096237805 18963911069209943286089177)
    ·
      refine ⟨14222933301907457464566883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18963911069209943286089177 14222933301907457464566883)
      ·
        refine ⟨21334399952861186196850325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222933301907457464566883 21334399952861186196850325)
        ·
          refine ⟨1000049997790368102977359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21334399952861186196850325 1000049997790368102977359)
          ·
            refine ⟨1500074996685552154466039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000049997790368102977359 1500074996685552154466039)
            ·
              refine ⟨2250112495028328231699059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500074996685552154466039 2250112495028328231699059)
              ·
                refine ⟨3375168742542492347548589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250112495028328231699059 3375168742542492347548589)
                ·
                  refine ⟨1265688278453434630330721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3375168742542492347548589 1265688278453434630330721)
                  ·
                    refine ⟨949266208840075972748041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1265688278453434630330721 949266208840075972748041)
                    ·
                      refine ⟨711949656630056979561031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949266208840075972748041 711949656630056979561031)
                      ·
                        rfl

theorem cell23_1386517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_1386517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386517 prefixEnd_1386517 := by exact prefixLift 1386517
  have htrace : WordTrace (prefixWord ++ tailWord_1386517) baseStart_1386517 baseEnd_1386517 := by
    simpa [prefixWord, tailWord_1386517, baseEnd_1386517] using wordTrace_append hprefix tailTrace_1386517
  have hstable : (prefixWord ++ tailWord_1386517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386517).length < 2 ^ (prefixWord ++ tailWord_1386517).sum := by decide
  have hdescent : baseEnd_1386517 < baseStart_1386517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386533 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_1386533 : Nat := 118140960795 + 1386533 * 2 ^ 59
def prefixEnd_1386533 : Nat := 4983230072969 + 3 ^ 40 * 1386533 * 2
def baseEnd_1386533 : Nat := 711957872320528916960957

theorem tailTrace_1386533 : CollatzResearch.WordTrace tailWord_1386533 prefixEnd_1386533 711957872320528916960957 := by
  unfold tailWord_1386533
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571013085835216828820253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33714008723890144552546835 50571013085835216828820253)
  ·
    refine ⟨18964129907188206310807595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50571013085835216828820253 18964129907188206310807595)
    ·
      refine ⟨28446194860782309466211393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18964129907188206310807595 28446194860782309466211393)
      ·
        refine ⟨21334646145586732099658545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28446194860782309466211393 21334646145586732099658545)
        ·
          refine ⟨16000984609190049074743909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21334646145586732099658545 16000984609190049074743909)
          ·
            refine ⟨3000184614223134201514483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16000984609190049074743909 3000184614223134201514483)
            ·
              refine ⟨4500276921334701302271725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000184614223134201514483 4500276921334701302271725)
              ·
                refine ⟨1687603845500512988351897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4500276921334701302271725 1687603845500512988351897)
                ·
                  refine ⟨1265702884125384741263923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687603845500512988351897 1265702884125384741263923)
                  ·
                    refine ⟨1898554326188077111895885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265702884125384741263923 1898554326188077111895885)
                    ·
                      refine ⟨711957872320528916960957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898554326188077111895885 711957872320528916960957)
                      ·
                        rfl

theorem cell23_1386533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_1386533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386533 prefixEnd_1386533 := by exact prefixLift 1386533
  have htrace : WordTrace (prefixWord ++ tailWord_1386533) baseStart_1386533 baseEnd_1386533 := by
    simpa [prefixWord, tailWord_1386533, baseEnd_1386533] using wordTrace_append hprefix tailTrace_1386533
  have hstable : (prefixWord ++ tailWord_1386533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386533).length < 2 ^ (prefixWord ++ tailWord_1386533).sum := by decide
  have hdescent : baseEnd_1386533 < baseStart_1386533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386559 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1386559 : Nat := 118140960795 + 1386559 * 2 ^ 59
def prefixEnd_1386559 : Nat := 4983230072969 + 3 ^ 40 * 1386559 * 2
def baseEnd_1386559 : Nat := 711971222817545815235837

theorem tailTrace_1386559 : CollatzResearch.WordTrace tailWord_1386559 prefixEnd_1386559 711971222817545815235837 := by
  unfold tailWord_1386559
  simp only [CollatzResearch.WordTrace]
  refine ⟨50571961383741023269266731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33714640922494015512844487 50571961383741023269266731)
  ·
    refine ⟨75857942075611534903900097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50571961383741023269266731 75857942075611534903900097)
    ·
      refine ⟨56893456556708651177925073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75857942075611534903900097 56893456556708651177925073)
      ·
        refine ⟨42670092417531488383443805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56893456556708651177925073 42670092417531488383443805)
        ·
          refine ⟨16001284656574308143791427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42670092417531488383443805 16001284656574308143791427)
          ·
            refine ⟨24001926984861462215687141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16001284656574308143791427 24001926984861462215687141)
            ·
              refine ⟨4500361309661524165441339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24001926984861462215687141 4500361309661524165441339)
              ·
                refine ⟨6750541964492286248162009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500361309661524165441339 6750541964492286248162009)
                ·
                  refine ⟨5062906473369214686121507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750541964492286248162009 5062906473369214686121507)
                  ·
                    refine ⟨7594359710053822029182261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062906473369214686121507 7594359710053822029182261)
                    ·
                      refine ⟨711971222817545815235837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7594359710053822029182261 711971222817545815235837)
                      ·
                        rfl

theorem cell23_1386559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1386559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386559 prefixEnd_1386559 := by exact prefixLift 1386559
  have htrace : WordTrace (prefixWord ++ tailWord_1386559) baseStart_1386559 baseEnd_1386559 := by
    simpa [prefixWord, tailWord_1386559, baseEnd_1386559] using wordTrace_append hprefix tailTrace_1386559
  have hstable : (prefixWord ++ tailWord_1386559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386559).length < 2 ^ (prefixWord ++ tailWord_1386559).sum := by decide
  have hdescent : baseEnd_1386559 < baseStart_1386559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386560 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2]
def baseStart_1386560 : Nat := 118140960795 + 1386560 * 2 ^ 59
def prefixEnd_1386560 : Nat := 4983230072969 + 3 ^ 40 * 1386560 * 2
def baseEnd_1386560 : Nat := 711971736298200311323333

theorem tailTrace_1386560 : CollatzResearch.WordTrace tailWord_1386560 prefixEnd_1386560 711971736298200311323333 := by
  unfold tailWord_1386560
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285998928368700220026567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33714665237824933626702089 25285998928368700220026567)
  ·
    refine ⟨37928998392553050330039851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25285998928368700220026567 37928998392553050330039851)
    ·
      refine ⟨56893497588829575495059777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37928998392553050330039851 56893497588829575495059777)
      ·
        refine ⟨42670123191622181621294833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56893497588829575495059777 42670123191622181621294833)
        ·
          refine ⟨32002592393716636215971125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42670123191622181621294833 32002592393716636215971125)
          ·
            refine ⟨3000243036910934645247293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32002592393716636215971125 3000243036910934645247293)
            ·
              refine ⟨1125091138841600491967735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3000243036910934645247293 1125091138841600491967735)
              ·
                refine ⟨1687636708262400737951603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125091138841600491967735 1687636708262400737951603)
                ·
                  refine ⟨2531455062393601106927405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687636708262400737951603 2531455062393601106927405)
                  ·
                    refine ⟨949295648397600415097777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531455062393601106927405 949295648397600415097777)
                    ·
                      refine ⟨711971736298200311323333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949295648397600415097777 711971736298200311323333)
                      ·
                        rfl

theorem cell23_1386560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_1386560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386560 prefixEnd_1386560 := by exact prefixLift 1386560
  have htrace : WordTrace (prefixWord ++ tailWord_1386560) baseStart_1386560 baseEnd_1386560 := by
    simpa [prefixWord, tailWord_1386560, baseEnd_1386560] using wordTrace_append hprefix tailTrace_1386560
  have hstable : (prefixWord ++ tailWord_1386560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386560).length < 2 ^ (prefixWord ++ tailWord_1386560).sum := by decide
  have hdescent : baseEnd_1386560 < baseStart_1386560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386569 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_1386569 : Nat := 118140960795 + 1386569 * 2 ^ 59
def prefixEnd_1386569 : Nat := 4983230072969 + 3 ^ 40 * 1386569 * 2
def baseEnd_1386569 : Nat := 711976357624090776110791

theorem tailTrace_1386569 : CollatzResearch.WordTrace tailWord_1386569 prefixEnd_1386569 711976357624090776110791 := by
  unfold tailWord_1386569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50572326113704794977130761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33714884075803196651420507 50572326113704794977130761)
  ·
    refine ⟨37929244585278596232848071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50572326113704794977130761 37929244585278596232848071)
    ·
      refine ⟨56893866877917894349272107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37929244585278596232848071 56893866877917894349272107)
      ·
        refine ⟨85340800316876841523908161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56893866877917894349272107 85340800316876841523908161)
        ·
          refine ⟨64005600237657631142931121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85340800316876841523908161 64005600237657631142931121)
          ·
            refine ⟨48004200178243223357198341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64005600237657631142931121 48004200178243223357198341)
            ·
              refine ⟨9000787533420604379474689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48004200178243223357198341 9000787533420604379474689)
              ·
                refine ⟨6750590650065453284606017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9000787533420604379474689 6750590650065453284606017)
                ·
                  refine ⟨5062942987549089963454513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6750590650065453284606017 5062942987549089963454513)
                  ·
                    refine ⟨3797207240661817472590885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5062942987549089963454513 3797207240661817472590885)
                    ·
                      refine ⟨711976357624090776110791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3797207240661817472590885 711976357624090776110791)
                      ·
                        rfl

theorem cell23_1386569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_1386569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386569 prefixEnd_1386569 := by exact prefixLift 1386569
  have htrace : WordTrace (prefixWord ++ tailWord_1386569) baseStart_1386569 baseEnd_1386569 := by
    simpa [prefixWord, tailWord_1386569, baseEnd_1386569] using wordTrace_append hprefix tailTrace_1386569
  have hstable : (prefixWord ++ tailWord_1386569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386569).length < 2 ^ (prefixWord ++ tailWord_1386569).sum := by decide
  have hdescent : baseEnd_1386569 < baseStart_1386569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386573 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1386573 : Nat := 118140960795 + 1386573 * 2 ^ 59
def prefixEnd_1386573 : Nat := 4983230072969 + 3 ^ 40 * 1386573 * 2
def baseEnd_1386573 : Nat := 711978411546708760460773

theorem tailTrace_1386573 : CollatzResearch.WordTrace tailWord_1386573 prefixEnd_1386573 711978411546708760460773 := by
  unfold tailWord_1386573
  simp only [CollatzResearch.WordTrace]
  refine ⟨50572472005690303660276373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33714981337126869106850915 50572472005690303660276373)
  ·
    refine ⟨2370584625266732984075455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50572472005690303660276373 2370584625266732984075455)
    ·
      refine ⟨3555876937900099476113183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370584625266732984075455 3555876937900099476113183)
      ·
        refine ⟨5333815406850149214169775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555876937900099476113183 5333815406850149214169775)
        ·
          refine ⟨8000723110275223821254663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333815406850149214169775 8000723110275223821254663)
          ·
            refine ⟨12001084665412835731881995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000723110275223821254663 12001084665412835731881995)
            ·
              refine ⟨18001626998119253597822993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12001084665412835731881995 18001626998119253597822993)
              ·
                refine ⟨13501220248589440198367245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18001626998119253597822993 13501220248589440198367245)
                ·
                  refine ⟨5062957593221040074387717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13501220248589440198367245 5062957593221040074387717)
                  ·
                    refine ⟨949304548728945013947697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062957593221040074387717 949304548728945013947697)
                    ·
                      refine ⟨711978411546708760460773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949304548728945013947697 711978411546708760460773)
                      ·
                        rfl

theorem cell23_1386573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1386573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386573 prefixEnd_1386573 := by exact prefixLift 1386573
  have htrace : WordTrace (prefixWord ++ tailWord_1386573) baseStart_1386573 baseEnd_1386573 := by
    simpa [prefixWord, tailWord_1386573, baseEnd_1386573] using wordTrace_append hprefix tailTrace_1386573
  have hstable : (prefixWord ++ tailWord_1386573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386573).length < 2 ^ (prefixWord ++ tailWord_1386573).sum := by decide
  have hdescent : baseEnd_1386573 < baseStart_1386573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386606 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1386606 : Nat := 118140960795 + 1386606 * 2 ^ 59
def prefixEnd_1386606 : Nat := 4983230072969 + 3 ^ 40 * 1386606 * 2
def baseEnd_1386606 : Nat := 711995356408307131348121

theorem tailTrace_1386606 : CollatzResearch.WordTrace tailWord_1386606 prefixEnd_1386606 711995356408307131348121 := by
  unfold tailWord_1386606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321709451821343787028459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33715783743047166864151781 6321709451821343787028459)
  ·
    refine ⟨9482564177732015680542689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6321709451821343787028459 9482564177732015680542689)
    ·
      refine ⟨7111923133299011760407017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9482564177732015680542689 7111923133299011760407017)
      ·
        refine ⟨5333942349974258820305263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7111923133299011760407017 5333942349974258820305263)
        ·
          refine ⟨8000913524961388230457895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333942349974258820305263 8000913524961388230457895)
          ·
            refine ⟨12001370287442082345686843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000913524961388230457895 12001370287442082345686843)
            ·
              refine ⟨18002055431163123518530265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12001370287442082345686843 18002055431163123518530265)
              ·
                refine ⟨13501541573372342638897699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18002055431163123518530265 13501541573372342638897699)
                ·
                  refine ⟨20252312360058513958346549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13501541573372342638897699 20252312360058513958346549)
                  ·
                    refine ⟨1898654283755485683594989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20252312360058513958346549 1898654283755485683594989)
                    ·
                      refine ⟨711995356408307131348121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898654283755485683594989 711995356408307131348121)
                      ·
                        rfl

theorem cell23_1386606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1386606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386606 prefixEnd_1386606 := by exact prefixLift 1386606
  have htrace : WordTrace (prefixWord ++ tailWord_1386606) baseStart_1386606 baseEnd_1386606 := by
    simpa [prefixWord, tailWord_1386606, baseEnd_1386606] using wordTrace_append hprefix tailTrace_1386606
  have hstable : (prefixWord ++ tailWord_1386606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386606).length < 2 ^ (prefixWord ++ tailWord_1386606).sum := by decide
  have hdescent : baseEnd_1386606 < baseStart_1386606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386609 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1386609 : Nat := 118140960795 + 1386609 * 2 ^ 59
def prefixEnd_1386609 : Nat := 4983230072969 + 3 ^ 40 * 1386609 * 2
def baseEnd_1386609 : Nat := 237332298950090206536869

theorem tailTrace_1386609 : CollatzResearch.WordTrace tailWord_1386609 prefixEnd_1386609 237332298950090206536869 := by
  unfold tailWord_1386609
  simp only [CollatzResearch.WordTrace]
  refine ⟨50573785033559881808586881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33715856689039921205724587 50573785033559881808586881)
  ·
    refine ⟨37930338775169911356440161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50573785033559881808586881 37930338775169911356440161)
    ·
      refine ⟨28447754081377433517330121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37930338775169911356440161 28447754081377433517330121)
      ·
        refine ⟨21335815561033075137997591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28447754081377433517330121 21335815561033075137997591)
        ·
          refine ⟨32003723341549612706996387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21335815561033075137997591 32003723341549612706996387)
          ·
            refine ⟨48005585012324419060494581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32003723341549612706996387 48005585012324419060494581)
            ·
              refine ⟨4500523594905414286921367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48005585012324419060494581 4500523594905414286921367)
              ·
                refine ⟨6750785392358121430382051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500523594905414286921367 6750785392358121430382051)
                ·
                  refine ⟨10126178088537182145573077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6750785392358121430382051 10126178088537182145573077)
                  ·
                    refine ⟨237332298950090206536869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10126178088537182145573077 237332298950090206536869)
                    ·
                      rfl

theorem cell23_1386609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1386609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386609 prefixEnd_1386609 := by exact prefixLift 1386609
  have htrace : WordTrace (prefixWord ++ tailWord_1386609) baseStart_1386609 baseEnd_1386609 := by
    simpa [prefixWord, tailWord_1386609, baseEnd_1386609] using wordTrace_append hprefix tailTrace_1386609
  have hstable : (prefixWord ++ tailWord_1386609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386609).length < 2 ^ (prefixWord ++ tailWord_1386609).sum := by decide
  have hdescent : baseEnd_1386609 < baseStart_1386609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386713 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_1386713 : Nat := 118140960795 + 1386713 * 2 ^ 59
def prefixEnd_1386713 : Nat := 4983230072969 + 3 ^ 40 * 1386713 * 2
def baseEnd_1386713 : Nat := 712050298838338212710129

theorem tailTrace_1386713 : CollatzResearch.WordTrace tailWord_1386713 prefixEnd_1386713 712050298838338212710129 := by
  unfold tailWord_1386713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50577578225183107570372793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33718385483455405046915195 50577578225183107570372793)
  ·
    refine ⟨37933183668887330677779595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50577578225183107570372793 37933183668887330677779595)
    ·
      refine ⟨56899775503330996016669393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37933183668887330677779595 56899775503330996016669393)
      ·
        refine ⟨42674831627498247012502045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56899775503330996016669393 42674831627498247012502045)
        ·
          refine ⟨16003061860311842629688267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42674831627498247012502045 16003061860311842629688267)
          ·
            refine ⟨24004592790467763944532401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16003061860311842629688267 24004592790467763944532401)
            ·
              refine ⟨18003444592850822958399301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24004592790467763944532401 18003444592850822958399301)
              ·
                refine ⟨3375645861159529304699869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18003444592850822958399301 3375645861159529304699869)
                ·
                  refine ⟨1265867197934823489262451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3375645861159529304699869 1265867197934823489262451)
                  ·
                    refine ⟨1898800796902235233893677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1265867197934823489262451 1898800796902235233893677)
                    ·
                      refine ⟨712050298838338212710129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898800796902235233893677 712050298838338212710129)
                      ·
                        rfl

theorem cell23_1386713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_1386713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386713 prefixEnd_1386713 := by exact prefixLift 1386713
  have htrace : WordTrace (prefixWord ++ tailWord_1386713) baseStart_1386713 baseEnd_1386713 := by
    simpa [prefixWord, tailWord_1386713, baseEnd_1386713] using wordTrace_append hprefix tailTrace_1386713
  have hstable : (prefixWord ++ tailWord_1386713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386713).length < 2 ^ (prefixWord ++ tailWord_1386713).sum := by decide
  have hdescent : baseEnd_1386713 < baseStart_1386713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386763 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 2, 4]
def baseStart_1386763 : Nat := 118140960795 + 1386763 * 2 ^ 59
def prefixEnd_1386763 : Nat := 4983230072969 + 3 ^ 40 * 1386763 * 2
def baseEnd_1386763 : Nat := 237358657623687672361633

theorem tailTrace_1386763 : CollatzResearch.WordTrace tailWord_1386763 prefixEnd_1386763 237358657623687672361633 := by
  unfold tailWord_1386763
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579401875001966109692943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33719601250001310739795295 50579401875001966109692943)
  ·
    refine ⟨75869102812502949164539415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50579401875001966109692943 75869102812502949164539415)
    ·
      refine ⟨113803654218754423746809123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75869102812502949164539415 113803654218754423746809123)
      ·
        refine ⟨170705481328131635620213685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113803654218754423746809123 170705481328131635620213685)
        ·
          refine ⟨16003638874512340839395033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170705481328131635620213685 16003638874512340839395033)
          ·
            refine ⟨12002729155884255629546275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16003638874512340839395033 12002729155884255629546275)
            ·
              refine ⟨18004093733826383444319413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12002729155884255629546275 18004093733826383444319413)
              ·
                refine ⟨1687883787546223447904945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18004093733826383444319413 1687883787546223447904945)
                ·
                  refine ⟨1265912840659667585928709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1687883787546223447904945 1265912840659667585928709)
                  ·
                    refine ⟨237358657623687672361633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265912840659667585928709 237358657623687672361633)
                    ·
                      rfl

theorem cell23_1386763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 4].length) (baseStart_1386763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386763 prefixEnd_1386763 := by exact prefixLift 1386763
  have htrace : WordTrace (prefixWord ++ tailWord_1386763) baseStart_1386763 baseEnd_1386763 := by
    simpa [prefixWord, tailWord_1386763, baseEnd_1386763] using wordTrace_append hprefix tailTrace_1386763
  have hstable : (prefixWord ++ tailWord_1386763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386763).length < 2 ^ (prefixWord ++ tailWord_1386763).sum := by decide
  have hdescent : baseEnd_1386763 < baseStart_1386763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386773 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1386773 : Nat := 118140960795 + 1386773 * 2 ^ 59
def prefixEnd_1386773 : Nat := 4983230072969 + 3 ^ 40 * 1386773 * 2
def baseEnd_1386773 : Nat := 712081107677607977959853

theorem tailTrace_1386773 : CollatzResearch.WordTrace tailWord_1386773 prefixEnd_1386773 712081107677607977959853 := by
  unfold tailWord_1386773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579766604965737817556973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33719844403310491878371315 50579766604965737817556973)
  ·
    refine ⟨18967412476862151681583865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50579766604965737817556973 18967412476862151681583865)
    ·
      refine ⟨14225559357646613761187899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18967412476862151681583865 14225559357646613761187899)
      ·
        refine ⟨21338339036469920641781849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14225559357646613761187899 21338339036469920641781849)
        ·
          refine ⟨16003754277352440481336387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21338339036469920641781849 16003754277352440481336387)
          ·
            refine ⟨24005631416028660722004581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16003754277352440481336387 24005631416028660722004581)
            ·
              refine ⟨4501055890505373885375859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24005631416028660722004581 4501055890505373885375859)
              ·
                refine ⟨6751583835758060828063789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501055890505373885375859 6751583835758060828063789)
                ·
                  refine ⟨2531843938409272810523921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6751583835758060828063789 2531843938409272810523921)
                  ·
                    refine ⟨1898882953806954607892941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2531843938409272810523921 1898882953806954607892941)
                    ·
                      refine ⟨712081107677607977959853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1898882953806954607892941 712081107677607977959853)
                      ·
                        rfl

theorem cell23_1386773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1386773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386773 prefixEnd_1386773 := by exact prefixLift 1386773
  have htrace : WordTrace (prefixWord ++ tailWord_1386773) baseStart_1386773 baseEnd_1386773 := by
    simpa [prefixWord, tailWord_1386773, baseEnd_1386773] using wordTrace_append hprefix tailTrace_1386773
  have hstable : (prefixWord ++ tailWord_1386773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386773).length < 2 ^ (prefixWord ++ tailWord_1386773).sum := by decide
  have hdescent : baseEnd_1386773 < baseStart_1386773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386783 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1386783 : Nat := 118140960795 + 1386783 * 2 ^ 59
def prefixEnd_1386783 : Nat := 4983230072969 + 3 ^ 40 * 1386783 * 2
def baseEnd_1386783 : Nat := 712086242484152938834807

theorem tailTrace_1386783 : CollatzResearch.WordTrace tailWord_1386783 prefixEnd_1386783 712086242484152938834807 := by
  unfold tailWord_1386783
  simp only [CollatzResearch.WordTrace]
  refine ⟨50580131334929509525421003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33720087556619673016947335 50580131334929509525421003)
  ·
    refine ⟨75870197002394264288131505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50580131334929509525421003 75870197002394264288131505)
    ·
      refine ⟨56902647751795698216098629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75870197002394264288131505 56902647751795698216098629)
      ·
        refine ⟨10669246453461693415518493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56902647751795698216098629 10669246453461693415518493)
        ·
          refine ⟨4000967420048135030819435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10669246453461693415518493 4000967420048135030819435)
          ·
            refine ⟨6001451130072202546229153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000967420048135030819435 6001451130072202546229153)
            ·
              refine ⟨4501088347554151909671865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001451130072202546229153 4501088347554151909671865)
              ·
                refine ⟨3375816260665613932253899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501088347554151909671865 3375816260665613932253899)
                ·
                  refine ⟨5063724390998420898380849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375816260665613932253899 5063724390998420898380849)
                  ·
                    refine ⟨3797793293248815673785637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063724390998420898380849 3797793293248815673785637)
                    ·
                      refine ⟨712086242484152938834807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3797793293248815673785637 712086242484152938834807)
                      ·
                        rfl

theorem cell23_1386783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1386783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386783 prefixEnd_1386783 := by exact prefixLift 1386783
  have htrace : WordTrace (prefixWord ++ tailWord_1386783) baseStart_1386783 baseEnd_1386783 := by
    simpa [prefixWord, tailWord_1386783, baseEnd_1386783] using wordTrace_append hprefix tailTrace_1386783
  have hstable : (prefixWord ++ tailWord_1386783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386783).length < 2 ^ (prefixWord ++ tailWord_1386783).sum := by decide
  have hdescent : baseEnd_1386783 < baseStart_1386783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386797 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1386797 : Nat := 118140960795 + 1386797 * 2 ^ 59
def prefixEnd_1386797 : Nat := 4983230072969 + 3 ^ 40 * 1386797 * 2
def baseEnd_1386797 : Nat := 237364477071105294686581

theorem tailTrace_1386797 : CollatzResearch.WordTrace tailWord_1386797 prefixEnd_1386797 237364477071105294686581 := by
  unfold tailWord_1386797
  simp only [CollatzResearch.WordTrace]
  refine ⟨50580641956878789916430645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33720427971252526610953763 50580641956878789916430645)
  ·
    refine ⟨4741935183457386554665373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50580641956878789916430645 4741935183457386554665373)
    ·
      refine ⟨1778225693796519957999515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4741935183457386554665373 1778225693796519957999515)
      ·
        refine ⟨2667338540694779936999273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778225693796519957999515 2667338540694779936999273)
        ·
          refine ⟨2000503905521084952749455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2667338540694779936999273 2000503905521084952749455)
          ·
            refine ⟨3000755858281627429124183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000503905521084952749455 3000755858281627429124183)
            ·
              refine ⟨4501133787422441143686275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000755858281627429124183 4501133787422441143686275)
              ·
                refine ⟨6751700681133661715529413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501133787422441143686275 6751700681133661715529413)
                ·
                  refine ⟨1265943877712561571661765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6751700681133661715529413 1265943877712561571661765)
                  ·
                    refine ⟨237364477071105294686581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1265943877712561571661765 237364477071105294686581)
                    ·
                      rfl

theorem cell23_1386797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1386797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386797 prefixEnd_1386797 := by exact prefixLift 1386797
  have htrace : WordTrace (prefixWord ++ tailWord_1386797) baseStart_1386797 baseEnd_1386797 := by
    simpa [prefixWord, tailWord_1386797, baseEnd_1386797] using wordTrace_append hprefix tailTrace_1386797
  have hstable : (prefixWord ++ tailWord_1386797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386797).length < 2 ^ (prefixWord ++ tailWord_1386797).sum := by decide
  have hdescent : baseEnd_1386797 < baseStart_1386797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386804 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1386804 : Nat := 118140960795 + 1386804 * 2 ^ 59
def prefixEnd_1386804 : Nat := 4983230072969 + 3 ^ 40 * 1386804 * 2
def baseEnd_1386804 : Nat := 712097025577897356672211

theorem tailTrace_1386804 : CollatzResearch.WordTrace tailWord_1386804 prefixEnd_1386804 712097025577897356672211 := by
  unfold tailWord_1386804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25290448633926715055967733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33720598178568953407956977 25290448633926715055967733)
  ·
    refine ⟨2370979559430629536496975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25290448633926715055967733 2370979559430629536496975)
    ·
      refine ⟨3556469339145944304745463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370979559430629536496975 3556469339145944304745463)
      ·
        refine ⟨5334704008718916457118195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556469339145944304745463 5334704008718916457118195)
        ·
          refine ⟨8002056013078374685677293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334704008718916457118195 8002056013078374685677293)
          ·
            refine ⟨3000771004904390507128985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8002056013078374685677293 3000771004904390507128985)
            ·
              refine ⟨2250578253678292880346739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000771004904390507128985 2250578253678292880346739)
              ·
                refine ⟨3375867380517439320520109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250578253678292880346739 3375867380517439320520109)
                ·
                  refine ⟨1265950267694039745195041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3375867380517439320520109 1265950267694039745195041)
                  ·
                    refine ⟨949462700770529808896281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1265950267694039745195041 949462700770529808896281)
                    ·
                      refine ⟨712097025577897356672211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949462700770529808896281 712097025577897356672211)
                      ·
                        rfl

theorem cell23_1386804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1386804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386804 prefixEnd_1386804 := by exact prefixLift 1386804
  have htrace : WordTrace (prefixWord ++ tailWord_1386804) baseStart_1386804 baseEnd_1386804 := by
    simpa [prefixWord, tailWord_1386804, baseEnd_1386804] using wordTrace_append hprefix tailTrace_1386804
  have hstable : (prefixWord ++ tailWord_1386804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386804).length < 2 ^ (prefixWord ++ tailWord_1386804).sum := by decide
  have hdescent : baseEnd_1386804 < baseStart_1386804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386817 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1386817 : Nat := 118140960795 + 1386817 * 2 ^ 59
def prefixEnd_1386817 : Nat := 4983230072969 + 3 ^ 40 * 1386817 * 2
def baseEnd_1386817 : Nat := 712103700826405805809651

theorem tailTrace_1386817 : CollatzResearch.WordTrace tailWord_1386817 prefixEnd_1386817 712103700826405805809651 := by
  unfold tailWord_1386817
  simp only [CollatzResearch.WordTrace]
  refine ⟨50581371416806333332158705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33720914277870888888105803 50581371416806333332158705)
  ·
    refine ⟨37936028562604749999119029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50581371416806333332158705 37936028562604749999119029)
    ·
      refine ⟨3556502677744195312417409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37936028562604749999119029 3556502677744195312417409)
      ·
        refine ⟨2667377008308146484313057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556502677744195312417409 2667377008308146484313057)
        ·
          refine ⟨2000532756231109863234793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2667377008308146484313057 2000532756231109863234793)
          ·
            refine ⟨1500399567173332397426095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000532756231109863234793 1500399567173332397426095)
            ·
              refine ⟨2250599350759998596139143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500399567173332397426095 2250599350759998596139143)
              ·
                refine ⟨3375899026139997894208715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250599350759998596139143 3375899026139997894208715)
                ·
                  refine ⟨5063848539209996841313073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375899026139997894208715 5063848539209996841313073)
                  ·
                    refine ⟨3797886404407497630984805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5063848539209996841313073 3797886404407497630984805)
                    ·
                      refine ⟨712103700826405805809651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3797886404407497630984805 712103700826405805809651)
                      ·
                        rfl

theorem cell23_1386817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1386817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386817 prefixEnd_1386817 := by exact prefixLift 1386817
  have htrace : WordTrace (prefixWord ++ tailWord_1386817) baseStart_1386817 baseEnd_1386817 := by
    simpa [prefixWord, tailWord_1386817, baseEnd_1386817] using wordTrace_append hprefix tailTrace_1386817
  have hstable : (prefixWord ++ tailWord_1386817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386817).length < 2 ^ (prefixWord ++ tailWord_1386817).sum := by decide
  have hdescent : baseEnd_1386817 < baseStart_1386817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386970 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1386970 : Nat := 118140960795 + 1386970 * 2 ^ 59
def prefixEnd_1386970 : Nat := 4983230072969 + 3 ^ 40 * 1386970 * 2
def baseEnd_1386970 : Nat := 712182263366543707196447

theorem tailTrace_1386970 : CollatzResearch.WordTrace tailWord_1386970 prefixEnd_1386970 712182263366543707196447 := by
  unfold tailWord_1386970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646737946313010115619591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33724634523501360308318909 12646737946313010115619591)
  ·
    refine ⟨18970106919469515173429387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12646737946313010115619591 18970106919469515173429387)
    ·
      refine ⟨28455160379204272760144081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18970106919469515173429387 28455160379204272760144081)
      ·
        refine ⟨21341370284403204570108061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28455160379204272760144081 21341370284403204570108061)
        ·
          refine ⟨8003013856651201713790523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21341370284403204570108061 8003013856651201713790523)
          ·
            refine ⟨12004520784976802570685785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003013856651201713790523 12004520784976802570685785)
            ·
              refine ⟨9003390588732601928014339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12004520784976802570685785 9003390588732601928014339)
              ·
                refine ⟨13505085883098902892021509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9003390588732601928014339 13505085883098902892021509)
                ·
                  refine ⟨2532203603081044292254033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13505085883098902892021509 2532203603081044292254033)
                  ·
                    refine ⟨1899152702310783219190525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2532203603081044292254033 1899152702310783219190525)
                    ·
                      refine ⟨712182263366543707196447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899152702310783219190525 712182263366543707196447)
                      ·
                        rfl

theorem cell23_1386970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1386970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386970 prefixEnd_1386970 := by exact prefixLift 1386970
  have htrace : WordTrace (prefixWord ++ tailWord_1386970) baseStart_1386970 baseEnd_1386970 := by
    simpa [prefixWord, tailWord_1386970, baseEnd_1386970] using wordTrace_append hprefix tailTrace_1386970
  have hstable : (prefixWord ++ tailWord_1386970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386970).length < 2 ^ (prefixWord ++ tailWord_1386970).sum := by decide
  have hdescent : baseEnd_1386970 < baseStart_1386970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386977 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1386977 : Nat := 118140960795 + 1386977 * 2 ^ 59
def prefixEnd_1386977 : Nat := 4983230072969 + 3 ^ 40 * 1386977 * 2
def baseEnd_1386977 : Nat := 237395285910375059936305

theorem tailTrace_1386977 : CollatzResearch.WordTrace tailWord_1386977 prefixEnd_1386977 237395285910375059936305 := by
  unfold tailWord_1386977
  simp only [CollatzResearch.WordTrace]
  refine ⟨50587207096226680657983185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33724804730817787105322123 50587207096226680657983185)
  ·
    refine ⟨37940405322170010493487389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50587207096226680657983185 37940405322170010493487389)
    ·
      refine ⟨14227651995813753935057771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37940405322170010493487389 14227651995813753935057771)
      ·
        refine ⟨21341477993720630902586657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14227651995813753935057771 21341477993720630902586657)
        ·
          refine ⟨16006108495290473176939993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21341477993720630902586657 16006108495290473176939993)
          ·
            refine ⟨12004581371467854882704995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16006108495290473176939993 12004581371467854882704995)
            ·
              refine ⟨18006872057201782324057493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004581371467854882704995 18006872057201782324057493)
              ·
                refine ⟨844072127681333546440195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18006872057201782324057493 844072127681333546440195)
                ·
                  refine ⟨1266108191522000319660293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844072127681333546440195 1266108191522000319660293)
                  ·
                    refine ⟨237395285910375059936305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266108191522000319660293 237395285910375059936305)
                    ·
                      rfl

theorem cell23_1386977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1386977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386977 prefixEnd_1386977 := by exact prefixLift 1386977
  have htrace : WordTrace (prefixWord ++ tailWord_1386977) baseStart_1386977 baseEnd_1386977 := by
    simpa [prefixWord, tailWord_1386977, baseEnd_1386977] using wordTrace_append hprefix tailTrace_1386977
  have hstable : (prefixWord ++ tailWord_1386977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386977).length < 2 ^ (prefixWord ++ tailWord_1386977).sum := by decide
  have hdescent : baseEnd_1386977 < baseStart_1386977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1386993 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1386993 : Nat := 118140960795 + 1386993 * 2 ^ 59
def prefixEnd_1386993 : Nat := 4983230072969 + 3 ^ 40 * 1386993 * 2
def baseEnd_1386993 : Nat := 712194073421597117208841

theorem tailTrace_1386993 : CollatzResearch.WordTrace tailWord_1386993 prefixEnd_1386993 712194073421597117208841 := by
  unfold tailWord_1386993
  simp only [CollatzResearch.WordTrace]
  refine ⟨50587790664168715390565633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33725193776112476927043755 50587790664168715390565633)
  ·
    refine ⟨37940842998126536542924225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50587790664168715390565633 37940842998126536542924225)
    ·
      refine ⟨28455632248594902407193169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37940842998126536542924225 28455632248594902407193169)
      ·
        refine ⟨21341724186446176805394877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28455632248594902407193169 21341724186446176805394877)
        ·
          refine ⟨8003146569917316302023079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21341724186446176805394877 8003146569917316302023079)
          ·
            refine ⟨12004719854875974453034619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003146569917316302023079 12004719854875974453034619)
            ·
              refine ⟨18007079782313961679551929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004719854875974453034619 18007079782313961679551929)
              ·
                refine ⟨13505309836735471259663947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18007079782313961679551929 13505309836735471259663947)
                ·
                  refine ⟨20257964755103206889495921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13505309836735471259663947 20257964755103206889495921)
                  ·
                    refine ⟨15193473566327405167121941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20257964755103206889495921 15193473566327405167121941)
                    ·
                      refine ⟨712194073421597117208841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15193473566327405167121941 712194073421597117208841)
                      ·
                        rfl

theorem cell23_1386993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1386993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1386993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1386993 prefixEnd_1386993 := by exact prefixLift 1386993
  have htrace : WordTrace (prefixWord ++ tailWord_1386993) baseStart_1386993 baseEnd_1386993 := by
    simpa [prefixWord, tailWord_1386993, baseEnd_1386993] using wordTrace_append hprefix tailTrace_1386993
  have hstable : (prefixWord ++ tailWord_1386993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1386993).length < 2 ^ (prefixWord ++ tailWord_1386993).sum := by decide
  have hdescent : baseEnd_1386993 < baseStart_1386993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1386993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387021 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1387021 : Nat := 118140960795 + 1387021 * 2 ^ 59
def prefixEnd_1387021 : Nat := 4983230072969 + 3 ^ 40 * 1387021 * 2
def baseEnd_1387021 : Nat := 712208450879923007658713

theorem tailTrace_1387021 : CollatzResearch.WordTrace tailWord_1387021 prefixEnd_1387021 712208450879923007658713 := by
  unfold tailWord_1387021
  simp only [CollatzResearch.WordTrace]
  refine ⟨50588811908067276172584917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33725874605378184115056611 50588811908067276172584917)
  ·
    refine ⟨1185675279095326785294959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50588811908067276172584917 1185675279095326785294959)
    ·
      refine ⟨1778512918642990177942439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185675279095326785294959 1778512918642990177942439)
      ·
        refine ⟨2667769377964485266913659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778512918642990177942439 2667769377964485266913659)
        ·
          refine ⟨4001654066946727900370489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667769377964485266913659 4001654066946727900370489)
          ·
            refine ⟨3001240550210045925277867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001654066946727900370489 3001240550210045925277867)
            ·
              refine ⟨4501860825315068887916801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001240550210045925277867 4501860825315068887916801)
              ·
                refine ⟨3376395618986301665937601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501860825315068887916801 3376395618986301665937601)
                ·
                  refine ⟨2532296714239726249453201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376395618986301665937601 2532296714239726249453201)
                  ·
                    refine ⟨1899222535679794687089901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2532296714239726249453201 1899222535679794687089901)
                    ·
                      refine ⟨712208450879923007658713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899222535679794687089901 712208450879923007658713)
                      ·
                        rfl

theorem cell23_1387021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1387021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387021 prefixEnd_1387021 := by exact prefixLift 1387021
  have htrace : WordTrace (prefixWord ++ tailWord_1387021) baseStart_1387021 baseEnd_1387021 := by
    simpa [prefixWord, tailWord_1387021, baseEnd_1387021] using wordTrace_append hprefix tailTrace_1387021
  have hstable : (prefixWord ++ tailWord_1387021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387021).length < 2 ^ (prefixWord ++ tailWord_1387021).sum := by decide
  have hdescent : baseEnd_1387021 < baseStart_1387021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387027 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 2, 3, 2]
def baseStart_1387027 : Nat := 118140960795 + 1387027 * 2 ^ 59
def prefixEnd_1387027 : Nat := 4983230072969 + 3 ^ 40 * 1387027 * 2
def baseEnd_1387027 : Nat := 712211531763849984183685

theorem tailTrace_1387027 : CollatzResearch.WordTrace tailWord_1387027 prefixEnd_1387027 712211531763849984183685 := by
  unfold tailWord_1387027
  simp only [CollatzResearch.WordTrace]
  refine ⟨50589030746045539197303335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33726020497363692798202223 50589030746045539197303335)
  ·
    refine ⟨75883546119068308795955003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50589030746045539197303335 75883546119068308795955003)
    ·
      refine ⟨113825319178602463193932505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75883546119068308795955003 113825319178602463193932505)
      ·
        refine ⟨85368989383951847395449379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113825319178602463193932505 85368989383951847395449379)
        ·
          refine ⟨128053484075927771093174069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85368989383951847395449379 128053484075927771093174069)
          ·
            refine ⟨12005014132118228539985069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128053484075927771093174069 12005014132118228539985069)
            ·
              refine ⟨4501880299544335702494401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12005014132118228539985069 4501880299544335702494401)
              ·
                refine ⟨3376410224658251776870801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501880299544335702494401 3376410224658251776870801)
                ·
                  refine ⟨2532307668493688832653101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376410224658251776870801 2532307668493688832653101)
                  ·
                    refine ⟨949615375685133312244913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532307668493688832653101 949615375685133312244913)
                    ·
                      refine ⟨712211531763849984183685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949615375685133312244913 712211531763849984183685)
                      ·
                        rfl

theorem cell23_1387027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3, 2].length) (baseStart_1387027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387027 prefixEnd_1387027 := by exact prefixLift 1387027
  have htrace : WordTrace (prefixWord ++ tailWord_1387027) baseStart_1387027 baseEnd_1387027 := by
    simpa [prefixWord, tailWord_1387027, baseEnd_1387027] using wordTrace_append hprefix tailTrace_1387027
  have hstable : (prefixWord ++ tailWord_1387027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387027).length < 2 ^ (prefixWord ++ tailWord_1387027).sum := by decide
  have hdescent : baseEnd_1387027 < baseStart_1387027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387028 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1387028 : Nat := 118140960795 + 1387028 * 2 ^ 59
def prefixEnd_1387028 : Nat := 4983230072969 + 3 ^ 40 * 1387028 * 2
def baseEnd_1387028 : Nat := 237404015081501493423727

theorem tailTrace_1387028 : CollatzResearch.WordTrace tailWord_1387028 prefixEnd_1387028 237404015081501493423727 := by
  unfold tailWord_1387028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25294533609520958184044869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33726044812694610912059825 25294533609520958184044869)
  ·
    refine ⟨4742725051785179659508413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25294533609520958184044869 4742725051785179659508413)
    ·
      refine ⟨1778521894419442372315655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4742725051785179659508413 1778521894419442372315655)
      ·
        refine ⟨2667782841629163558473483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778521894419442372315655 2667782841629163558473483)
        ·
          refine ⟨4001674262443745337710225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667782841629163558473483 4001674262443745337710225)
          ·
            refine ⟨3001255696832809003282669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001674262443745337710225 3001255696832809003282669)
            ·
              refine ⟨1125470886312303376231001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3001255696832809003282669 1125470886312303376231001)
              ·
                refine ⟨844103164734227532173251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125470886312303376231001 844103164734227532173251)
                ·
                  refine ⟨1266154747101341298259877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844103164734227532173251 1266154747101341298259877)
                  ·
                    refine ⟨237404015081501493423727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266154747101341298259877 237404015081501493423727)
                    ·
                      rfl

theorem cell23_1387028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1387028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387028 prefixEnd_1387028 := by exact prefixLift 1387028
  have htrace : WordTrace (prefixWord ++ tailWord_1387028) baseStart_1387028 baseEnd_1387028 := by
    simpa [prefixWord, tailWord_1387028, baseEnd_1387028] using wordTrace_append hprefix tailTrace_1387028
  have hstable : (prefixWord ++ tailWord_1387028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387028).length < 2 ^ (prefixWord ++ tailWord_1387028).sum := by decide
  have hdescent : baseEnd_1387028 < baseStart_1387028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387033 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_1387033 : Nat := 118140960795 + 1387033 * 2 ^ 59
def prefixEnd_1387033 : Nat := 4983230072969 + 3 ^ 40 * 1387033 * 2
def baseEnd_1387033 : Nat := 237404870882592320236219

theorem tailTrace_1387033 : CollatzResearch.WordTrace tailWord_1387033 prefixEnd_1387033 237404870882592320236219 := by
  unfold tailWord_1387033
  simp only [CollatzResearch.WordTrace]
  refine ⟨50589249584023802222021753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33726166389349201481347835 50589249584023802222021753)
  ·
    refine ⟨37941937188017851666516315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50589249584023802222021753 37941937188017851666516315)
    ·
      refine ⟨56912905782026777499774473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37941937188017851666516315 56912905782026777499774473)
      ·
        refine ⟨42684679336520083124830855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56912905782026777499774473 42684679336520083124830855)
        ·
          refine ⟨64027019004780124687246283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42684679336520083124830855 64027019004780124687246283)
          ·
            refine ⟨96040528507170187030869425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64027019004780124687246283 96040528507170187030869425)
            ·
              refine ⟨72030396380377640273152069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96040528507170187030869425 72030396380377640273152069)
              ·
                refine ⟨13505699321320807551216013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72030396380377640273152069 13505699321320807551216013)
                ·
                  refine ⟨5064637245495302831706005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13505699321320807551216013 5064637245495302831706005)
                  ·
                    refine ⟨237404870882592320236219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5064637245495302831706005 237404870882592320236219)
                    ·
                      rfl

theorem cell23_1387033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_1387033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387033 prefixEnd_1387033 := by exact prefixLift 1387033
  have htrace : WordTrace (prefixWord ++ tailWord_1387033) baseStart_1387033 baseEnd_1387033 := by
    simpa [prefixWord, tailWord_1387033, baseEnd_1387033] using wordTrace_append hprefix tailTrace_1387033
  have hstable : (prefixWord ++ tailWord_1387033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387033).length < 2 ^ (prefixWord ++ tailWord_1387033).sum := by decide
  have hdescent : baseEnd_1387033 < baseStart_1387033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387034 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_1387034 : Nat := 118140960795 + 1387034 * 2 ^ 59
def prefixEnd_1387034 : Nat := 4983230072969 + 3 ^ 40 * 1387034 * 2
def baseEnd_1387034 : Nat := 712215126128431456796153

theorem tailTrace_1387034 : CollatzResearch.WordTrace tailWord_1387034 prefixEnd_1387034 712215126128431456796153 := by
  unfold tailWord_1387034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647321514255044848202039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33726190704680119595205437 12647321514255044848202039)
  ·
    refine ⟨18970982271382567272303059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647321514255044848202039 18970982271382567272303059)
    ·
      refine ⟨28456473407073850908454589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18970982271382567272303059 28456473407073850908454589)
      ·
        refine ⟨10671177527652694090670471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28456473407073850908454589 10671177527652694090670471)
        ·
          refine ⟨16006766291479041136005707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671177527652694090670471 16006766291479041136005707)
          ·
            refine ⟨24010149437218561704008561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16006766291479041136005707 24010149437218561704008561)
            ·
              refine ⟨18007612077913921278006421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24010149437218561704008561 18007612077913921278006421)
              ·
                refine ⟨844106816152215059906551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18007612077913921278006421 844106816152215059906551)
                ·
                  refine ⟨1266160224228322589859827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844106816152215059906551 1266160224228322589859827)
                  ·
                    refine ⟨1899240336342483884789741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266160224228322589859827 1899240336342483884789741)
                    ·
                      refine ⟨712215126128431456796153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899240336342483884789741 712215126128431456796153)
                      ·
                        rfl

theorem cell23_1387034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_1387034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387034 prefixEnd_1387034 := by exact prefixLift 1387034
  have htrace : WordTrace (prefixWord ++ tailWord_1387034) baseStart_1387034 baseEnd_1387034 := by
    simpa [prefixWord, tailWord_1387034, baseEnd_1387034] using wordTrace_append hprefix tailTrace_1387034
  have hstable : (prefixWord ++ tailWord_1387034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387034).length < 2 ^ (prefixWord ++ tailWord_1387034).sum := by decide
  have hdescent : baseEnd_1387034 < baseStart_1387034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387057 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_1387057 : Nat := 118140960795 + 1387057 * 2 ^ 59
def prefixEnd_1387057 : Nat := 4983230072969 + 3 ^ 40 * 1387057 * 2
def baseEnd_1387057 : Nat := 712226936183484866808547

theorem tailTrace_1387057 : CollatzResearch.WordTrace tailWord_1387057 prefixEnd_1387057 712226936183484866808547 := by
  unfold tailWord_1387057
  simp only [CollatzResearch.WordTrace]
  refine ⟨50590124935936854320895425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33726749957291236213930283 50590124935936854320895425)
  ·
    refine ⟨37942593701952640740671569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50590124935936854320895425 37942593701952640740671569)
    ·
      refine ⟨28456945276464480555503677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37942593701952640740671569 28456945276464480555503677)
      ·
        refine ⟨10671354478674180208313879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28456945276464480555503677 10671354478674180208313879)
        ·
          refine ⟨16007031718011270312470819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671354478674180208313879 16007031718011270312470819)
          ·
            refine ⟨24010547577016905468706229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16007031718011270312470819 24010547577016905468706229)
            ·
              refine ⟨2250988835345334887691209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24010547577016905468706229 2250988835345334887691209)
              ·
                refine ⟨1688241626509001165768407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250988835345334887691209 1688241626509001165768407)
                ·
                  refine ⟨2532362439763501748652611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688241626509001165768407 2532362439763501748652611)
                  ·
                    refine ⟨3798543659645252622978917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2532362439763501748652611 3798543659645252622978917)
                    ·
                      refine ⟨712226936183484866808547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3798543659645252622978917 712226936183484866808547)
                      ·
                        rfl

theorem cell23_1387057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_1387057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387057 prefixEnd_1387057 := by exact prefixLift 1387057
  have htrace : WordTrace (prefixWord ++ tailWord_1387057) baseStart_1387057 baseEnd_1387057 := by
    simpa [prefixWord, tailWord_1387057, baseEnd_1387057] using wordTrace_append hprefix tailTrace_1387057
  have hstable : (prefixWord ++ tailWord_1387057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387057).length < 2 ^ (prefixWord ++ tailWord_1387057).sum := by decide
  have hdescent : baseEnd_1387057 < baseStart_1387057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387063 : List Nat := [1, 1, 3, 1, 2, 3, 1, 11]
def baseStart_1387063 : Nat := 118140960795 + 1387063 * 2 ^ 59
def prefixEnd_1387063 : Nat := 4983230072969 + 3 ^ 40 * 1387063 * 2
def baseEnd_1387063 : Nat := 26378889521015253456797

theorem tailTrace_1387063 : CollatzResearch.WordTrace tailWord_1387063 prefixEnd_1387063 26378889521015253456797 := by
  unfold tailWord_1387063
  simp only [CollatzResearch.WordTrace]
  refine ⟨50590343773915117345613843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33726895849276744897075895 50590343773915117345613843)
  ·
    refine ⟨75885515660872676018420765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50590343773915117345613843 75885515660872676018420765)
    ·
      refine ⟨28457068372827253506907787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75885515660872676018420765 28457068372827253506907787)
      ·
        refine ⟨42685602559240880260361681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28457068372827253506907787 42685602559240880260361681)
        ·
          refine ⟨32014201919430660195271261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42685602559240880260361681 32014201919430660195271261)
          ·
            refine ⟨12005325719786497573226723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32014201919430660195271261 12005325719786497573226723)
            ·
              refine ⟨18007988579679746359840085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005325719786497573226723 18007988579679746359840085)
              ·
                refine ⟨26378889521015253456797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18007988579679746359840085 26378889521015253456797)
                ·
                  rfl

theorem cell23_1387063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 11].length) (baseStart_1387063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387063 prefixEnd_1387063 := by exact prefixLift 1387063
  have htrace : WordTrace (prefixWord ++ tailWord_1387063) baseStart_1387063 baseEnd_1387063 := by
    simpa [prefixWord, tailWord_1387063, baseEnd_1387063] using wordTrace_append hprefix tailTrace_1387063
  have hstable : (prefixWord ++ tailWord_1387063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387063).length < 2 ^ (prefixWord ++ tailWord_1387063).sum := by decide
  have hdescent : baseEnd_1387063 < baseStart_1387063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387077 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_1387077 : Nat := 118140960795 + 1387077 * 2 ^ 59
def prefixEnd_1387077 : Nat := 4983230072969 + 3 ^ 40 * 1387077 * 2
def baseEnd_1387077 : Nat := 712237205796574788558455

theorem tailTrace_1387077 : CollatzResearch.WordTrace tailWord_1387077 prefixEnd_1387077 712237205796574788558455 := by
  unfold tailWord_1387077
  simp only [CollatzResearch.WordTrace]
  refine ⟨50590854395864397736623485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33727236263909598491082323 50590854395864397736623485)
  ·
    refine ⟨18971570398449149151233807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50590854395864397736623485 18971570398449149151233807)
    ·
      refine ⟨28457355597673723726850711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18971570398449149151233807 28457355597673723726850711)
      ·
        refine ⟨42686033396510585590276067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28457355597673723726850711 42686033396510585590276067)
        ·
          refine ⟨64029050094765878385414101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42686033396510585590276067 64029050094765878385414101)
          ·
            refine ⟨1500680861596075274658143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64029050094765878385414101 1500680861596075274658143)
            ·
              refine ⟨2251021292394112911987215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500680861596075274658143 2251021292394112911987215)
              ·
                refine ⟨3376531938591169367980823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251021292394112911987215 3376531938591169367980823)
                ·
                  refine ⟨5064797907886754051971235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376531938591169367980823 5064797907886754051971235)
                  ·
                    refine ⟨7597196861830131077956853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5064797907886754051971235 7597196861830131077956853)
                    ·
                      refine ⟨712237205796574788558455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7597196861830131077956853 712237205796574788558455)
                      ·
                        rfl

theorem cell23_1387077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_1387077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387077 prefixEnd_1387077 := by exact prefixLift 1387077
  have htrace : WordTrace (prefixWord ++ tailWord_1387077) baseStart_1387077 baseEnd_1387077 := by
    simpa [prefixWord, tailWord_1387077, baseEnd_1387077] using wordTrace_append hprefix tailTrace_1387077
  have hstable : (prefixWord ++ tailWord_1387077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387077).length < 2 ^ (prefixWord ++ tailWord_1387077).sum := by decide
  have hdescent : baseEnd_1387077 < baseStart_1387077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387085 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1387085 : Nat := 118140960795 + 1387085 * 2 ^ 59
def prefixEnd_1387085 : Nat := 4983230072969 + 3 ^ 40 * 1387085 * 2
def baseEnd_1387085 : Nat := 712241313641810757258419

theorem tailTrace_1387085 : CollatzResearch.WordTrace tailWord_1387085 prefixEnd_1387085 712241313641810757258419 := by
  unfold tailWord_1387085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591146179835415102914709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33727430786556943401943139 50591146179835415102914709)
  ·
    refine ⟨2371459977179785082949127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50591146179835415102914709 2371459977179785082949127)
    ·
      refine ⟨3557189965769677624423691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371459977179785082949127 3557189965769677624423691)
      ·
        refine ⟨5335784948654516436635537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557189965769677624423691 5335784948654516436635537)
        ·
          refine ⟨4001838711490887327476653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5335784948654516436635537 4001838711490887327476653)
          ·
            refine ⟨1500689516809082747803745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4001838711490887327476653 1500689516809082747803745)
            ·
              refine ⟨1125517137606812060852809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500689516809082747803745 1125517137606812060852809)
              ·
                refine ⟨844137853205109045639607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125517137606812060852809 844137853205109045639607)
                ·
                  refine ⟨1266206779807663568459411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844137853205109045639607 1266206779807663568459411)
                  ·
                    refine ⟨1899310169711495352689117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266206779807663568459411 1899310169711495352689117)
                    ·
                      refine ⟨712241313641810757258419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899310169711495352689117 712241313641810757258419)
                      ·
                        rfl

theorem cell23_1387085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1387085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387085 prefixEnd_1387085 := by exact prefixLift 1387085
  have htrace : WordTrace (prefixWord ++ tailWord_1387085) baseStart_1387085 baseEnd_1387085 := by
    simpa [prefixWord, tailWord_1387085, baseEnd_1387085] using wordTrace_append hprefix tailTrace_1387085
  have hstable : (prefixWord ++ tailWord_1387085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387085).length < 2 ^ (prefixWord ++ tailWord_1387085).sum := by decide
  have hdescent : baseEnd_1387085 < baseStart_1387085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387107 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1387107 : Nat := 118140960795 + 1387107 * 2 ^ 59
def prefixEnd_1387107 : Nat := 4983230072969 + 3 ^ 40 * 1387107 * 2
def baseEnd_1387107 : Nat := 712252610216209671183317

theorem tailTrace_1387107 : CollatzResearch.WordTrace tailWord_1387107 prefixEnd_1387107 712252610216209671183317 := by
  unfold tailWord_1387107
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591948585755712860215575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33727965723837141906810383 50591948585755712860215575)
  ·
    refine ⟨75887922878633569290323363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50591948585755712860215575 75887922878633569290323363)
    ·
      refine ⟨113831884317950353935485045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75887922878633569290323363 113831884317950353935485045)
      ·
        refine ⟨10671739154807845681451723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113831884317950353935485045 10671739154807845681451723)
        ·
          refine ⟨16007608732211768522177585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671739154807845681451723 16007608732211768522177585)
          ·
            refine ⟨12005706549158826391633189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16007608732211768522177585 12005706549158826391633189)
            ·
              refine ⟨2251069977967279948431223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12005706549158826391633189 2251069977967279948431223)
              ·
                refine ⟨3376604966950919922646835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251069977967279948431223 3376604966950919922646835)
                ·
                  refine ⟨5064907450426379883970253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376604966950919922646835 5064907450426379883970253)
                  ·
                    refine ⟨1899340293909892456488845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5064907450426379883970253 1899340293909892456488845)
                    ·
                      refine ⟨712252610216209671183317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899340293909892456488845 712252610216209671183317)
                      ·
                        rfl

theorem cell23_1387107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1387107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387107 prefixEnd_1387107 := by exact prefixLift 1387107
  have htrace : WordTrace (prefixWord ++ tailWord_1387107) baseStart_1387107 baseEnd_1387107 := by
    simpa [prefixWord, tailWord_1387107, baseEnd_1387107] using wordTrace_append hprefix tailTrace_1387107
  have hstable : (prefixWord ++ tailWord_1387107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387107).length < 2 ^ (prefixWord ++ tailWord_1387107).sum := by decide
  have hdescent : baseEnd_1387107 < baseStart_1387107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387125 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1387125 : Nat := 118140960795 + 1387125 * 2 ^ 59
def prefixEnd_1387125 : Nat := 4983230072969 + 3 ^ 40 * 1387125 * 2
def baseEnd_1387125 : Nat := 712261852867990600758235

theorem tailTrace_1387125 : CollatzResearch.WordTrace tailWord_1387125 prefixEnd_1387125 712261852867990600758235 := by
  unfold tailWord_1387125
  simp only [CollatzResearch.WordTrace]
  refine ⟨50592605099690501934370829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33728403399793667956247219 50592605099690501934370829)
  ·
    refine ⟨18972226912383938225389061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50592605099690501934370829 18972226912383938225389061)
    ·
      refine ⟨3557292546071988417260449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18972226912383938225389061 3557292546071988417260449)
      ·
        refine ⟨2667969409553991312945337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3557292546071988417260449 2667969409553991312945337)
        ·
          refine ⟨2000977057165493484709003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2667969409553991312945337 2000977057165493484709003)
          ·
            refine ⟨3001465585748240227063505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000977057165493484709003 3001465585748240227063505)
            ·
              refine ⟨2251099189311180170297629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001465585748240227063505 2251099189311180170297629)
              ·
                refine ⟨844162195991692563861611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251099189311180170297629 844162195991692563861611)
                ·
                  refine ⟨1266243293987538845792417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844162195991692563861611 1266243293987538845792417)
                  ·
                    refine ⟨949682470490654134344313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266243293987538845792417 949682470490654134344313)
                    ·
                      refine ⟨712261852867990600758235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949682470490654134344313 712261852867990600758235)
                      ·
                        rfl

theorem cell23_1387125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1387125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387125 prefixEnd_1387125 := by exact prefixLift 1387125
  have htrace : WordTrace (prefixWord ++ tailWord_1387125) baseStart_1387125 baseEnd_1387125 := by
    simpa [prefixWord, tailWord_1387125, baseEnd_1387125] using wordTrace_append hprefix tailTrace_1387125
  have hstable : (prefixWord ++ tailWord_1387125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387125).length < 2 ^ (prefixWord ++ tailWord_1387125).sum := by decide
  have hdescent : baseEnd_1387125 < baseStart_1387125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387141 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_1387141 : Nat := 118140960795 + 1387141 * 2 ^ 59
def prefixEnd_1387141 : Nat := 4983230072969 + 3 ^ 40 * 1387141 * 2
def baseEnd_1387141 : Nat := 712270068558462538158161

theorem tailTrace_1387141 : CollatzResearch.WordTrace tailWord_1387141 prefixEnd_1387141 712270068558462538158161 := by
  unfold tailWord_1387141
  simp only [CollatzResearch.WordTrace]
  refine ⟨50593188667632536666953277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33728792445088357777968851 50593188667632536666953277)
  ·
    refine ⟨18972445750362201250107479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50593188667632536666953277 18972445750362201250107479)
    ·
      refine ⟨28458668625543301875161219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18972445750362201250107479 28458668625543301875161219)
      ·
        refine ⟨42688002938314952812741829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28458668625543301875161219 42688002938314952812741829)
        ·
          refine ⟨8004000550934053652389093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42688002938314952812741829 8004000550934053652389093)
          ·
            refine ⟨1500750103300135059822955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8004000550934053652389093 1500750103300135059822955)
            ·
              refine ⟨2251125154950202589734433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500750103300135059822955 2251125154950202589734433)
              ·
                refine ⟨1688343866212651942300825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251125154950202589734433 1688343866212651942300825)
                ·
                  refine ⟨1266257899659488956725619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688343866212651942300825 1266257899659488956725619)
                  ·
                    refine ⟨1899386849489233435088429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266257899659488956725619 1899386849489233435088429)
                    ·
                      refine ⟨712270068558462538158161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899386849489233435088429 712270068558462538158161)
                      ·
                        rfl

theorem cell23_1387141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_1387141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387141 prefixEnd_1387141 := by exact prefixLift 1387141
  have htrace : WordTrace (prefixWord ++ tailWord_1387141) baseStart_1387141 baseEnd_1387141 := by
    simpa [prefixWord, tailWord_1387141, baseEnd_1387141] using wordTrace_append hprefix tailTrace_1387141
  have hstable : (prefixWord ++ tailWord_1387141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387141).length < 2 ^ (prefixWord ++ tailWord_1387141).sum := by decide
  have hdescent : baseEnd_1387141 < baseStart_1387141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387181 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1387181 : Nat := 118140960795 + 1387181 * 2 ^ 59
def prefixEnd_1387181 : Nat := 4983230072969 + 3 ^ 40 * 1387181 * 2
def baseEnd_1387181 : Nat := 712290607784642381657977

theorem tailTrace_1387181 : CollatzResearch.WordTrace tailWord_1387181 prefixEnd_1387181 712290607784642381657977 := by
  unfold tailWord_1387181
  simp only [CollatzResearch.WordTrace]
  refine ⟨50594647587487623498409397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33729765058325082332272931 50594647587487623498409397)
  ·
    refine ⟨4743248211326964702975881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50594647587487623498409397 4743248211326964702975881)
    ·
      refine ⟨3557436158495223527231911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4743248211326964702975881 3557436158495223527231911)
      ·
        refine ⟨5336154237742835290847867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557436158495223527231911 5336154237742835290847867)
        ·
          refine ⟨8004231356614252936271801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336154237742835290847867 8004231356614252936271801)
          ·
            refine ⟨6003173517460689702203851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8004231356614252936271801 6003173517460689702203851)
            ·
              refine ⟨9004760276191034553305777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003173517460689702203851 9004760276191034553305777)
              ·
                refine ⟨6753570207143275914979333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9004760276191034553305777 6753570207143275914979333)
                ·
                  refine ⟨1266294413839364234058625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6753570207143275914979333 1266294413839364234058625)
                  ·
                    refine ⟨949720810379523175543969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266294413839364234058625 949720810379523175543969)
                    ·
                      refine ⟨712290607784642381657977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949720810379523175543969 712290607784642381657977)
                      ·
                        rfl

theorem cell23_1387181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1387181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387181 prefixEnd_1387181 := by exact prefixLift 1387181
  have htrace : WordTrace (prefixWord ++ tailWord_1387181) baseStart_1387181 baseEnd_1387181 := by
    simpa [prefixWord, tailWord_1387181, baseEnd_1387181] using wordTrace_append hprefix tailTrace_1387181
  have hstable : (prefixWord ++ tailWord_1387181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387181).length < 2 ^ (prefixWord ++ tailWord_1387181).sum := by decide
  have hdescent : baseEnd_1387181 < baseStart_1387181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387204 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1387204 : Nat := 118140960795 + 1387204 * 2 ^ 59
def prefixEnd_1387204 : Nat := 4983230072969 + 3 ^ 40 * 1387204 * 2
def baseEnd_1387204 : Nat := 79144713093299532407819

theorem tailTrace_1387204 : CollatzResearch.WordTrace tailWord_1387204 prefixEnd_1387204 79144713093299532407819 := by
  unfold tailWord_1387204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25297743233202149213248333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33730324310936198950997777 25297743233202149213248333)
  ·
    refine ⟨9486653712450805954968125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25297743233202149213248333 9486653712450805954968125)
    ·
      refine ⟨3557495142169052233113047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9486653712450805954968125 3557495142169052233113047)
      ·
        refine ⟨5336242713253578349669571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557495142169052233113047 5336242713253578349669571)
        ·
          refine ⟨8004364069880367524504357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336242713253578349669571 8004364069880367524504357)
          ·
            refine ⟨1500818263102568910844567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8004364069880367524504357 1500818263102568910844567)
            ·
              refine ⟨2251227394653853366266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500818263102568910844567 2251227394653853366266851)
              ·
                refine ⟨3376841091980780049400277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251227394653853366266851 3376841091980780049400277)
                ·
                  refine ⟨79144713093299532407819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3376841091980780049400277 79144713093299532407819)
                  ·
                    rfl

theorem cell23_1387204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1387204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387204 prefixEnd_1387204 := by exact prefixLift 1387204
  have htrace : WordTrace (prefixWord ++ tailWord_1387204) baseStart_1387204 baseEnd_1387204 := by
    simpa [prefixWord, tailWord_1387204, baseEnd_1387204] using wordTrace_append hprefix tailTrace_1387204
  have hstable : (prefixWord ++ tailWord_1387204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387204).length < 2 ^ (prefixWord ++ tailWord_1387204).sum := by decide
  have hdescent : baseEnd_1387204 < baseStart_1387204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387254 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1387254 : Nat := 118140960795 + 1387254 * 2 ^ 59
def prefixEnd_1387254 : Nat := 4983230072969 + 3 ^ 40 * 1387254 * 2
def baseEnd_1387254 : Nat := 712328091872420596045141

theorem tailTrace_1387254 : CollatzResearch.WordTrace tailWord_1387254 prefixEnd_1387254 712328091872420596045141 := by
  unfold tailWord_1387254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162331882263947310363551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33731540077482104643877877 3162331882263947310363551)
  ·
    refine ⟨4743497823395920965545327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162331882263947310363551 4743497823395920965545327)
    ·
      refine ⟨7115246735093881448317991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743497823395920965545327 7115246735093881448317991)
      ·
        refine ⟨10672870102640822172476987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115246735093881448317991 10672870102640822172476987)
        ·
          refine ⟨16009305153961233258715481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10672870102640822172476987 16009305153961233258715481)
          ·
            refine ⟨12006978865470924944036611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16009305153961233258715481 12006978865470924944036611)
            ·
              refine ⟨18010468298206387416054917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12006978865470924944036611 18010468298206387416054917)
              ·
                refine ⟨3376962805913697640510297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18010468298206387416054917 3376962805913697640510297)
                ·
                  refine ⟨2532722104435273230382723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376962805913697640510297 2532722104435273230382723)
                  ·
                    refine ⟨3799083156652909845574085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2532722104435273230382723 3799083156652909845574085)
                    ·
                      refine ⟨712328091872420596045141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3799083156652909845574085 712328091872420596045141)
                      ·
                        rfl

theorem cell23_1387254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1387254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387254 prefixEnd_1387254 := by exact prefixLift 1387254
  have htrace : WordTrace (prefixWord ++ tailWord_1387254) baseStart_1387254 baseEnd_1387254 := by
    simpa [prefixWord, tailWord_1387254, baseEnd_1387254] using wordTrace_append hprefix tailTrace_1387254
  have hstable : (prefixWord ++ tailWord_1387254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387254).length < 2 ^ (prefixWord ++ tailWord_1387254).sum := by decide
  have hdescent : baseEnd_1387254 < baseStart_1387254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387271 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1387271 : Nat := 118140960795 + 1387271 * 2 ^ 59
def prefixEnd_1387271 : Nat := 4983230072969 + 3 ^ 40 * 1387271 * 2
def baseEnd_1387271 : Nat := 712336821043547029532563

theorem tailTrace_1387271 : CollatzResearch.WordTrace tailWord_1387271 prefixEnd_1387271 712336821043547029532563 := by
  unfold tailWord_1387271
  simp only [CollatzResearch.WordTrace]
  refine ⟨50597930157161568869185667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33731953438107712579457111 50597930157161568869185667)
  ·
    refine ⟨75896895235742353303778501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50597930157161568869185667 75896895235742353303778501)
    ·
      refine ⟨14230667856701691244458469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75896895235742353303778501 14230667856701691244458469)
      ·
        refine ⟨2668250223131567108335963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14230667856701691244458469 2668250223131567108335963)
        ·
          refine ⟨4002375334697350662503945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668250223131567108335963 4002375334697350662503945)
          ·
            refine ⟨3001781501023012996877959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002375334697350662503945 3001781501023012996877959)
            ·
              refine ⟨4502672251534519495316939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001781501023012996877959 4502672251534519495316939)
              ·
                refine ⟨6754008377301779242975409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502672251534519495316939 6754008377301779242975409)
                ·
                  refine ⟨5065506282976334432231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6754008377301779242975409 5065506282976334432231557)
                  ·
                    refine ⟨949782428058062706043417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065506282976334432231557 949782428058062706043417)
                    ·
                      refine ⟨712336821043547029532563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949782428058062706043417 712336821043547029532563)
                      ·
                        rfl

theorem cell23_1387271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1387271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387271 prefixEnd_1387271 := by exact prefixLift 1387271
  have htrace : WordTrace (prefixWord ++ tailWord_1387271) baseStart_1387271 baseEnd_1387271 := by
    simpa [prefixWord, tailWord_1387271, baseEnd_1387271] using wordTrace_append hprefix tailTrace_1387271
  have hstable : (prefixWord ++ tailWord_1387271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387271).length < 2 ^ (prefixWord ++ tailWord_1387271).sum := by decide
  have hdescent : baseEnd_1387271 < baseStart_1387271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387298 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1387298 : Nat := 118140960795 + 1387298 * 2 ^ 59
def prefixEnd_1387298 : Nat := 4983230072969 + 3 ^ 40 * 1387298 * 2
def baseEnd_1387298 : Nat := 237450228340406141298313

theorem tailTrace_1387298 : CollatzResearch.WordTrace tailWord_1387298 prefixEnd_1387298 237450228340406141298313 := by
  unfold tailWord_1387298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12649728732015938120104637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33732609952042501653612365 12649728732015938120104637)
  ·
    refine ⟨4743648274505976795039239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12649728732015938120104637 4743648274505976795039239)
    ·
      refine ⟨7115472411758965192558859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743648274505976795039239 7115472411758965192558859)
      ·
        refine ⟨10673208617638447788838289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115472411758965192558859 10673208617638447788838289)
        ·
          refine ⟨8004906463228835841628717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10673208617638447788838289 8004906463228835841628717)
          ·
            refine ⟨3001839923710813440610769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8004906463228835841628717 3001839923710813440610769)
            ·
              refine ⟨2251379942783110080458077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001839923710813440610769 2251379942783110080458077)
              ·
                refine ⟨844267478543666280171779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251379942783110080458077 844267478543666280171779)
                ·
                  refine ⟨1266401217815499420257669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844267478543666280171779 1266401217815499420257669)
                  ·
                    refine ⟨237450228340406141298313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266401217815499420257669 237450228340406141298313)
                    ·
                      rfl

theorem cell23_1387298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1387298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387298 prefixEnd_1387298 := by exact prefixLift 1387298
  have htrace : WordTrace (prefixWord ++ tailWord_1387298) baseStart_1387298 baseEnd_1387298 := by
    simpa [prefixWord, tailWord_1387298, baseEnd_1387298] using wordTrace_append hprefix tailTrace_1387298
  have hstable : (prefixWord ++ tailWord_1387298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387298).length < 2 ^ (prefixWord ++ tailWord_1387298).sum := by decide
  have hdescent : baseEnd_1387298 < baseStart_1387298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387344 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_1387344 : Nat := 118140960795 + 1387344 * 2 ^ 59
def prefixEnd_1387344 : Nat := 4983230072969 + 3 ^ 40 * 1387344 * 2
def baseEnd_1387344 : Nat := 712374305131325243919727

theorem tailTrace_1387344 : CollatzResearch.WordTrace tailWord_1387344 prefixEnd_1387344 712374305131325243919727 := by
  unfold tailWord_1387344
  simp only [CollatzResearch.WordTrace]
  refine ⟨25300296342948551168296543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33733728457264734891062057 25300296342948551168296543)
  ·
    refine ⟨37950444514422826752444815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25300296342948551168296543 37950444514422826752444815)
    ·
      refine ⟨56925666771634240128667223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37950444514422826752444815 56925666771634240128667223)
      ·
        refine ⟨85388500157451360193000835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56925666771634240128667223 85388500157451360193000835)
        ·
          refine ⟨128082750236177040289501253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85388500157451360193000835 128082750236177040289501253)
          ·
            refine ⟨24015515669283195054281485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128082750236177040289501253 24015515669283195054281485)
            ·
              refine ⟨9005818375981198145355557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24015515669283195054281485 9005818375981198145355557)
              ·
                refine ⟨1688590945496474652254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9005818375981198145355557 1688590945496474652254167)
                ·
                  refine ⟨2532886418244711978381251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688590945496474652254167 2532886418244711978381251)
                  ·
                    refine ⟨3799329627367067967571877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2532886418244711978381251 3799329627367067967571877)
                    ·
                      refine ⟨712374305131325243919727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3799329627367067967571877 712374305131325243919727)
                      ·
                        rfl

theorem cell23_1387344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_1387344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387344 prefixEnd_1387344 := by exact prefixLift 1387344
  have htrace : WordTrace (prefixWord ++ tailWord_1387344) baseStart_1387344 baseEnd_1387344 := by
    simpa [prefixWord, tailWord_1387344, baseEnd_1387344] using wordTrace_append hprefix tailTrace_1387344
  have hstable : (prefixWord ++ tailWord_1387344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387344).length < 2 ^ (prefixWord ++ tailWord_1387344).sum := by decide
  have hdescent : baseEnd_1387344 < baseStart_1387344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387347 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3]
def baseStart_1387347 : Nat := 118140960795 + 1387347 * 2 ^ 59
def prefixEnd_1387347 : Nat := 4983230072969 + 3 ^ 40 * 1387347 * 2
def baseEnd_1387347 : Nat := 712375845573288732182213

theorem tailTrace_1387347 : CollatzResearch.WordTrace tailWord_1387347 prefixEnd_1387347 712375845573288732182213 := by
  unfold tailWord_1387347
  simp only [CollatzResearch.WordTrace]
  refine ⟨50600702104886233848952295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33733801403257489232634863 50600702104886233848952295)
  ·
    refine ⟨75901053157329350773428443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50600702104886233848952295 75901053157329350773428443)
    ·
      refine ⟨113851579735994026160142665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75901053157329350773428443 113851579735994026160142665)
      ·
        refine ⟨85388684801995519620106999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113851579735994026160142665 85388684801995519620106999)
        ·
          refine ⟨128083027202993279430160499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85388684801995519620106999 128083027202993279430160499)
          ·
            refine ⟨192124540804489919145240749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128083027202993279430160499 192124540804489919145240749)
            ·
              refine ⟨72046702801683719679465281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192124540804489919145240749 72046702801683719679465281)
              ·
                refine ⟨54035027101262789759598961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72046702801683719679465281 54035027101262789759598961)
                ·
                  refine ⟨40526270325947092319699221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54035027101262789759598961 40526270325947092319699221)
                  ·
                    refine ⟨1899668921528769952485901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40526270325947092319699221 1899668921528769952485901)
                    ·
                      refine ⟨712375845573288732182213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899668921528769952485901 712375845573288732182213)
                      ·
                        rfl

theorem cell23_1387347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_1387347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387347 prefixEnd_1387347 := by exact prefixLift 1387347
  have htrace : WordTrace (prefixWord ++ tailWord_1387347) baseStart_1387347 baseEnd_1387347 := by
    simpa [prefixWord, tailWord_1387347, baseEnd_1387347] using wordTrace_append hprefix tailTrace_1387347
  have hstable : (prefixWord ++ tailWord_1387347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387347).length < 2 ^ (prefixWord ++ tailWord_1387347).sum := by decide
  have hdescent : baseEnd_1387347 < baseStart_1387347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387354 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_1387354 : Nat := 118140960795 + 1387354 * 2 ^ 59
def prefixEnd_1387354 : Nat := 4983230072969 + 3 ^ 40 * 1387354 * 2
def baseEnd_1387354 : Nat := 237459813312623401598227

theorem tailTrace_1387354 : CollatzResearch.WordTrace tailWord_1387354 prefixEnd_1387354 237459813312623401598227 := by
  unfold tailWord_1387354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650239353965218511114279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33733971610573916029638077 12650239353965218511114279)
  ·
    refine ⟨18975359030947827766671419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12650239353965218511114279 18975359030947827766671419)
    ·
      refine ⟨28463038546421741650007129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18975359030947827766671419 28463038546421741650007129)
      ·
        refine ⟨21347278909816306237505347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28463038546421741650007129 21347278909816306237505347)
        ·
          refine ⟨32020918364724459356258021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21347278909816306237505347 32020918364724459356258021)
          ·
            refine ⟨6003922193385836129298379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32020918364724459356258021 6003922193385836129298379)
            ·
              refine ⟨9005883290078754193947569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003922193385836129298379 9005883290078754193947569)
              ·
                refine ⟨6754412467559065645460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9005883290078754193947569 6754412467559065645460677)
                ·
                  refine ⟨1266452337667324808523877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6754412467559065645460677 1266452337667324808523877)
                  ·
                    refine ⟨237459813312623401598227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266452337667324808523877 237459813312623401598227)
                    ·
                      rfl

theorem cell23_1387354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_1387354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387354 prefixEnd_1387354 := by exact prefixLift 1387354
  have htrace : WordTrace (prefixWord ++ tailWord_1387354) baseStart_1387354 baseEnd_1387354 := by
    simpa [prefixWord, tailWord_1387354, baseEnd_1387354] using wordTrace_append hprefix tailTrace_1387354
  have hstable : (prefixWord ++ tailWord_1387354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387354).length < 2 ^ (prefixWord ++ tailWord_1387354).sum := by decide
  have hdescent : baseEnd_1387354 < baseStart_1387354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387364 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_1387364 : Nat := 118140960795 + 1387364 * 2 ^ 59
def prefixEnd_1387364 : Nat := 4983230072969 + 3 ^ 40 * 1387364 * 2
def baseEnd_1387364 : Nat := 712384574744415165669635

theorem tailTrace_1387364 : CollatzResearch.WordTrace tailWord_1387364 prefixEnd_1387364 712384574744415165669635 := by
  unfold tailWord_1387364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25300661072912322876160573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33734214763883097168214097 25300661072912322876160573)
  ·
    refine ⟨9487747902342121078560215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25300661072912322876160573 9487747902342121078560215)
    ·
      refine ⟨14231621853513181617840323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9487747902342121078560215 14231621853513181617840323)
      ·
        refine ⟨21347432780269772426760485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14231621853513181617840323 21347432780269772426760485)
        ·
          refine ⟨4002643646300582330017591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21347432780269772426760485 4002643646300582330017591)
          ·
            refine ⟨6003965469450873495026387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002643646300582330017591 6003965469450873495026387)
            ·
              refine ⟨9005948204176310242539581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003965469450873495026387 9005948204176310242539581)
              ·
                refine ⟨3377230576566116340952343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9005948204176310242539581 3377230576566116340952343)
                ·
                  refine ⟨5065845864849174511428515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377230576566116340952343 5065845864849174511428515)
                  ·
                    refine ⟨7598768797273761767142773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5065845864849174511428515 7598768797273761767142773)
                    ·
                      refine ⟨712384574744415165669635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7598768797273761767142773 712384574744415165669635)
                      ·
                        rfl

theorem cell23_1387364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_1387364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387364 prefixEnd_1387364 := by exact prefixLift 1387364
  have htrace : WordTrace (prefixWord ++ tailWord_1387364) baseStart_1387364 baseEnd_1387364 := by
    simpa [prefixWord, tailWord_1387364, baseEnd_1387364] using wordTrace_append hprefix tailTrace_1387364
  have hstable : (prefixWord ++ tailWord_1387364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387364).length < 2 ^ (prefixWord ++ tailWord_1387364).sum := by decide
  have hdescent : baseEnd_1387364 < baseStart_1387364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387367 : List Nat := [1, 1, 5, 1, 2, 2, 11]
def baseStart_1387367 : Nat := 118140960795 + 1387367 * 2 ^ 59
def prefixEnd_1387367 : Nat := 4983230072969 + 3 ^ 40 * 1387367 * 2
def baseEnd_1387367 : Nat := 8794890310942946344841

theorem tailTrace_1387367 : CollatzResearch.WordTrace tailWord_1387367 prefixEnd_1387367 8794890310942946344841 := by
  unfold tailWord_1387367
  simp only [CollatzResearch.WordTrace]
  refine ⟨50601431564813777264680355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33734287709875851509786903 50601431564813777264680355)
  ·
    refine ⟨75902147347220665897020533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50601431564813777264680355 75902147347220665897020533)
    ·
      refine ⟨7115826313801937427845675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75902147347220665897020533 7115826313801937427845675)
      ·
        refine ⟨10673739470702906141768513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115826313801937427845675 10673739470702906141768513)
        ·
          refine ⟨8005304603027179606326385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10673739470702906141768513 8005304603027179606326385)
          ·
            refine ⟨6003978452270384704744789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8005304603027179606326385 6003978452270384704744789)
            ·
              refine ⟨8794890310942946344841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6003978452270384704744789 8794890310942946344841)
              ·
                rfl

theorem cell23_1387367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 11].length) (baseStart_1387367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387367 prefixEnd_1387367 := by exact prefixLift 1387367
  have htrace : WordTrace (prefixWord ++ tailWord_1387367) baseStart_1387367 baseEnd_1387367 := by
    simpa [prefixWord, tailWord_1387367, baseEnd_1387367] using wordTrace_append hprefix tailTrace_1387367
  have hstable : (prefixWord ++ tailWord_1387367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387367).length < 2 ^ (prefixWord ++ tailWord_1387367).sum := by decide
  have hdescent : baseEnd_1387367 < baseStart_1387367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387378 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_1387378 : Nat := 118140960795 + 1387378 * 2 ^ 59
def prefixEnd_1387378 : Nat := 4983230072969 + 3 ^ 40 * 1387378 * 2
def baseEnd_1387378 : Nat := 712391763473578110894571

theorem tailTrace_1387378 : CollatzResearch.WordTrace tailWord_1387378 prefixEnd_1387378 712391763473578110894571 := by
  unfold tailWord_1387378
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650458191943481535832697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33734555178515950762220525 12650458191943481535832697)
  ·
    refine ⟨9487843643957611151874523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12650458191943481535832697 9487843643957611151874523)
    ·
      refine ⟨14231765465936416727811785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9487843643957611151874523 14231765465936416727811785)
      ·
        refine ⟨10673824099452312545858839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14231765465936416727811785 10673824099452312545858839)
        ·
          refine ⟨16010736149178468818788259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673824099452312545858839 16010736149178468818788259)
          ·
            refine ⟨24016104223767703228182389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16010736149178468818788259 24016104223767703228182389)
            ·
              refine ⟨2251509770978222177642099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24016104223767703228182389 2251509770978222177642099)
              ·
                refine ⟨3377264656467333266463149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251509770978222177642099 3377264656467333266463149)
                ·
                  refine ⟨1266474246175249974923681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377264656467333266463149 1266474246175249974923681)
                  ·
                    refine ⟨949855684631437481192761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266474246175249974923681 949855684631437481192761)
                    ·
                      refine ⟨712391763473578110894571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949855684631437481192761 712391763473578110894571)
                      ·
                        rfl

theorem cell23_1387378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_1387378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387378 prefixEnd_1387378 := by exact prefixLift 1387378
  have htrace : WordTrace (prefixWord ++ tailWord_1387378) baseStart_1387378 baseEnd_1387378 := by
    simpa [prefixWord, tailWord_1387378, baseEnd_1387378] using wordTrace_append hprefix tailTrace_1387378
  have hstable : (prefixWord ++ tailWord_1387378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387378).length < 2 ^ (prefixWord ++ tailWord_1387378).sum := by decide
  have hdescent : baseEnd_1387378 < baseStart_1387378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387428 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_1387428 : Nat := 118140960795 + 1387428 * 2 ^ 59
def prefixEnd_1387428 : Nat := 4983230072969 + 3 ^ 40 * 1387428 * 2
def baseEnd_1387428 : Nat := 712417437506302915269341

theorem tailTrace_1387428 : CollatzResearch.WordTrace tailWord_1387428 prefixEnd_1387428 712417437506302915269341 := by
  unfold tailWord_1387428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301828208796392341325469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33735770945061856455100625 25301828208796392341325469)
  ·
    refine ⟨9488185578298647127997051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25301828208796392341325469 9488185578298647127997051)
    ·
      refine ⟨14232278367447970691995577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488185578298647127997051 14232278367447970691995577)
      ·
        refine ⟨10674208775585978018996683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232278367447970691995577 10674208775585978018996683)
        ·
          refine ⟨16011313163378967028495025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10674208775585978018996683 16011313163378967028495025)
          ·
            refine ⟨12008484872534225271371269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16011313163378967028495025 12008484872534225271371269)
            ·
              refine ⟨2251590913600167238382113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12008484872534225271371269 2251590913600167238382113)
              ·
                refine ⟨1688693185200125428786585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251590913600167238382113 1688693185200125428786585)
                ·
                  refine ⟨1266519888900094071589939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688693185200125428786585 1266519888900094071589939)
                  ·
                    refine ⟨1899779833350141107384909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266519888900094071589939 1899779833350141107384909)
                    ·
                      refine ⟨712417437506302915269341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1899779833350141107384909 712417437506302915269341)
                      ·
                        rfl

theorem cell23_1387428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_1387428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387428 prefixEnd_1387428 := by exact prefixLift 1387428
  have htrace : WordTrace (prefixWord ++ tailWord_1387428) baseStart_1387428 baseEnd_1387428 := by
    simpa [prefixWord, tailWord_1387428, baseEnd_1387428] using wordTrace_append hprefix tailTrace_1387428
  have hstable : (prefixWord ++ tailWord_1387428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387428).length < 2 ^ (prefixWord ++ tailWord_1387428).sum := by decide
  have hdescent : baseEnd_1387428 < baseStart_1387428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387468 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1387468 : Nat := 118140960795 + 1387468 * 2 ^ 59
def prefixEnd_1387468 : Nat := 4983230072969 + 3 ^ 40 * 1387468 * 2
def baseEnd_1387468 : Nat := 712437976732482758769157

theorem tailTrace_1387468 : CollatzResearch.WordTrace tailWord_1387468 prefixEnd_1387468 712437976732482758769157 := by
  unfold tailWord_1387468
  simp only [CollatzResearch.WordTrace]
  refine ⟨25302557668723935757053529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33736743558298581009404705 25302557668723935757053529)
  ·
    refine ⟨18976918251542951817790147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25302557668723935757053529 18976918251542951817790147)
    ·
      refine ⟨28465377377314427726685221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18976918251542951817790147 28465377377314427726685221)
      ·
        refine ⟨5337258258246455198753479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28465377377314427726685221 5337258258246455198753479)
        ·
          refine ⟨8005887387369682798130219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337258258246455198753479 8005887387369682798130219)
          ·
            refine ⟨12008831081054524197195329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005887387369682798130219 12008831081054524197195329)
            ·
              refine ⟨9006623310790893147896497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008831081054524197195329 9006623310790893147896497)
              ·
                refine ⟨6754967483093169860922373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006623310790893147896497 6754967483093169860922373)
                ·
                  refine ⟨1266556403079969348922945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6754967483093169860922373 1266556403079969348922945)
                  ·
                    refine ⟨949917302309977011692209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266556403079969348922945 949917302309977011692209)
                    ·
                      refine ⟨712437976732482758769157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949917302309977011692209 712437976732482758769157)
                      ·
                        rfl

theorem cell23_1387468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1387468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387468 prefixEnd_1387468 := by exact prefixLift 1387468
  have htrace : WordTrace (prefixWord ++ tailWord_1387468) baseStart_1387468 baseEnd_1387468 := by
    simpa [prefixWord, tailWord_1387468, baseEnd_1387468] using wordTrace_append hprefix tailTrace_1387468
  have hstable : (prefixWord ++ tailWord_1387468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387468).length < 2 ^ (prefixWord ++ tailWord_1387468).sum := by decide
  have hdescent : baseEnd_1387468 < baseStart_1387468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387485 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_1387485 : Nat := 118140960795 + 1387485 * 2 ^ 59
def prefixEnd_1387485 : Nat := 4983230072969 + 3 ^ 40 * 1387485 * 2
def baseEnd_1387485 : Nat := 712446705903609192256579

theorem tailTrace_1387485 : CollatzResearch.WordTrace tailWord_1387485 prefixEnd_1387485 712446705903609192256579 := by
  unfold tailWord_1387485
  simp only [CollatzResearch.WordTrace]
  refine ⟨50605735378386283417475909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33737156918924188944983939 50605735378386283417475909)
  ·
    refine ⟨9488575383447428140776733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50605735378386283417475909 9488575383447428140776733)
    ·
      refine ⟨3558215768792785552791275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9488575383447428140776733 3558215768792785552791275)
      ·
        refine ⟨5337323653189178329186913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558215768792785552791275 5337323653189178329186913)
        ·
          refine ⟨4002992739891883746890185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5337323653189178329186913 4002992739891883746890185)
          ·
            refine ⟨3002244554918912810167639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002992739891883746890185 3002244554918912810167639)
            ·
              refine ⟨4503366832378369215251459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002244554918912810167639 4503366832378369215251459)
              ·
                refine ⟨6755050248567553822877189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503366832378369215251459 6755050248567553822877189)
                ·
                  refine ⟨1266571921606416341789473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6755050248567553822877189 1266571921606416341789473)
                  ·
                    refine ⟨949928941204812256342105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266571921606416341789473 949928941204812256342105)
                    ·
                      refine ⟨712446705903609192256579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949928941204812256342105 712446705903609192256579)
                      ·
                        rfl

theorem cell23_1387485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_1387485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387485 prefixEnd_1387485 := by exact prefixLift 1387485
  have htrace : WordTrace (prefixWord ++ tailWord_1387485) baseStart_1387485 baseEnd_1387485 := by
    simpa [prefixWord, tailWord_1387485, baseEnd_1387485] using wordTrace_append hprefix tailTrace_1387485
  have hstable : (prefixWord ++ tailWord_1387485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387485).length < 2 ^ (prefixWord ++ tailWord_1387485).sum := by decide
  have hdescent : baseEnd_1387485 < baseStart_1387485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387491 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 5]
def baseStart_1387491 : Nat := 118140960795 + 1387491 * 2 ^ 59
def prefixEnd_1387491 : Nat := 4983230072969 + 3 ^ 40 * 1387491 * 2
def baseEnd_1387491 : Nat := 79161087420837352086839

theorem tailTrace_1387491 : CollatzResearch.WordTrace tailWord_1387491 prefixEnd_1387491 79161087420837352086839 := by
  unfold tailWord_1387491
  simp only [CollatzResearch.WordTrace]
  refine ⟨50605954216364546442194327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33737302810909697628129551 50605954216364546442194327)
  ·
    refine ⟨75908931324546819663291491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50605954216364546442194327 75908931324546819663291491)
    ·
      refine ⟨113863396986820229494937237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75908931324546819663291491 113863396986820229494937237)
      ·
        refine ⟨5337346733757198257575183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113863396986820229494937237 5337346733757198257575183)
        ·
          refine ⟨8006020100635797386362775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337346733757198257575183 8006020100635797386362775)
          ·
            refine ⟨12009030150953696079544163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006020100635797386362775 12009030150953696079544163)
            ·
              refine ⟨18013545226430544119316245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12009030150953696079544163 18013545226430544119316245)
              ·
                refine ⟨844384932488931755592949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18013545226430544119316245 844384932488931755592949)
                ·
                  refine ⟨79161087420837352086839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 844384932488931755592949 79161087420837352086839)
                  ·
                    rfl

theorem cell23_1387491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 5].length) (baseStart_1387491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387491 prefixEnd_1387491 := by exact prefixLift 1387491
  have htrace : WordTrace (prefixWord ++ tailWord_1387491) baseStart_1387491 baseEnd_1387491 := by
    simpa [prefixWord, tailWord_1387491, baseEnd_1387491] using wordTrace_append hprefix tailTrace_1387491
  have hstable : (prefixWord ++ tailWord_1387491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387491).length < 2 ^ (prefixWord ++ tailWord_1387491).sum := by decide
  have hdescent : baseEnd_1387491 < baseStart_1387491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387502 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_1387502 : Nat := 118140960795 + 1387502 * 2 ^ 59
def prefixEnd_1387502 : Nat := 4983230072969 + 3 ^ 40 * 1387502 * 2
def baseEnd_1387502 : Nat := 712455435074735625744001

theorem tailTrace_1387502 : CollatzResearch.WordTrace tailWord_1387502 prefixEnd_1387502 712455435074735625744001 := by
  unfold tailWord_1387502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325794427415586915105595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33737570279549796880563173 6325794427415586915105595)
  ·
    refine ⟨9488691641123380372658393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325794427415586915105595 9488691641123380372658393)
    ·
      refine ⟨7116518730842535279493795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9488691641123380372658393 7116518730842535279493795)
      ·
        refine ⟨10674778096263802919240693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116518730842535279493795 10674778096263802919240693)
        ·
          refine ⟨1000760446524731523678815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10674778096263802919240693 1000760446524731523678815)
          ·
            refine ⟨1501140669787097285518223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000760446524731523678815 1501140669787097285518223)
            ·
              refine ⟨2251711004680645928277335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501140669787097285518223 2251711004680645928277335)
              ·
                refine ⟨3377566507020968892416003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251711004680645928277335 3377566507020968892416003)
                ·
                  refine ⟨5066349760531453338624005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377566507020968892416003 5066349760531453338624005)
                  ·
                    refine ⟨949940580099647500992001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066349760531453338624005 949940580099647500992001)
                    ·
                      refine ⟨712455435074735625744001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 949940580099647500992001 712455435074735625744001)
                      ·
                        rfl

theorem cell23_1387502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_1387502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387502 prefixEnd_1387502 := by exact prefixLift 1387502
  have htrace : WordTrace (prefixWord ++ tailWord_1387502) baseStart_1387502 baseEnd_1387502 := by
    simpa [prefixWord, tailWord_1387502, baseEnd_1387502] using wordTrace_append hprefix tailTrace_1387502
  have hstable : (prefixWord ++ tailWord_1387502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387502).length < 2 ^ (prefixWord ++ tailWord_1387502).sum := by decide
  have hdescent : baseEnd_1387502 < baseStart_1387502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387541 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1387541 : Nat := 118140960795 + 1387541 * 2 ^ 59
def prefixEnd_1387541 : Nat := 4983230072969 + 3 ^ 40 * 1387541 * 2
def baseEnd_1387541 : Nat := 712475460820260973156321

theorem tailTrace_1387541 : CollatzResearch.WordTrace tailWord_1387541 prefixEnd_1387541 712475460820260973156321 := by
  unfold tailWord_1387541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50607777866183404981514477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33738518577455603321009651 50607777866183404981514477)
  ·
    refine ⟨18977916699818776868067929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50607777866183404981514477 18977916699818776868067929)
    ·
      refine ⟨14233437524864082651050947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18977916699818776868067929 14233437524864082651050947)
      ·
        refine ⟨21350156287296123976576421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14233437524864082651050947 21350156287296123976576421)
        ·
          refine ⟨4003154303868023245608079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21350156287296123976576421 4003154303868023245608079)
          ·
            refine ⟨6004731455802034868412119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003154303868023245608079 6004731455802034868412119)
            ·
              refine ⟨9007097183703052302618179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004731455802034868412119 9007097183703052302618179)
              ·
                refine ⟨13510645775554578453927269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007097183703052302618179 13510645775554578453927269)
                ·
                  refine ⟨2533246082916483460111363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13510645775554578453927269 2533246082916483460111363)
                  ·
                    refine ⟨3799869124374725190167045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533246082916483460111363 3799869124374725190167045)
                    ·
                      refine ⟨712475460820260973156321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3799869124374725190167045 712475460820260973156321)
                      ·
                        rfl

theorem cell23_1387541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1387541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387541 prefixEnd_1387541 := by exact prefixLift 1387541
  have htrace : WordTrace (prefixWord ++ tailWord_1387541) baseStart_1387541 baseEnd_1387541 := by
    simpa [prefixWord, tailWord_1387541, baseEnd_1387541] using wordTrace_append hprefix tailTrace_1387541
  have hstable : (prefixWord ++ tailWord_1387541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387541).length < 2 ^ (prefixWord ++ tailWord_1387541).sum := by decide
  have hdescent : baseEnd_1387541 < baseStart_1387541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387602 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1387602 : Nat := 118140960795 + 1387602 * 2 ^ 59
def prefixEnd_1387602 : Nat := 4983230072969 + 3 ^ 40 * 1387602 * 2
def baseEnd_1387602 : Nat := 237502261046728411497847

theorem tailTrace_1387602 : CollatzResearch.WordTrace tailWord_1387602 prefixEnd_1387602 237502261046728411497847 := by
  unfold tailWord_1387602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12652500679740603099871265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33740001812641608266323373 12652500679740603099871265)
  ·
    refine ⟨9489375509805452324903449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12652500679740603099871265 9489375509805452324903449)
    ·
      refine ⟨7117031632354089243677587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9489375509805452324903449 7117031632354089243677587)
      ·
        refine ⟨10675547448531133865516381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117031632354089243677587 10675547448531133865516381)
        ·
          refine ⟨4003330293199175199568643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10675547448531133865516381 4003330293199175199568643)
          ·
            refine ⟨6004995439798762799352965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003330293199175199568643 6004995439798762799352965)
            ·
              refine ⟨1125936644962268024878681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6004995439798762799352965 1125936644962268024878681)
              ·
                refine ⟨844452483721701018659011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125936644962268024878681 844452483721701018659011)
                ·
                  refine ⟨1266678725582551527988517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844452483721701018659011 1266678725582551527988517)
                  ·
                    refine ⟨237502261046728411497847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266678725582551527988517 237502261046728411497847)
                    ·
                      rfl

theorem cell23_1387602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1387602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387602 prefixEnd_1387602 := by exact prefixLift 1387602
  have htrace : WordTrace (prefixWord ++ tailWord_1387602) baseStart_1387602 baseEnd_1387602 := by
    simpa [prefixWord, tailWord_1387602, baseEnd_1387602] using wordTrace_append hprefix tailTrace_1387602
  have hstable : (prefixWord ++ tailWord_1387602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387602).length < 2 ^ (prefixWord ++ tailWord_1387602).sum := by decide
  have hdescent : baseEnd_1387602 < baseStart_1387602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387608 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1387608 : Nat := 118140960795 + 1387608 * 2 ^ 59
def prefixEnd_1387608 : Nat := 4983230072969 + 3 ^ 40 * 1387608 * 2
def baseEnd_1387608 : Nat := 712509864024112211018513

theorem tailTrace_1387608 : CollatzResearch.WordTrace tailWord_1387608 prefixEnd_1387608 712509864024112211018513 := by
  unfold tailWord_1387608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25305110778470337712101739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33740147704627116949468985 25305110778470337712101739)
  ·
    refine ⟨37957666167705506568152609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25305110778470337712101739 37957666167705506568152609)
    ·
      refine ⟨28468249625779129926114457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37957666167705506568152609 28468249625779129926114457)
      ·
        refine ⟨21351187219334347444585843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28468249625779129926114457 21351187219334347444585843)
        ·
          refine ⟨32026780829001521166878765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21351187219334347444585843 32026780829001521166878765)
          ·
            refine ⟨12010042810875570437579537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32026780829001521166878765 12010042810875570437579537)
            ·
              refine ⟨9007532108156677828184653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010042810875570437579537 9007532108156677828184653)
              ·
                refine ⟨3377824540558754185569245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9007532108156677828184653 3377824540558754185569245)
                ·
                  refine ⟨1266684202709532819588467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3377824540558754185569245 1266684202709532819588467)
                  ·
                    refine ⟨1900026304064299229382701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266684202709532819588467 1900026304064299229382701)
                    ·
                      refine ⟨712509864024112211018513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1900026304064299229382701 712509864024112211018513)
                      ·
                        rfl

theorem cell23_1387608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1387608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387608 prefixEnd_1387608 := by exact prefixLift 1387608
  have htrace : WordTrace (prefixWord ++ tailWord_1387608) baseStart_1387608 baseEnd_1387608 := by
    simpa [prefixWord, tailWord_1387608, baseEnd_1387608] using wordTrace_append hprefix tailTrace_1387608
  have hstable : (prefixWord ++ tailWord_1387608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387608).length < 2 ^ (prefixWord ++ tailWord_1387608).sum := by decide
  have hdescent : baseEnd_1387608 < baseStart_1387608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387631 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_1387631 : Nat := 118140960795 + 1387631 * 2 ^ 59
def prefixEnd_1387631 : Nat := 4983230072969 + 3 ^ 40 * 1387631 * 2
def baseEnd_1387631 : Nat := 712521674079165621030907

theorem tailTrace_1387631 : CollatzResearch.WordTrace tailWord_1387631 prefixEnd_1387631 712521674079165621030907 := by
  unfold tailWord_1387631
  simp only [CollatzResearch.WordTrace]
  refine ⟨50611060435857350352290747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33740706957238233568193831 50611060435857350352290747)
  ·
    refine ⟨75916590653786025528436121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50611060435857350352290747 75916590653786025528436121)
    ·
      refine ⟨56937442990339519146327091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75916590653786025528436121 56937442990339519146327091)
      ·
        refine ⟨85406164485509278719490637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56937442990339519146327091 85406164485509278719490637)
        ·
          refine ⟨32027311682065979519808989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85406164485509278719490637 32027311682065979519808989)
          ·
            refine ⟨12010241880774742319928371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32027311682065979519808989 12010241880774742319928371)
            ·
              refine ⟨18015362821162113479892557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12010241880774742319928371 18015362821162113479892557)
              ·
                refine ⟨6755761057935792554959709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18015362821162113479892557 6755761057935792554959709)
                ·
                  refine ⟨2533410396725922208109891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6755761057935792554959709 2533410396725922208109891)
                  ·
                    refine ⟨3800115595088883312164837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533410396725922208109891 3800115595088883312164837)
                    ·
                      refine ⟨712521674079165621030907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3800115595088883312164837 712521674079165621030907)
                      ·
                        rfl

theorem cell23_1387631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_1387631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387631 prefixEnd_1387631 := by exact prefixLift 1387631
  have htrace : WordTrace (prefixWord ++ tailWord_1387631) baseStart_1387631 baseEnd_1387631 := by
    simpa [prefixWord, tailWord_1387631, baseEnd_1387631] using wordTrace_append hprefix tailTrace_1387631
  have hstable : (prefixWord ++ tailWord_1387631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387631).length < 2 ^ (prefixWord ++ tailWord_1387631).sum := by decide
  have hdescent : baseEnd_1387631 < baseStart_1387631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387651 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1387651 : Nat := 118140960795 + 1387651 * 2 ^ 59
def prefixEnd_1387651 : Nat := 4983230072969 + 3 ^ 40 * 1387651 * 2
def baseEnd_1387651 : Nat := 712531943692255542780815

theorem tailTrace_1387651 : CollatzResearch.WordTrace tailWord_1387651 prefixEnd_1387651 712531943692255542780815 := by
  unfold tailWord_1387651
  simp only [CollatzResearch.WordTrace]
  refine ⟨50611789895784893768018807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33741193263856595845345871 50611789895784893768018807)
  ·
    refine ⟨75917684843677340652028211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50611789895784893768018807 75917684843677340652028211)
    ·
      refine ⟨113876527265516010978042317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75917684843677340652028211 113876527265516010978042317)
      ·
        refine ⟨42703697724568504116765869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113876527265516010978042317 42703697724568504116765869)
        ·
          refine ⟨16013886646713189043787201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42703697724568504116765869 16013886646713189043787201)
          ·
            refine ⟨12010414985034891782840401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013886646713189043787201 12010414985034891782840401)
            ·
              refine ⟨9007811238776168837130301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12010414985034891782840401 9007811238776168837130301)
              ·
                refine ⟨3377929214541063313923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9007811238776168837130301 3377929214541063313923863)
                ·
                  refine ⟨5066893821811594970885795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377929214541063313923863 5066893821811594970885795)
                  ·
                    refine ⟨7600340732717392456328693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066893821811594970885795 7600340732717392456328693)
                    ·
                      refine ⟨712531943692255542780815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7600340732717392456328693 712531943692255542780815)
                      ·
                        rfl

theorem cell23_1387651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1387651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387651 prefixEnd_1387651 := by exact prefixLift 1387651
  have htrace : WordTrace (prefixWord ++ tailWord_1387651) baseStart_1387651 baseEnd_1387651 := by
    simpa [prefixWord, tailWord_1387651, baseEnd_1387651] using wordTrace_append hprefix tailTrace_1387651
  have hstable : (prefixWord ++ tailWord_1387651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387651).length < 2 ^ (prefixWord ++ tailWord_1387651).sum := by decide
  have hdescent : baseEnd_1387651 < baseStart_1387651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387658 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_1387658 : Nat := 118140960795 + 1387658 * 2 ^ 59
def prefixEnd_1387658 : Nat := 4983230072969 + 3 ^ 40 * 1387658 * 2
def baseEnd_1387658 : Nat := 237511846018945671797761

theorem tailTrace_1387658 : CollatzResearch.WordTrace tailWord_1387658 prefixEnd_1387658 237511846018945671797761 := by
  unfold tailWord_1387658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653011301689883490880907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33741363471173022642349085 12653011301689883490880907)
  ·
    refine ⟨18979516952534825236321361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12653011301689883490880907 18979516952534825236321361)
    ·
      refine ⟨14234637714401118927241021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18979516952534825236321361 14234637714401118927241021)
      ·
        refine ⟨5337989142900419597715383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14234637714401118927241021 5337989142900419597715383)
        ·
          refine ⟨8006983714350629396573075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337989142900419597715383 8006983714350629396573075)
          ·
            refine ⟨12010475571525944094859613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006983714350629396573075 12010475571525944094859613)
            ·
              refine ⟨4503928339322229035572355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12010475571525944094859613 4503928339322229035572355)
              ·
                refine ⟨6755892508983343553358533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503928339322229035572355 6755892508983343553358533)
                ·
                  refine ⟨1266729845434376916254725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6755892508983343553358533 1266729845434376916254725)
                  ·
                    refine ⟨237511846018945671797761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266729845434376916254725 237511846018945671797761)
                    ·
                      rfl

theorem cell23_1387658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_1387658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387658 prefixEnd_1387658 := by exact prefixLift 1387658
  have htrace : WordTrace (prefixWord ++ tailWord_1387658) baseStart_1387658 baseEnd_1387658 := by
    simpa [prefixWord, tailWord_1387658, baseEnd_1387658] using wordTrace_append hprefix tailTrace_1387658
  have hstable : (prefixWord ++ tailWord_1387658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387658).length < 2 ^ (prefixWord ++ tailWord_1387658).sum := by decide
  have hdescent : baseEnd_1387658 < baseStart_1387658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387682 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1387682 : Nat := 118140960795 + 1387682 * 2 ^ 59
def prefixEnd_1387682 : Nat := 4983230072969 + 3 ^ 40 * 1387682 * 2
def baseEnd_1387682 : Nat := 712547861592544921493173

theorem tailTrace_1387682 : CollatzResearch.WordTrace tailWord_1387682 prefixEnd_1387682 712547861592544921493173 := by
  unfold tailWord_1387682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653230139668146515599325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33741947039115057374931533 12653230139668146515599325)
  ·
    refine ⟨4744961302375554943349747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12653230139668146515599325 4744961302375554943349747)
    ·
      refine ⟨7117441953563332415024621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744961302375554943349747 7117441953563332415024621)
      ·
        refine ⟨2669040732586249655634233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7117441953563332415024621 2669040732586249655634233)
        ·
          refine ⟨2001780549439687241725675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669040732586249655634233 2001780549439687241725675)
          ·
            refine ⟨3002670824159530862588513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001780549439687241725675 3002670824159530862588513)
            ·
              refine ⟨2252003118119648146941385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002670824159530862588513 2252003118119648146941385)
              ·
                refine ⟨1689002338589736110206039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252003118119648146941385 1689002338589736110206039)
                ·
                  refine ⟨2533503507884604165309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689002338589736110206039 2533503507884604165309059)
                  ·
                    refine ⟨3800255261826906247963589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533503507884604165309059 3800255261826906247963589)
                    ·
                      refine ⟨712547861592544921493173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3800255261826906247963589 712547861592544921493173)
                      ·
                        rfl

theorem cell23_1387682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1387682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387682 prefixEnd_1387682 := by exact prefixLift 1387682
  have htrace : WordTrace (prefixWord ++ tailWord_1387682) baseStart_1387682 baseEnd_1387682 := by
    simpa [prefixWord, tailWord_1387682, baseEnd_1387682] using wordTrace_append hprefix tailTrace_1387682
  have hstable : (prefixWord ++ tailWord_1387682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387682).length < 2 ^ (prefixWord ++ tailWord_1387682).sum := by decide
  have hdescent : baseEnd_1387682 < baseStart_1387682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387685 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_1387685 : Nat := 118140960795 + 1387685 * 2 ^ 59
def prefixEnd_1387685 : Nat := 4983230072969 + 3 ^ 40 * 1387685 * 2
def baseEnd_1387685 : Nat := 712549402034508409755659

theorem tailTrace_1387685 : CollatzResearch.WordTrace tailWord_1387685 prefixEnd_1387685 712549402034508409755659 := by
  unfold tailWord_1387685
  simp only [CollatzResearch.WordTrace]
  refine ⟨50613029977661717574756509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33742019985107811716504339 50613029977661717574756509)
  ·
    refine ⟨18979886241623144090533691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50613029977661717574756509 18979886241623144090533691)
    ·
      refine ⟨28469829362434716135800537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18979886241623144090533691 28469829362434716135800537)
      ·
        refine ⟨21352372021826037101850403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28469829362434716135800537 21352372021826037101850403)
        ·
          refine ⟨32028558032739055652775605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21352372021826037101850403 32028558032739055652775605)
          ·
            refine ⟨3002677315569286467447713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32028558032739055652775605 3002677315569286467447713)
            ·
              refine ⟨2252007986676964850585785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002677315569286467447713 2252007986676964850585785)
              ·
                refine ⟨1689005990007723637939339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252007986676964850585785 1689005990007723637939339)
                ·
                  refine ⟨2533508985011585456909009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689005990007723637939339 2533508985011585456909009)
                  ·
                    refine ⟨1900131738758689092681757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2533508985011585456909009 1900131738758689092681757)
                    ·
                      refine ⟨712549402034508409755659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1900131738758689092681757 712549402034508409755659)
                      ·
                        rfl

theorem cell23_1387685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_1387685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387685 prefixEnd_1387685 := by exact prefixLift 1387685
  have htrace : WordTrace (prefixWord ++ tailWord_1387685) baseStart_1387685 baseEnd_1387685 := by
    simpa [prefixWord, tailWord_1387685, baseEnd_1387685] using wordTrace_append hprefix tailTrace_1387685
  have hstable : (prefixWord ++ tailWord_1387685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387685).length < 2 ^ (prefixWord ++ tailWord_1387685).sum := by decide
  have hdescent : baseEnd_1387685 < baseStart_1387685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387716 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_1387716 : Nat := 118140960795 + 1387716 * 2 ^ 59
def prefixEnd_1387716 : Nat := 4983230072969 + 3 ^ 40 * 1387716 * 2
def baseEnd_1387716 : Nat := 712565319934797788468017

theorem tailTrace_1387716 : CollatzResearch.WordTrace tailWord_1387716 prefixEnd_1387716 712565319934797788468017 := by
  unfold tailWord_1387716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307080320274704934567501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33742773760366273246090001 25307080320274704934567501)
  ·
    refine ⟨9490155120103014350462813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25307080320274704934567501 9490155120103014350462813)
    ·
      refine ⟨3558808170038630381423555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9490155120103014350462813 3558808170038630381423555)
      ·
        refine ⟨5338212255057945572135333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558808170038630381423555 5338212255057945572135333)
        ·
          refine ⟨1000914797823364794775375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5338212255057945572135333 1000914797823364794775375)
          ·
            refine ⟨1501372196735047192163063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000914797823364794775375 1501372196735047192163063)
            ·
              refine ⟨2252058295102570788244595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501372196735047192163063 2252058295102570788244595)
              ·
                refine ⟨3378087442653856182366893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252058295102570788244595 3378087442653856182366893)
                ·
                  refine ⟨1266782790995196068387585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3378087442653856182366893 1266782790995196068387585)
                  ·
                    refine ⟨950087093246397051290689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266782790995196068387585 950087093246397051290689)
                    ·
                      refine ⟨712565319934797788468017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950087093246397051290689 712565319934797788468017)
                      ·
                        rfl

theorem cell23_1387716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_1387716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387716 prefixEnd_1387716 := by exact prefixLift 1387716
  have htrace : WordTrace (prefixWord ++ tailWord_1387716) baseStart_1387716 baseEnd_1387716 := by
    simpa [prefixWord, tailWord_1387716, baseEnd_1387716] using wordTrace_append hprefix tailTrace_1387716
  have hstable : (prefixWord ++ tailWord_1387716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387716).length < 2 ^ (prefixWord ++ tailWord_1387716).sum := by decide
  have hdescent : baseEnd_1387716 < baseStart_1387716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387755 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 4, 2]
def baseStart_1387755 : Nat := 118140960795 + 1387755 * 2 ^ 59
def prefixEnd_1387755 : Nat := 4983230072969 + 3 ^ 40 * 1387755 * 2
def baseEnd_1387755 : Nat := 712585345680323135880337

theorem tailTrace_1387755 : CollatzResearch.WordTrace tailWord_1387755 prefixEnd_1387755 712585345680323135880337 := by
  unfold tailWord_1387755
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615583087408119529804719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33743722058272079686536479 50615583087408119529804719)
  ·
    refine ⟨75923374631112179294707079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615583087408119529804719 75923374631112179294707079)
    ·
      refine ⟨113885061946668268942060619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75923374631112179294707079 113885061946668268942060619)
      ·
        refine ⟨170827592920002403413090929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113885061946668268942060619 170827592920002403413090929)
        ·
          refine ⟨128120694690001802559818197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170827592920002403413090929 128120694690001802559818197)
          ·
            refine ⟨3002828781796917247495739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128120694690001802559818197 3002828781796917247495739)
            ·
              refine ⟨4504243172695375871243609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002828781796917247495739 4504243172695375871243609)
              ·
                refine ⟨3378182379521531903432707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4504243172695375871243609 3378182379521531903432707)
                ·
                  refine ⟨5067273569282297855149061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378182379521531903432707 5067273569282297855149061)
                  ·
                    refine ⟨950113794240430847840449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5067273569282297855149061 950113794240430847840449)
                    ·
                      refine ⟨712585345680323135880337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950113794240430847840449 712585345680323135880337)
                      ·
                        rfl

theorem cell23_1387755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4, 2].length) (baseStart_1387755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387755 prefixEnd_1387755 := by exact prefixLift 1387755
  have htrace : WordTrace (prefixWord ++ tailWord_1387755) baseStart_1387755 baseEnd_1387755 := by
    simpa [prefixWord, tailWord_1387755, baseEnd_1387755] using wordTrace_append hprefix tailTrace_1387755
  have hstable : (prefixWord ++ tailWord_1387755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387755).length < 2 ^ (prefixWord ++ tailWord_1387755).sum := by decide
  have hdescent : baseEnd_1387755 < baseStart_1387755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387758 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1387758 : Nat := 118140960795 + 1387758 * 2 ^ 59
def prefixEnd_1387758 : Nat := 4983230072969 + 3 ^ 40 * 1387758 * 2
def baseEnd_1387758 : Nat := 712586886122286624142823

theorem tailTrace_1387758 : CollatzResearch.WordTrace tailWord_1387758 prefixEnd_1387758 712586886122286624142823 := by
  unfold tailWord_1387758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326961563299656380270491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33743795004264834028109285 6326961563299656380270491)
  ·
    refine ⟨9490442344949484570405737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6326961563299656380270491 9490442344949484570405737)
    ·
      refine ⟨7117831758712113427804303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9490442344949484570405737 7117831758712113427804303)
      ·
        refine ⟨10676747638068170141706455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117831758712113427804303 10676747638068170141706455)
        ·
          refine ⟨16015121457102255212559683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10676747638068170141706455 16015121457102255212559683)
          ·
            refine ⟨24022682185653382818839525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015121457102255212559683 24022682185653382818839525)
            ·
              refine ⟨4504252909810009278532411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24022682185653382818839525 4504252909810009278532411)
              ·
                refine ⟨6756379364715013917798617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504252909810009278532411 6756379364715013917798617)
                ·
                  refine ⟨5067284523536260438348963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6756379364715013917798617 5067284523536260438348963)
                  ·
                    refine ⟨7600926785304390657523445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067284523536260438348963 7600926785304390657523445)
                    ·
                      refine ⟨712586886122286624142823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7600926785304390657523445 712586886122286624142823)
                      ·
                        rfl

theorem cell23_1387758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1387758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387758 prefixEnd_1387758 := by exact prefixLift 1387758
  have htrace : WordTrace (prefixWord ++ tailWord_1387758) baseStart_1387758 baseEnd_1387758 := by
    simpa [prefixWord, tailWord_1387758, baseEnd_1387758] using wordTrace_append hprefix tailTrace_1387758
  have hstable : (prefixWord ++ tailWord_1387758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387758).length < 2 ^ (prefixWord ++ tailWord_1387758).sum := by decide
  have hdescent : baseEnd_1387758 < baseStart_1387758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387759 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 1, 3, 2]
def baseStart_1387759 : Nat := 118140960795 + 1387759 * 2 ^ 59
def prefixEnd_1387759 : Nat := 4983230072969 + 3 ^ 40 * 1387759 * 2
def baseEnd_1387759 : Nat := 712587399602941120230319

theorem tailTrace_1387759 : CollatzResearch.WordTrace tailWord_1387759 prefixEnd_1387759 712587399602941120230319 := by
  unfold tailWord_1387759
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615728979393628212950331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33743819319595752141966887 50615728979393628212950331)
  ·
    refine ⟨75923593469090442319425497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615728979393628212950331 75923593469090442319425497)
    ·
      refine ⟨56942695101817831739569123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75923593469090442319425497 56942695101817831739569123)
      ·
        refine ⟨85414042652726747609353685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56942695101817831739569123 85414042652726747609353685)
        ·
          refine ⟨2001891624673283147094227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85414042652726747609353685 2001891624673283147094227)
          ·
            refine ⟨3002837437009924720641341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001891624673283147094227 3002837437009924720641341)
            ·
              refine ⟨1126064038878721770240503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3002837437009924720641341 1126064038878721770240503)
              ·
                refine ⟨1689096058318082655360755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126064038878721770240503 1689096058318082655360755)
                ·
                  refine ⟨2533644087477123983041133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689096058318082655360755 2533644087477123983041133)
                  ·
                    refine ⟨950116532803921493640425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533644087477123983041133 950116532803921493640425)
                    ·
                      refine ⟨712587399602941120230319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950116532803921493640425 712587399602941120230319)
                      ·
                        rfl

theorem cell23_1387759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 3, 2].length) (baseStart_1387759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387759 prefixEnd_1387759 := by exact prefixLift 1387759
  have htrace : WordTrace (prefixWord ++ tailWord_1387759) baseStart_1387759 baseEnd_1387759 := by
    simpa [prefixWord, tailWord_1387759, baseEnd_1387759] using wordTrace_append hprefix tailTrace_1387759
  have hstable : (prefixWord ++ tailWord_1387759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387759).length < 2 ^ (prefixWord ++ tailWord_1387759).sum := by decide
  have hdescent : baseEnd_1387759 < baseStart_1387759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387788 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1387788 : Nat := 118140960795 + 1387788 * 2 ^ 59
def prefixEnd_1387788 : Nat := 4983230072969 + 3 ^ 40 * 1387788 * 2
def baseEnd_1387788 : Nat := 712602290541921506767685

theorem tailTrace_1387788 : CollatzResearch.WordTrace tailWord_1387788 prefixEnd_1387788 712602290541921506767685 := by
  unfold tailWord_1387788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25308393348144283082878009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33744524464192377443837345 25308393348144283082878009)
  ·
    refine ⟨18981295011108212312158507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25308393348144283082878009 18981295011108212312158507)
    ·
      refine ⟨28471942516662318468237761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18981295011108212312158507 28471942516662318468237761)
      ·
        refine ⟨21353956887496738851178321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28471942516662318468237761 21353956887496738851178321)
        ·
          refine ⟨16015467665622554138383741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21353956887496738851178321 16015467665622554138383741)
          ·
            refine ⟨6005800374608457801893903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16015467665622554138383741 6005800374608457801893903)
            ·
              refine ⟨9008700561912686702840855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005800374608457801893903 9008700561912686702840855)
              ·
                refine ⟨13513050842869030054261283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9008700561912686702840855 13513050842869030054261283)
                ·
                  refine ⟨20269576264303545081391925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513050842869030054261283 20269576264303545081391925)
                  ·
                    refine ⟨1900272774778457351380493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20269576264303545081391925 1900272774778457351380493)
                    ·
                      refine ⟨712602290541921506767685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1900272774778457351380493 712602290541921506767685)
                      ·
                        rfl

theorem cell23_1387788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1387788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387788 prefixEnd_1387788 := by exact prefixLift 1387788
  have htrace : WordTrace (prefixWord ++ tailWord_1387788) baseStart_1387788 baseEnd_1387788 := by
    simpa [prefixWord, tailWord_1387788, baseEnd_1387788] using wordTrace_append hprefix tailTrace_1387788
  have hstable : (prefixWord ++ tailWord_1387788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387788).length < 2 ^ (prefixWord ++ tailWord_1387788).sum := by decide
  have hdescent : baseEnd_1387788 < baseStart_1387788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387801 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1387801 : Nat := 118140960795 + 1387801 * 2 ^ 59
def prefixEnd_1387801 : Nat := 4983230072969 + 3 ^ 40 * 1387801 * 2
def baseEnd_1387801 : Nat := 712608965790429955905125

theorem tailTrace_1387801 : CollatzResearch.WordTrace tailWord_1387801 prefixEnd_1387801 712608965790429955905125 := by
  unfold tailWord_1387801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50617260845241469385979257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33744840563494312923986171 50617260845241469385979257)
  ·
    refine ⟨37962945633931102039484443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50617260845241469385979257 37962945633931102039484443)
    ·
      refine ⟨56944418450896653059226665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37962945633931102039484443 56944418450896653059226665)
      ·
        refine ⟨42708313838172489794419999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56944418450896653059226665 42708313838172489794419999)
        ·
          refine ⟨64062470757258734691629999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42708313838172489794419999 64062470757258734691629999)
          ·
            refine ⟨96093706135888102037444999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64062470757258734691629999 96093706135888102037444999)
            ·
              refine ⟨144140559203832153056167499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96093706135888102037444999 144140559203832153056167499)
              ·
                refine ⟨216210838805748229584251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144140559203832153056167499 216210838805748229584251249)
                ·
                  refine ⟨162158129104311172188188437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216210838805748229584251249 162158129104311172188188437)
                  ·
                    refine ⟨7601162301764586196321333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 162158129104311172188188437 7601162301764586196321333)
                    ·
                      refine ⟨712608965790429955905125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7601162301764586196321333 712608965790429955905125)
                      ·
                        rfl

theorem cell23_1387801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1387801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387801 prefixEnd_1387801 := by exact prefixLift 1387801
  have htrace : WordTrace (prefixWord ++ tailWord_1387801) baseStart_1387801 baseEnd_1387801 := by
    simpa [prefixWord, tailWord_1387801, baseEnd_1387801] using wordTrace_append hprefix tailTrace_1387801
  have hstable : (prefixWord ++ tailWord_1387801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387801).length < 2 ^ (prefixWord ++ tailWord_1387801).sum := by decide
  have hdescent : baseEnd_1387801 < baseStart_1387801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387858 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1387858 : Nat := 118140960795 + 1387858 * 2 ^ 59
def prefixEnd_1387858 : Nat := 4983230072969 + 3 ^ 40 * 1387858 * 2
def baseEnd_1387858 : Nat := 712638234187736232892363

theorem tailTrace_1387858 : CollatzResearch.WordTrace tailWord_1387858 prefixEnd_1387858 712638234187736232892363 := by
  unfold tailWord_1387858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654834951508742030201057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33746226537356645413869485 12654834951508742030201057)
  ·
    refine ⟨9491126213631556522650793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12654834951508742030201057 9491126213631556522650793)
    ·
      refine ⟨7118344660223667391988095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9491126213631556522650793 7118344660223667391988095)
      ·
        refine ⟨10677516990335501087982143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118344660223667391988095 10677516990335501087982143)
        ·
          refine ⟨16016275485503251631973215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677516990335501087982143 16016275485503251631973215)
          ·
            refine ⟨24024413228254877447959823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16016275485503251631973215 24024413228254877447959823)
            ·
              refine ⟨36036619842382316171939735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24024413228254877447959823 36036619842382316171939735)
              ·
                refine ⟨54054929763573474257909603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36036619842382316171939735 54054929763573474257909603)
                ·
                  refine ⟨81082394645360211386864405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54054929763573474257909603 81082394645360211386864405)
                  ·
                    refine ⟨3800737249001259908759269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81082394645360211386864405 3800737249001259908759269)
                    ·
                      refine ⟨712638234187736232892363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3800737249001259908759269 712638234187736232892363)
                      ·
                        rfl

theorem cell23_1387858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1387858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387858 prefixEnd_1387858 := by exact prefixLift 1387858
  have htrace : WordTrace (prefixWord ++ tailWord_1387858) baseStart_1387858 baseEnd_1387858 := by
    simpa [prefixWord, tailWord_1387858, baseEnd_1387858] using wordTrace_append hprefix tailTrace_1387858
  have hstable : (prefixWord ++ tailWord_1387858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387858).length < 2 ^ (prefixWord ++ tailWord_1387858).sum := by decide
  have hdescent : baseEnd_1387858 < baseStart_1387858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387898 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_1387898 : Nat := 118140960795 + 1387898 * 2 ^ 59
def prefixEnd_1387898 : Nat := 4983230072969 + 3 ^ 40 * 1387898 * 2
def baseEnd_1387898 : Nat := 237552924471305358797393

theorem tailTrace_1387898 : CollatzResearch.WordTrace tailWord_1387898 prefixEnd_1387898 237552924471305358797393 := by
  unfold tailWord_1387898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655199681472513738065087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33747199150593369968173565 12655199681472513738065087)
  ·
    refine ⟨18982799522208770607097631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12655199681472513738065087 18982799522208770607097631)
    ·
      refine ⟨28474199283313155910646447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18982799522208770607097631 28474199283313155910646447)
      ·
        refine ⟨42711298924969733865969671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28474199283313155910646447 42711298924969733865969671)
        ·
          refine ⟨64066948387454600798954507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42711298924969733865969671 64066948387454600798954507)
          ·
            refine ⟨96100422581181901198431761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64066948387454600798954507 96100422581181901198431761)
            ·
              refine ⟨72075316935886425898823821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96100422581181901198431761 72075316935886425898823821)
              ·
                refine ⟨27028243850957409712058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72075316935886425898823821 27028243850957409712058933)
                ·
                  refine ⟨2533897861027257160505525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27028243850957409712058933 2533897861027257160505525)
                  ·
                    refine ⟨237552924471305358797393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2533897861027257160505525 237552924471305358797393)
                    ·
                      rfl

theorem cell23_1387898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_1387898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387898 prefixEnd_1387898 := by exact prefixLift 1387898
  have htrace : WordTrace (prefixWord ++ tailWord_1387898) baseStart_1387898 baseEnd_1387898 := by
    simpa [prefixWord, tailWord_1387898, baseEnd_1387898] using wordTrace_append hprefix tailTrace_1387898
  have hstable : (prefixWord ++ tailWord_1387898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387898).length < 2 ^ (prefixWord ++ tailWord_1387898).sum := by decide
  have hdescent : baseEnd_1387898 < baseStart_1387898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387948 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1387948 : Nat := 118140960795 + 1387948 * 2 ^ 59
def prefixEnd_1387948 : Nat := 4983230072969 + 3 ^ 40 * 1387948 * 2
def baseEnd_1387948 : Nat := 712684447446640880766949

theorem tailTrace_1387948 : CollatzResearch.WordTrace tailWord_1387948 prefixEnd_1387948 712684447446640880766949 := by
  unfold tailWord_1387948
  simp only [CollatzResearch.WordTrace]
  refine ⟨25311311187854456745790249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33748414917139275661053665 25311311187854456745790249)
  ·
    refine ⟨18983483390890842559342687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25311311187854456745790249 18983483390890842559342687)
    ·
      refine ⟨28475225086336263839014031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983483390890842559342687 28475225086336263839014031)
      ·
        refine ⟨42712837629504395758521047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28475225086336263839014031 42712837629504395758521047)
        ·
          refine ⟨64069256444256593637781571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42712837629504395758521047 64069256444256593637781571)
          ·
            refine ⟨96103884666384890456672357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64069256444256593637781571 96103884666384890456672357)
            ·
              refine ⟨18019478374947166960626067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96103884666384890456672357 18019478374947166960626067)
              ·
                refine ⟨27029217562420750440939101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18019478374947166960626067 27029217562420750440939101)
                ·
                  refine ⟨10135956585907781415352163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27029217562420750440939101 10135956585907781415352163)
                  ·
                    refine ⟨15203934878861672123028245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10135956585907781415352163 15203934878861672123028245)
                    ·
                      refine ⟨712684447446640880766949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15203934878861672123028245 712684447446640880766949)
                      ·
                        rfl

theorem cell23_1387948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1387948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387948 prefixEnd_1387948 := by exact prefixLift 1387948
  have htrace : WordTrace (prefixWord ++ tailWord_1387948) baseStart_1387948 baseEnd_1387948 := by
    simpa [prefixWord, tailWord_1387948, baseEnd_1387948] using wordTrace_append hprefix tailTrace_1387948
  have hstable : (prefixWord ++ tailWord_1387948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387948).length < 2 ^ (prefixWord ++ tailWord_1387948).sum := by decide
  have hdescent : baseEnd_1387948 < baseStart_1387948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1387975 : List Nat := [1, 1, 4, 1, 1, 3, 5, 7]
def baseStart_1387975 : Nat := 118140960795 + 1387975 * 2 ^ 59
def prefixEnd_1387975 : Nat := 4983230072969 + 3 ^ 40 * 1387975 * 2
def baseEnd_1387975 : Nat := 26396233756456010189975

theorem tailTrace_1387975 : CollatzResearch.WordTrace tailWord_1387975 prefixEnd_1387975 26396233756456010189975 := by
  unfold tailWord_1387975
  simp only [CollatzResearch.WordTrace]
  refine ⟨50623607146611097102813379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33749071431074064735208919 50623607146611097102813379)
  ·
    refine ⟨75935410719916645654220069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50623607146611097102813379 75935410719916645654220069)
    ·
      refine ⟨14237889509984371060166263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75935410719916645654220069 14237889509984371060166263)
      ·
        refine ⟨21356834264976556590249395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14237889509984371060166263 21356834264976556590249395)
        ·
          refine ⟨32035251397464834885374093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21356834264976556590249395 32035251397464834885374093)
          ·
            refine ⟨12013219274049313082015285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32035251397464834885374093 12013219274049313082015285)
            ·
              refine ⟨1126239306942123101438933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12013219274049313082015285 1126239306942123101438933)
              ·
                refine ⟨26396233756456010189975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1126239306942123101438933 26396233756456010189975)
                ·
                  rfl

theorem cell23_1387975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 7].length) (baseStart_1387975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1387975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1387975 prefixEnd_1387975 := by exact prefixLift 1387975
  have htrace : WordTrace (prefixWord ++ tailWord_1387975) baseStart_1387975 baseEnd_1387975 := by
    simpa [prefixWord, tailWord_1387975, baseEnd_1387975] using wordTrace_append hprefix tailTrace_1387975
  have hstable : (prefixWord ++ tailWord_1387975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1387975).length < 2 ^ (prefixWord ++ tailWord_1387975).sum := by decide
  have hdescent : baseEnd_1387975 < baseStart_1387975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1387975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_1388012 : Nat := 118140960795 + 1388012 * 2 ^ 59
def prefixEnd_1388012 : Nat := 4983230072969 + 3 ^ 40 * 1388012 * 2
def baseEnd_1388012 : Nat := 712717310208528630366655

theorem tailTrace_1388012 : CollatzResearch.WordTrace tailWord_1388012 prefixEnd_1388012 712717310208528630366655 := by
  unfold tailWord_1388012
  simp only [CollatzResearch.WordTrace]
  refine ⟨25312478323738526210955145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33749971098318034947940193 25312478323738526210955145)
  ·
    refine ⟨18984358742803894658216359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25312478323738526210955145 18984358742803894658216359)
    ·
      refine ⟨28476538114205841987324539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18984358742803894658216359 28476538114205841987324539)
      ·
        refine ⟨42714807171308762980986809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28476538114205841987324539 42714807171308762980986809)
        ·
          refine ⟨32036105378481572235740107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42714807171308762980986809 32036105378481572235740107)
          ·
            refine ⟨48054158067722358353610161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32036105378481572235740107 48054158067722358353610161)
            ·
              refine ⟨36040618550791768765207621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48054158067722358353610161 36040618550791768765207621)
              ·
                refine ⟨6757615978273456643476429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36040618550791768765207621 6757615978273456643476429)
                ·
                  refine ⟨2534105991852546241303661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6757615978273456643476429 2534105991852546241303661)
                  ·
                    refine ⟨950289746944704840488873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534105991852546241303661 950289746944704840488873)
                    ·
                      refine ⟨712717310208528630366655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950289746944704840488873 712717310208528630366655)
                      ·
                        rfl

theorem cell23_1388012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_1388012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388012 prefixEnd_1388012 := by exact prefixLift 1388012
  have htrace : WordTrace (prefixWord ++ tailWord_1388012) baseStart_1388012 baseEnd_1388012 := by
    simpa [prefixWord, tailWord_1388012, baseEnd_1388012] using wordTrace_append hprefix tailTrace_1388012
  have hstable : (prefixWord ++ tailWord_1388012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388012).length < 2 ^ (prefixWord ++ tailWord_1388012).sum := by decide
  have hdescent : baseEnd_1388012 < baseStart_1388012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388029 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_1388029 : Nat := 118140960795 + 1388029 * 2 ^ 59
def prefixEnd_1388029 : Nat := 4983230072969 + 3 ^ 40 * 1388029 * 2
def baseEnd_1388029 : Nat := 712726039379655063854077

theorem tailTrace_1388029 : CollatzResearch.WordTrace tailWord_1388029 prefixEnd_1388029 712726039379655063854077 := by
  unfold tailWord_1388029
  simp only [CollatzResearch.WordTrace]
  refine ⟨50625576688415464325279141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33750384458943642883519427 50625576688415464325279141)
  ·
    refine ⟨9492295629077899560989839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50625576688415464325279141 9492295629077899560989839)
    ·
      refine ⟨14238443443616849341484759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492295629077899560989839 14238443443616849341484759)
      ·
        refine ⟨21357665165425274012227139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14238443443616849341484759 21357665165425274012227139)
        ·
          refine ⟨32036497748137911018340709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21357665165425274012227139 32036497748137911018340709)
          ·
            refine ⟨6006843327775858315938883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32036497748137911018340709 6006843327775858315938883)
            ·
              refine ⟨9010264991663787473908325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006843327775858315938883 9010264991663787473908325)
              ·
                refine ⟨1689424685936960151357811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9010264991663787473908325 1689424685936960151357811)
                ·
                  refine ⟨2534137028905440227036717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689424685936960151357811 2534137028905440227036717)
                  ·
                    refine ⟨950301385839540085138769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534137028905440227036717 950301385839540085138769)
                    ·
                      refine ⟨712726039379655063854077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950301385839540085138769 712726039379655063854077)
                      ·
                        rfl

theorem cell23_1388029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_1388029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388029 prefixEnd_1388029 := by exact prefixLift 1388029
  have htrace : WordTrace (prefixWord ++ tailWord_1388029) baseStart_1388029 baseEnd_1388029 := by
    simpa [prefixWord, tailWord_1388029, baseEnd_1388029] using wordTrace_append hprefix tailTrace_1388029
  have hstable : (prefixWord ++ tailWord_1388029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388029).length < 2 ^ (prefixWord ++ tailWord_1388029).sum := by decide
  have hdescent : baseEnd_1388029 < baseStart_1388029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388145 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1388145 : Nat := 118140960795 + 1388145 * 2 ^ 59
def prefixEnd_1388145 : Nat := 4983230072969 + 3 ^ 40 * 1388145 * 2
def baseEnd_1388145 : Nat := 712785603135576610003543

theorem tailTrace_1388145 : CollatzResearch.WordTrace tailWord_1388145 prefixEnd_1388145 712785603135576610003543 := by
  unfold tailWord_1388145
  simp only [CollatzResearch.WordTrace]
  refine ⟨50629807555995216136501889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33753205037330144091001259 50629807555995216136501889)
  ·
    refine ⟨37972355666996412102376417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50629807555995216136501889 37972355666996412102376417)
    ·
      refine ⟨28479266750247309076782313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37972355666996412102376417 28479266750247309076782313)
      ·
        refine ⟨21359450062685481807586735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28479266750247309076782313 21359450062685481807586735)
        ·
          refine ⟨32039175094028222711380103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21359450062685481807586735 32039175094028222711380103)
          ·
            refine ⟨48058762641042334067070155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32039175094028222711380103 48058762641042334067070155)
            ·
              refine ⟨72088143961563501100605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48058762641042334067070155 72088143961563501100605233)
              ·
                refine ⟨54066107971172625825453925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72088143961563501100605233 54066107971172625825453925)
                ·
                  refine ⟨10137395244594867342272611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54066107971172625825453925 10137395244594867342272611)
                  ·
                    refine ⟨15206092866892301013408917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10137395244594867342272611 15206092866892301013408917)
                    ·
                      refine ⟨712785603135576610003543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15206092866892301013408917 712785603135576610003543)
                      ·
                        rfl

theorem cell23_1388145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1388145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388145 prefixEnd_1388145 := by exact prefixLift 1388145
  have htrace : WordTrace (prefixWord ++ tailWord_1388145) baseStart_1388145 baseEnd_1388145 := by
    simpa [prefixWord, tailWord_1388145, baseEnd_1388145] using wordTrace_append hprefix tailTrace_1388145
  have hstable : (prefixWord ++ tailWord_1388145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388145).length < 2 ^ (prefixWord ++ tailWord_1388145).sum := by decide
  have hdescent : baseEnd_1388145 < baseStart_1388145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388149 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1388149 : Nat := 118140960795 + 1388149 * 2 ^ 59
def prefixEnd_1388149 : Nat := 4983230072969 + 3 ^ 40 * 1388149 * 2
def baseEnd_1388149 : Nat := 712787657058194594353525

theorem tailTrace_1388149 : CollatzResearch.WordTrace tailWord_1388149 prefixEnd_1388149 712787657058194594353525 := by
  unfold tailWord_1388149
  simp only [CollatzResearch.WordTrace]
  refine ⟨50629953447980724819647501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33753302298653816546431667 50629953447980724819647501)
  ·
    refine ⟨18986232542992771807367813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50629953447980724819647501 18986232542992771807367813)
    ·
      refine ⟨3559918601811144713881465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18986232542992771807367813 3559918601811144713881465)
      ·
        refine ⟨2669938951358358535411099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3559918601811144713881465 2669938951358358535411099)
        ·
          refine ⟨4004908427037537803116649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669938951358358535411099 4004908427037537803116649)
          ·
            refine ⟨3003681320278153352337487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004908427037537803116649 3003681320278153352337487)
            ·
              refine ⟨4505521980417230028506231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003681320278153352337487 4505521980417230028506231)
              ·
                refine ⟨6758282970625845042759347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505521980417230028506231 6758282970625845042759347)
                ·
                  refine ⟨10137424455938767564139021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758282970625845042759347 10137424455938767564139021)
                  ·
                    refine ⟨3801534170977037836552133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10137424455938767564139021 3801534170977037836552133)
                    ·
                      refine ⟨712787657058194594353525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3801534170977037836552133 712787657058194594353525)
                      ·
                        rfl

theorem cell23_1388149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1388149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388149 prefixEnd_1388149 := by exact prefixLift 1388149
  have htrace : WordTrace (prefixWord ++ tailWord_1388149) baseStart_1388149 baseEnd_1388149 := by
    simpa [prefixWord, tailWord_1388149, baseEnd_1388149] using wordTrace_append hprefix tailTrace_1388149
  have hstable : (prefixWord ++ tailWord_1388149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388149).length < 2 ^ (prefixWord ++ tailWord_1388149).sum := by decide
  have hdescent : baseEnd_1388149 < baseStart_1388149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388155 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 8]
def baseStart_1388155 : Nat := 118140960795 + 1388155 * 2 ^ 59
def prefixEnd_1388155 : Nat := 4983230072969 + 3 ^ 40 * 1388155 * 2
def baseEnd_1388155 : Nat := 79198970882457952319833

theorem tailTrace_1388155 : CollatzResearch.WordTrace tailWord_1388155 prefixEnd_1388155 79198970882457952319833 := by
  unfold tailWord_1388155
  simp only [CollatzResearch.WordTrace]
  refine ⟨50630172285958987844365919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33753448190639325229577279 50630172285958987844365919)
  ·
    refine ⟨75945258428938481766548879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50630172285958987844365919 75945258428938481766548879)
    ·
      refine ⟨113917887643407722649823319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75945258428938481766548879 113917887643407722649823319)
      ·
        refine ⟨170876831465111583974734979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113917887643407722649823319 170876831465111583974734979)
        ·
          refine ⟨256315247197667375962102469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170876831465111583974734979 256315247197667375962102469)
          ·
            refine ⟨48059108849562632992894213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256315247197667375962102469 48059108849562632992894213)
            ·
              refine ⟨9011082909292993686167665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48059108849562632992894213 9011082909292993686167665)
              ·
                refine ⟨6758312181969745264625749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9011082909292993686167665 6758312181969745264625749)
                ·
                  refine ⟨79198970882457952319833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6758312181969745264625749 79198970882457952319833)
                  ·
                    rfl

theorem cell23_1388155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_1388155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388155 prefixEnd_1388155 := by exact prefixLift 1388155
  have htrace : WordTrace (prefixWord ++ tailWord_1388155) baseStart_1388155 baseEnd_1388155 := by
    simpa [prefixWord, tailWord_1388155, baseEnd_1388155] using wordTrace_append hprefix tailTrace_1388155
  have hstable : (prefixWord ++ tailWord_1388155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388155).length < 2 ^ (prefixWord ++ tailWord_1388155).sum := by decide
  have hdescent : baseEnd_1388155 < baseStart_1388155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388185 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_1388185 : Nat := 118140960795 + 1388185 * 2 ^ 59
def prefixEnd_1388185 : Nat := 4983230072969 + 3 ^ 40 * 1388185 * 2
def baseEnd_1388185 : Nat := 237602047453918817834453

theorem tailTrace_1388185 : CollatzResearch.WordTrace tailWord_1388185 prefixEnd_1388185 237602047453918817834453 := by
  unfold tailWord_1388185
  simp only [CollatzResearch.WordTrace]
  refine ⟨50631266475850302967958009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33754177650566868645305339 50631266475850302967958009)
  ·
    refine ⟨37973449856887727225968507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50631266475850302967958009 37973449856887727225968507)
    ·
      refine ⟨56960174785331590838952761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37973449856887727225968507 56960174785331590838952761)
      ·
        refine ⟨42720131088998693129214571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56960174785331590838952761 42720131088998693129214571)
        ·
          refine ⟨64080196633498039693821857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42720131088998693129214571 64080196633498039693821857)
          ·
            refine ⟨48060147475123529770366393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64080196633498039693821857 48060147475123529770366393)
            ·
              refine ⟨36045110606342647327774795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48060147475123529770366393 36045110606342647327774795)
              ·
                refine ⟨54067665909513970991662193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36045110606342647327774795 54067665909513970991662193)
                ·
                  refine ⟨40550749432135478243746645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54067665909513970991662193 40550749432135478243746645)
                  ·
                    refine ⟨237602047453918817834453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40550749432135478243746645 237602047453918817834453)
                    ·
                      rfl

theorem cell23_1388185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_1388185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388185 prefixEnd_1388185 := by exact prefixLift 1388185
  have htrace : WordTrace (prefixWord ++ tailWord_1388185) baseStart_1388185 baseEnd_1388185 := by
    simpa [prefixWord, tailWord_1388185, baseEnd_1388185] using wordTrace_append hprefix tailTrace_1388185
  have hstable : (prefixWord ++ tailWord_1388185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388185).length < 2 ^ (prefixWord ++ tailWord_1388185).sum := by decide
  have hdescent : baseEnd_1388185 < baseStart_1388185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388256 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2]
def baseStart_1388256 : Nat := 118140960795 + 1388256 * 2 ^ 59
def prefixEnd_1388256 : Nat := 4983230072969 + 3 ^ 40 * 1388256 * 2
def baseEnd_1388256 : Nat := 712842599488225675715533

theorem tailTrace_1388256 : CollatzResearch.WordTrace tailWord_1388256 prefixEnd_1388256 712842599488225675715533 := by
  unfold tailWord_1388256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316928029296541046896311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33755904039062054729195081 25316928029296541046896311)
  ·
    refine ⟨37975392043944811570344467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25316928029296541046896311 37975392043944811570344467)
    ·
      refine ⟨56963088065917217355516701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37975392043944811570344467 56963088065917217355516701)
      ·
        refine ⟨21361158024718956508318763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56963088065917217355516701 21361158024718956508318763)
        ·
          refine ⟨32041737037078434762478145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21361158024718956508318763 32041737037078434762478145)
          ·
            refine ⟨24031302777808826071858609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32041737037078434762478145 24031302777808826071858609)
            ·
              refine ⟨18023477083356619553893957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24031302777808826071858609 18023477083356619553893957)
              ·
                refine ⟨3379401953129366166355117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18023477083356619553893957 3379401953129366166355117)
                ·
                  refine ⟨1267275732423512312383169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3379401953129366166355117 1267275732423512312383169)
                  ·
                    refine ⟨950456799317634234287377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1267275732423512312383169 950456799317634234287377)
                    ·
                      refine ⟨712842599488225675715533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950456799317634234287377 712842599488225675715533)
                      ·
                        rfl

theorem cell23_1388256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_1388256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388256 prefixEnd_1388256 := by exact prefixLift 1388256
  have htrace : WordTrace (prefixWord ++ tailWord_1388256) baseStart_1388256 baseEnd_1388256 := by
    simpa [prefixWord, tailWord_1388256, baseEnd_1388256] using wordTrace_append hprefix tailTrace_1388256
  have hstable : (prefixWord ++ tailWord_1388256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388256).length < 2 ^ (prefixWord ++ tailWord_1388256).sum := by decide
  have hdescent : baseEnd_1388256 < baseStart_1388256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388269 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1388269 : Nat := 118140960795 + 1388269 * 2 ^ 59
def prefixEnd_1388269 : Nat := 4983230072969 + 3 ^ 40 * 1388269 * 2
def baseEnd_1388269 : Nat := 712849274736734124852973

theorem tailTrace_1388269 : CollatzResearch.WordTrace tailWord_1388269 prefixEnd_1388269 712849274736734124852973 := by
  unfold tailWord_1388269
  simp only [CollatzResearch.WordTrace]
  refine ⟨50634330207545985314015861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33756220138363990209343907 50634330207545985314015861)
  ·
    refine ⟨4746968456957436123188987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50634330207545985314015861 4746968456957436123188987)
    ·
      refine ⟨7120452685436154184783481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4746968456957436123188987 7120452685436154184783481)
      ·
        refine ⟨5340339514077115638587611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7120452685436154184783481 5340339514077115638587611)
        ·
          refine ⟨8010509271115673457881417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340339514077115638587611 8010509271115673457881417)
          ·
            refine ⟨6007881953336755093411063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8010509271115673457881417 6007881953336755093411063)
            ·
              refine ⟨9011822930005132640116595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007881953336755093411063 9011822930005132640116595)
              ·
                refine ⟨13517734395007698960174893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011822930005132640116595 13517734395007698960174893)
                ·
                  refine ⟨5069150398127887110065585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13517734395007698960174893 5069150398127887110065585)
                  ·
                    refine ⟨3801862798595915332549189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069150398127887110065585 3801862798595915332549189)
                    ·
                      refine ⟨712849274736734124852973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3801862798595915332549189 712849274736734124852973)
                      ·
                        rfl

theorem cell23_1388269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1388269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388269 prefixEnd_1388269 := by exact prefixLift 1388269
  have htrace : WordTrace (prefixWord ++ tailWord_1388269) baseStart_1388269 baseEnd_1388269 := by
    simpa [prefixWord, tailWord_1388269, baseEnd_1388269] using wordTrace_append hprefix tailTrace_1388269
  have hstable : (prefixWord ++ tailWord_1388269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388269).length < 2 ^ (prefixWord ++ tailWord_1388269).sum := by decide
  have hdescent : baseEnd_1388269 < baseStart_1388269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388316 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1388316 : Nat := 118140960795 + 1388316 * 2 ^ 59
def prefixEnd_1388316 : Nat := 4983230072969 + 3 ^ 40 * 1388316 * 2
def baseEnd_1388316 : Nat := 712873408327495440965257

theorem tailTrace_1388316 : CollatzResearch.WordTrace tailWord_1388316 prefixEnd_1388316 712873408327495440965257 := by
  unfold tailWord_1388316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318022219187856170488401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33757362958917141560651201 25318022219187856170488401)
  ·
    refine ⟨18988516664390892127866301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25318022219187856170488401 18988516664390892127866301)
    ·
      refine ⟨7120693749146584547949863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18988516664390892127866301 7120693749146584547949863)
      ·
        refine ⟨10681040623719876821924795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7120693749146584547949863 10681040623719876821924795)
        ·
          refine ⟨16021560935579815232887193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681040623719876821924795 16021560935579815232887193)
          ·
            refine ⟨12016170701684861424665395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16021560935579815232887193 12016170701684861424665395)
            ·
              refine ⟨18024256052527292136998093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016170701684861424665395 18024256052527292136998093)
              ·
                refine ⟨6759096019697734551374285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18024256052527292136998093 6759096019697734551374285)
                ·
                  refine ⟨2534661007386650456765357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6759096019697734551374285 2534661007386650456765357)
                  ·
                    refine ⟨950497877769993921287009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2534661007386650456765357 950497877769993921287009)
                    ·
                      refine ⟨712873408327495440965257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950497877769993921287009 712873408327495440965257)
                      ·
                        rfl

theorem cell23_1388316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1388316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388316 prefixEnd_1388316 := by exact prefixLift 1388316
  have htrace : WordTrace (prefixWord ++ tailWord_1388316) baseStart_1388316 baseEnd_1388316 := by
    simpa [prefixWord, tailWord_1388316, baseEnd_1388316] using wordTrace_append hprefix tailTrace_1388316
  have hstable : (prefixWord ++ tailWord_1388316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388316).length < 2 ^ (prefixWord ++ tailWord_1388316).sum := by decide
  have hdescent : baseEnd_1388316 < baseStart_1388316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388340 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1388340 : Nat := 118140960795 + 1388340 * 2 ^ 59
def prefixEnd_1388340 : Nat := 4983230072969 + 3 ^ 40 * 1388340 * 2
def baseEnd_1388340 : Nat := 712885731863203347065147

theorem tailTrace_1388340 : CollatzResearch.WordTrace tailWord_1388340 prefixEnd_1388340 712885731863203347065147 := by
  unfold tailWord_1388340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318459895144382219925237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33757946526859176293233649 25318459895144382219925237)
  ·
    refine ⟨2373605615169785833117991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25318459895144382219925237 2373605615169785833117991)
    ·
      refine ⟨3560408422754678749676987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373605615169785833117991 3560408422754678749676987)
      ·
        refine ⟨5340612634132018124515481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560408422754678749676987 5340612634132018124515481)
        ·
          refine ⟨4005459475599013593386611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5340612634132018124515481 4005459475599013593386611)
          ·
            refine ⟨6008189213398520390079917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005459475599013593386611 6008189213398520390079917)
            ·
              refine ⟨2253070955024445146279969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6008189213398520390079917 2253070955024445146279969)
              ·
                refine ⟨1689803216268333859709977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253070955024445146279969 1689803216268333859709977)
                ·
                  refine ⟨1267352412201250394782483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689803216268333859709977 1267352412201250394782483)
                  ·
                    refine ⟨1901028618301875592173725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1267352412201250394782483 1901028618301875592173725)
                    ·
                      refine ⟨712885731863203347065147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901028618301875592173725 712885731863203347065147)
                      ·
                        rfl

theorem cell23_1388340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1388340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388340 prefixEnd_1388340 := by exact prefixLift 1388340
  have htrace : WordTrace (prefixWord ++ tailWord_1388340) baseStart_1388340 baseEnd_1388340 := by
    simpa [prefixWord, tailWord_1388340, baseEnd_1388340] using wordTrace_append hprefix tailTrace_1388340
  have hstable : (prefixWord ++ tailWord_1388340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388340).length < 2 ^ (prefixWord ++ tailWord_1388340).sum := by decide
  have hdescent : baseEnd_1388340 < baseStart_1388340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388359 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1388359 : Nat := 118140960795 + 1388359 * 2 ^ 59
def prefixEnd_1388359 : Nat := 4983230072969 + 3 ^ 40 * 1388359 * 2
def baseEnd_1388359 : Nat := 712895487995638772727559

theorem tailTrace_1388359 : CollatzResearch.WordTrace tailWord_1388359 prefixEnd_1388359 712895487995638772727559 := by
  unfold tailWord_1388359
  simp only [CollatzResearch.WordTrace]
  refine ⟨50637612777219930684792131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33758408518146620456528087 50637612777219930684792131)
  ·
    refine ⟨75956419165829896027188197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50637612777219930684792131 75956419165829896027188197)
    ·
      refine ⟨14241828593593105505097787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75956419165829896027188197 14241828593593105505097787)
      ·
        refine ⟨21362742890389658257646681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14241828593593105505097787 21362742890389658257646681)
        ·
          refine ⟨16022057167792243693235011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21362742890389658257646681 16022057167792243693235011)
          ·
            refine ⟨24033085751688365539852517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022057167792243693235011 24033085751688365539852517)
            ·
              refine ⟨4506203578441568538722347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24033085751688365539852517 4506203578441568538722347)
              ·
                refine ⟨6759305367662352808083521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506203578441568538722347 6759305367662352808083521)
                ·
                  refine ⟨5069479025746764606062641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6759305367662352808083521 5069479025746764606062641)
                  ·
                    refine ⟨3802109269310073454546981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069479025746764606062641 3802109269310073454546981)
                    ·
                      refine ⟨712895487995638772727559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3802109269310073454546981 712895487995638772727559)
                      ·
                        rfl

theorem cell23_1388359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1388359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388359 prefixEnd_1388359 := by exact prefixLift 1388359
  have htrace : WordTrace (prefixWord ++ tailWord_1388359) baseStart_1388359 baseEnd_1388359 := by
    simpa [prefixWord, tailWord_1388359, baseEnd_1388359] using wordTrace_append hprefix tailTrace_1388359
  have hstable : (prefixWord ++ tailWord_1388359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388359).length < 2 ^ (prefixWord ++ tailWord_1388359).sum := by decide
  have hdescent : baseEnd_1388359 < baseStart_1388359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388369 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 7]
def baseStart_1388369 : Nat := 118140960795 + 1388369 * 2 ^ 59
def prefixEnd_1388369 : Nat := 4983230072969 + 3 ^ 40 * 1388369 * 2
def baseEnd_1388369 : Nat := 79211180311353748178057

theorem tailTrace_1388369 : CollatzResearch.WordTrace tailWord_1388369 prefixEnd_1388369 79211180311353748178057 := by
  unfold tailWord_1388369
  simp only [CollatzResearch.WordTrace]
  refine ⟨50637977507183702392656161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33758651671455801595104107 50637977507183702392656161)
  ·
    refine ⟨37978483130387776794492121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50637977507183702392656161 37978483130387776794492121)
    ·
      refine ⟨28483862347790832595869091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37978483130387776794492121 28483862347790832595869091)
      ·
        refine ⟨42725793521686248893803637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28483862347790832595869091 42725793521686248893803637)
        ·
          refine ⟨4005543142658085833794091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42725793521686248893803637 4005543142658085833794091)
          ·
            refine ⟨6008314713987128750691137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005543142658085833794091 6008314713987128750691137)
            ·
              refine ⟨4506236035490346563018353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008314713987128750691137 4506236035490346563018353)
              ·
                refine ⟨3379677026617759922263765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506236035490346563018353 3379677026617759922263765)
                ·
                  refine ⟨79211180311353748178057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3379677026617759922263765 79211180311353748178057)
                  ·
                    rfl

theorem cell23_1388369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_1388369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388369 prefixEnd_1388369 := by exact prefixLift 1388369
  have htrace : WordTrace (prefixWord ++ tailWord_1388369) baseStart_1388369 baseEnd_1388369 := by
    simpa [prefixWord, tailWord_1388369, baseEnd_1388369] using wordTrace_append hprefix tailTrace_1388369
  have hstable : (prefixWord ++ tailWord_1388369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388369).length < 2 ^ (prefixWord ++ tailWord_1388369).sum := by decide
  have hdescent : baseEnd_1388369 < baseStart_1388369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388409 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1388409 : Nat := 118140960795 + 1388409 * 2 ^ 59
def prefixEnd_1388409 : Nat := 4983230072969 + 3 ^ 40 * 1388409 * 2
def baseEnd_1388409 : Nat := 712921162028363577102329

theorem tailTrace_1388409 : CollatzResearch.WordTrace tailWord_1388409 prefixEnd_1388409 712921162028363577102329 := by
  unfold tailWord_1388409
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639436427038789224112281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33759624284692526149408187 50639436427038789224112281)
  ·
    refine ⟨37979577320279091918084211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50639436427038789224112281 37979577320279091918084211)
    ·
      refine ⟨56969365980418637877126317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37979577320279091918084211 56969365980418637877126317)
      ·
        refine ⟨21363512242656989203922369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56969365980418637877126317 21363512242656989203922369)
        ·
          refine ⟨16022634181992741902941777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21363512242656989203922369 16022634181992741902941777)
          ·
            refine ⟨12016975636494556427206333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16022634181992741902941777 12016975636494556427206333)
            ·
              refine ⟨4506365863685458660202375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12016975636494556427206333 4506365863685458660202375)
              ·
                refine ⟨6759548795528187990303563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506365863685458660202375 6759548795528187990303563)
                ·
                  refine ⟨10139323193292281985455345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6759548795528187990303563 10139323193292281985455345)
                  ·
                    refine ⟨7604492394969211489091509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10139323193292281985455345 7604492394969211489091509)
                    ·
                      refine ⟨712921162028363577102329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7604492394969211489091509 712921162028363577102329)
                      ·
                        rfl

theorem cell23_1388409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1388409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388409 prefixEnd_1388409 := by exact prefixLift 1388409
  have htrace : WordTrace (prefixWord ++ tailWord_1388409) baseStart_1388409 baseEnd_1388409 := by
    simpa [prefixWord, tailWord_1388409, baseEnd_1388409] using wordTrace_append hprefix tailTrace_1388409
  have hstable : (prefixWord ++ tailWord_1388409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388409).length < 2 ^ (prefixWord ++ tailWord_1388409).sum := by decide
  have hdescent : baseEnd_1388409 < baseStart_1388409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388414 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1388414 : Nat := 118140960795 + 1388414 * 2 ^ 59
def prefixEnd_1388414 : Nat := 4983230072969 + 3 ^ 40 * 1388414 * 2
def baseEnd_1388414 : Nat := 712923729431636057539807

theorem tailTrace_1388414 : CollatzResearch.WordTrace tailWord_1388414 prefixEnd_1388414 712923729431636057539807 := by
  unfold tailWord_1388414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329952349002584384755537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33759745861347116718696197 6329952349002584384755537)
  ·
    refine ⟨4747464261751938288566653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6329952349002584384755537 4747464261751938288566653)
    ·
      refine ⟨1780299098156976858212495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4747464261751938288566653 1780299098156976858212495)
      ·
        refine ⟨2670448647235465287318743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780299098156976858212495 2670448647235465287318743)
        ·
          refine ⟨4005672970853197930978115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670448647235465287318743 4005672970853197930978115)
          ·
            refine ⟨6008509456279796896467173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005672970853197930978115 6008509456279796896467173)
            ·
              refine ⟨1126595523052461918087595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6008509456279796896467173 1126595523052461918087595)
              ·
                refine ⟨1689893284578692877131393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126595523052461918087595 1689893284578692877131393)
                ·
                  refine ⟨1267419963434019657848545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689893284578692877131393 1267419963434019657848545)
                  ·
                    refine ⟨950564972575514743386409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1267419963434019657848545 950564972575514743386409)
                    ·
                      refine ⟨712923729431636057539807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950564972575514743386409 712923729431636057539807)
                      ·
                        rfl

theorem cell23_1388414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1388414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388414 prefixEnd_1388414 := by exact prefixLift 1388414
  have htrace : WordTrace (prefixWord ++ tailWord_1388414) baseStart_1388414 baseEnd_1388414 := by
    simpa [prefixWord, tailWord_1388414, baseEnd_1388414] using wordTrace_append hprefix tailTrace_1388414
  have hstable : (prefixWord ++ tailWord_1388414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388414).length < 2 ^ (prefixWord ++ tailWord_1388414).sum := by decide
  have hdescent : baseEnd_1388414 < baseStart_1388414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388463 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 1, 4]
def baseStart_1388463 : Nat := 118140960795 + 1388463 * 2 ^ 59
def prefixEnd_1388463 : Nat := 4983230072969 + 3 ^ 40 * 1388463 * 2
def baseEnd_1388463 : Nat := 237649629994568788609027

theorem tailTrace_1388463 : CollatzResearch.WordTrace tailWord_1388463 prefixEnd_1388463 237649629994568788609027 := by
  unfold tailWord_1388463
  simp only [CollatzResearch.WordTrace]
  refine ⟨50641405968843156446578043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33760937312562104297718695 50641405968843156446578043)
  ·
    refine ⟨75962108953264734669867065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50641405968843156446578043 75962108953264734669867065)
    ·
      refine ⟨56971581714948551002400299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75962108953264734669867065 56971581714948551002400299)
      ·
        refine ⟨85457372572422826503600449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56971581714948551002400299 85457372572422826503600449)
        ·
          refine ⟨64093029429317119877700337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85457372572422826503600449 64093029429317119877700337)
          ·
            refine ⟨48069772071987839908275253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64093029429317119877700337 48069772071987839908275253)
            ·
              refine ⟨4506541131748859991400805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48069772071987839908275253 4506541131748859991400805)
              ·
                refine ⟨844976462202911248387651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4506541131748859991400805 844976462202911248387651)
                ·
                  refine ⟨1267464693304366872581477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844976462202911248387651 1267464693304366872581477)
                  ·
                    refine ⟨237649629994568788609027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1267464693304366872581477 237649629994568788609027)
                    ·
                      rfl

theorem cell23_1388463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_1388463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388463 prefixEnd_1388463 := by exact prefixLift 1388463
  have htrace : WordTrace (prefixWord ++ tailWord_1388463) baseStart_1388463 baseEnd_1388463 := by
    simpa [prefixWord, tailWord_1388463, baseEnd_1388463] using wordTrace_append hprefix tailTrace_1388463
  have hstable : (prefixWord ++ tailWord_1388463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388463).length < 2 ^ (prefixWord ++ tailWord_1388463).sum := by decide
  have hdescent : baseEnd_1388463 < baseStart_1388463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388513 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_1388513 : Nat := 118140960795 + 1388513 * 2 ^ 59
def prefixEnd_1388513 : Nat := 4983230072969 + 3 ^ 40 * 1388513 * 2
def baseEnd_1388513 : Nat := 712974564016431170201851

theorem tailTrace_1388513 : CollatzResearch.WordTrace tailWord_1388513 prefixEnd_1388513 712974564016431170201851 := by
  unfold tailWord_1388513
  simp only [CollatzResearch.WordTrace]
  refine ⟨50643229618662014985898193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33762153079108009990598795 50643229618662014985898193)
  ·
    refine ⟨37982422213996511239423645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50643229618662014985898193 37982422213996511239423645)
    ·
      refine ⟨14243408330248691714783867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37982422213996511239423645 14243408330248691714783867)
      ·
        refine ⟨21365112495373037572175801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14243408330248691714783867 21365112495373037572175801)
        ·
          refine ⟨16023834371529778179131851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21365112495373037572175801 16023834371529778179131851)
          ·
            refine ⟨24035751557294667268697777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16023834371529778179131851 24035751557294667268697777)
            ·
              refine ⟨18026813667971000451523333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24035751557294667268697777 18026813667971000451523333)
              ·
                refine ⟨3380027562744562584660625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18026813667971000451523333 3380027562744562584660625)
                ·
                  refine ⟨2535020672058421938495469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380027562744562584660625 2535020672058421938495469)
                  ·
                    refine ⟨950632752021908226935801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535020672058421938495469 950632752021908226935801)
                    ·
                      refine ⟨712974564016431170201851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950632752021908226935801 712974564016431170201851)
                      ·
                        rfl

theorem cell23_1388513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_1388513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388513 prefixEnd_1388513 := by exact prefixLift 1388513
  have htrace : WordTrace (prefixWord ++ tailWord_1388513) baseStart_1388513 baseEnd_1388513 := by
    simpa [prefixWord, tailWord_1388513, baseEnd_1388513] using wordTrace_append hprefix tailTrace_1388513
  have hstable : (prefixWord ++ tailWord_1388513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388513).length < 2 ^ (prefixWord ++ tailWord_1388513).sum := by decide
  have hdescent : baseEnd_1388513 < baseStart_1388513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388536 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_1388536 : Nat := 118140960795 + 1388536 * 2 ^ 59
def prefixEnd_1388536 : Nat := 4983230072969 + 3 ^ 40 * 1388536 * 2
def baseEnd_1388536 : Nat := 237662124690494860071415

theorem tailTrace_1388536 : CollatzResearch.WordTrace tailWord_1388536 prefixEnd_1388536 237662124690494860071415 := by
  unfold tailWord_1388536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322034248789344956992731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33762712331719126609323641 25322034248789344956992731)
  ·
    refine ⟨37983051373184017435489097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25322034248789344956992731 37983051373184017435489097)
    ·
      refine ⟨28487288529888013076616823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37983051373184017435489097 28487288529888013076616823)
      ·
        refine ⟨42730932794832019614925235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28487288529888013076616823 42730932794832019614925235)
        ·
          refine ⟨64096399192248029422387853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42730932794832019614925235 64096399192248029422387853)
          ·
            refine ⟨24036149697093011033395445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64096399192248029422387853 24036149697093011033395445)
            ·
              refine ⟨2253389034102469784380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24036149697093011033395445 2253389034102469784380823)
              ·
                refine ⟨3380083551153704676571235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253389034102469784380823 3380083551153704676571235)
                ·
                  refine ⟨5070125326730557014856853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380083551153704676571235 5070125326730557014856853)
                  ·
                    refine ⟨237662124690494860071415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5070125326730557014856853 237662124690494860071415)
                    ·
                      rfl

theorem cell23_1388536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_1388536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388536 prefixEnd_1388536 := by exact prefixLift 1388536
  have htrace : WordTrace (prefixWord ++ tailWord_1388536) baseStart_1388536 baseEnd_1388536 := by
    simpa [prefixWord, tailWord_1388536, baseEnd_1388536] using wordTrace_append hprefix tailTrace_1388536
  have hstable : (prefixWord ++ tailWord_1388536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388536).length < 2 ^ (prefixWord ++ tailWord_1388536).sum := by decide
  have hdescent : baseEnd_1388536 < baseStart_1388536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388554 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_1388554 : Nat := 118140960795 + 1388554 * 2 ^ 59
def prefixEnd_1388554 : Nat := 4983230072969 + 3 ^ 40 * 1388554 * 2
def baseEnd_1388554 : Nat := 712995616723265509789163

theorem tailTrace_1388554 : CollatzResearch.WordTrace tailWord_1388554 prefixEnd_1388554 712995616723265509789163 := by
  unfold tailWord_1388554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661181252878369747035179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33763150007675652658760477 12661181252878369747035179)
  ·
    refine ⟨18991771879317554620552769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12661181252878369747035179 18991771879317554620552769)
    ·
      refine ⟨14243828909488165965414577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18991771879317554620552769 14243828909488165965414577)
      ·
        refine ⟨10682871682116124474060933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14243828909488165965414577 10682871682116124474060933)
        ·
          refine ⟨2003038440396773338886425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10682871682116124474060933 2003038440396773338886425)
          ·
            refine ⟨1502278830297580004164819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003038440396773338886425 1502278830297580004164819)
            ·
              refine ⟨2253418245446370006247229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502278830297580004164819 2253418245446370006247229)
              ·
                refine ⟨845031842042388752342711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2253418245446370006247229 845031842042388752342711)
                ·
                  refine ⟨1267547763063583128514067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845031842042388752342711 1267547763063583128514067)
                  ·
                    refine ⟨1901321644595374692771101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1267547763063583128514067 1901321644595374692771101)
                    ·
                      refine ⟨712995616723265509789163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901321644595374692771101 712995616723265509789163)
                      ·
                        rfl

theorem cell23_1388554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_1388554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388554 prefixEnd_1388554 := by exact prefixLift 1388554
  have htrace : WordTrace (prefixWord ++ tailWord_1388554) baseStart_1388554 baseEnd_1388554 := by
    simpa [prefixWord, tailWord_1388554, baseEnd_1388554] using wordTrace_append hprefix tailTrace_1388554
  have hstable : (prefixWord ++ tailWord_1388554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388554).length < 2 ^ (prefixWord ++ tailWord_1388554).sum := by decide
  have hdescent : baseEnd_1388554 < baseStart_1388554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388556 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1388556 : Nat := 118140960795 + 1388556 * 2 ^ 59
def prefixEnd_1388556 : Nat := 4983230072969 + 3 ^ 40 * 1388556 * 2
def baseEnd_1388556 : Nat := 712996643684574501964153

theorem tailTrace_1388556 : CollatzResearch.WordTrace tailWord_1388556 prefixEnd_1388556 712996643684574501964153 := by
  unfold tailWord_1388556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322398978753116664856761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33763198638337488886475681 25322398978753116664856761)
  ·
    refine ⟨18991799234064837498642571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25322398978753116664856761 18991799234064837498642571)
    ·
      refine ⟨28487698851097256247963857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18991799234064837498642571 28487698851097256247963857)
      ·
        refine ⟨21365774138322942185972893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28487698851097256247963857 21365774138322942185972893)
        ·
          refine ⟨8012165301871103319739835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21365774138322942185972893 8012165301871103319739835)
          ·
            refine ⟨12018247952806654979609753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012165301871103319739835 12018247952806654979609753)
            ·
              refine ⟨9013685964604991234707315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12018247952806654979609753 9013685964604991234707315)
              ·
                refine ⟨13520528946907486852060973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9013685964604991234707315 13520528946907486852060973)
                ·
                  refine ⟨5070198355090307569522865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13520528946907486852060973 5070198355090307569522865)
                  ·
                    refine ⟨3802648766317730677142149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5070198355090307569522865 3802648766317730677142149)
                    ·
                      refine ⟨712996643684574501964153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3802648766317730677142149 712996643684574501964153)
                      ·
                        rfl

theorem cell23_1388556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1388556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388556 prefixEnd_1388556 := by exact prefixLift 1388556
  have htrace : WordTrace (prefixWord ++ tailWord_1388556) baseStart_1388556 baseEnd_1388556 := by
    simpa [prefixWord, tailWord_1388556, baseEnd_1388556] using wordTrace_append hprefix tailTrace_1388556
  have hstable : (prefixWord ++ tailWord_1388556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388556).length < 2 ^ (prefixWord ++ tailWord_1388556).sum := by decide
  have hdescent : baseEnd_1388556 < baseStart_1388556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388563 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 3]
def baseStart_1388563 : Nat := 118140960795 + 1388563 * 2 ^ 59
def prefixEnd_1388563 : Nat := 4983230072969 + 3 ^ 40 * 1388563 * 2
def baseEnd_1388563 : Nat := 713000238049155974576621

theorem tailTrace_1388563 : CollatzResearch.WordTrace tailWord_1388563 prefixEnd_1388563 713000238049155974576621 := by
  unfold tailWord_1388563
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645053268480873525218343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33763368845653915683478895 50645053268480873525218343)
  ·
    refine ⟨75967579902721310287827515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50645053268480873525218343 75967579902721310287827515)
    ·
      refine ⟨113951369854081965431741273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75967579902721310287827515 113951369854081965431741273)
      ·
        refine ⟨85463527390561474073805955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113951369854081965431741273 85463527390561474073805955)
        ·
          refine ⟨128195291085842211110708933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85463527390561474073805955 128195291085842211110708933)
          ·
            refine ⟨24036617078595414583257925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128195291085842211110708933 24036617078595414583257925)
            ·
              refine ⟨4506865702236640234360861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24036617078595414583257925 4506865702236640234360861)
              ·
                refine ⟨1690074638338740087885323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4506865702236640234360861 1690074638338740087885323)
                ·
                  refine ⟨2535111957508110131827985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690074638338740087885323 2535111957508110131827985)
                  ·
                    refine ⟨1901333968131082598870989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535111957508110131827985 1901333968131082598870989)
                    ·
                      refine ⟨713000238049155974576621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901333968131082598870989 713000238049155974576621)
                      ·
                        rfl

theorem cell23_1388563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_1388563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388563 prefixEnd_1388563 := by exact prefixLift 1388563
  have htrace : WordTrace (prefixWord ++ tailWord_1388563) baseStart_1388563 baseEnd_1388563 := by
    simpa [prefixWord, tailWord_1388563, baseEnd_1388563] using wordTrace_append hprefix tailTrace_1388563
  have hstable : (prefixWord ++ tailWord_1388563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388563).length < 2 ^ (prefixWord ++ tailWord_1388563).sum := by decide
  have hdescent : baseEnd_1388563 < baseStart_1388563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388564 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1388564 : Nat := 118140960795 + 1388564 * 2 ^ 59
def prefixEnd_1388564 : Nat := 4983230072969 + 3 ^ 40 * 1388564 * 2
def baseEnd_1388564 : Nat := 713000751529810470664117

theorem tailTrace_1388564 : CollatzResearch.WordTrace tailWord_1388564 prefixEnd_1388564 713000751529810470664117 := by
  unfold tailWord_1388564
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322544870738625348002373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33763393160984833797336497 25322544870738625348002373)
  ·
    refine ⟨4747977163263492252750445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25322544870738625348002373 4747977163263492252750445)
    ·
      refine ⟨1780491436223809594781417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4747977163263492252750445 1780491436223809594781417)
      ·
        refine ⟨1335368577167857196086063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780491436223809594781417 1335368577167857196086063)
        ·
          refine ⟨2003052865751785794129095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335368577167857196086063 2003052865751785794129095)
          ·
            refine ⟨3004579298627678691193643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003052865751785794129095 3004579298627678691193643)
            ·
              refine ⟨4506868947941518036790465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004579298627678691193643 4506868947941518036790465)
              ·
                refine ⟨3380151710956138527592849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506868947941518036790465 3380151710956138527592849)
                ·
                  refine ⟨2535113783217103895694637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380151710956138527592849 2535113783217103895694637)
                  ·
                    refine ⟨950667668706413960885489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535113783217103895694637 950667668706413960885489)
                    ·
                      refine ⟨713000751529810470664117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950667668706413960885489 713000751529810470664117)
                      ·
                        rfl

theorem cell23_1388564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1388564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388564 prefixEnd_1388564 := by exact prefixLift 1388564
  have htrace : WordTrace (prefixWord ++ tailWord_1388564) baseStart_1388564 baseEnd_1388564 := by
    simpa [prefixWord, tailWord_1388564, baseEnd_1388564] using wordTrace_append hprefix tailTrace_1388564
  have hstable : (prefixWord ++ tailWord_1388564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388564).length < 2 ^ (prefixWord ++ tailWord_1388564).sum := by decide
  have hdescent : baseEnd_1388564 < baseStart_1388564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 3, 3, 2]
def baseStart_1388603 : Nat := 118140960795 + 1388603 * 2 ^ 59
def prefixEnd_1388603 : Nat := 4983230072969 + 3 ^ 40 * 1388603 * 2
def baseEnd_1388603 : Nat := 713020777275335818076437

theorem tailTrace_1388603 : CollatzResearch.WordTrace tailWord_1388603 prefixEnd_1388603 713020777275335818076437 := by
  unfold tailWord_1388603
  simp only [CollatzResearch.WordTrace]
  refine ⟨50646512188335960356674463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33764341458890640237782975 50646512188335960356674463)
  ·
    refine ⟨75969768282503940535011695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50646512188335960356674463 75969768282503940535011695)
    ·
      refine ⟨113954652423755910802517543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75969768282503940535011695 113954652423755910802517543)
      ·
        refine ⟨170931978635633866203776315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113954652423755910802517543 170931978635633866203776315)
        ·
          refine ⟨256397967953450799305664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170931978635633866203776315 256397967953450799305664473)
          ·
            refine ⟨192298475965088099479248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256397967953450799305664473 192298475965088099479248355)
            ·
              refine ⟨288447713947632149218872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192298475965088099479248355 288447713947632149218872533)
              ·
                refine ⟨6760493295647628497317325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 288447713947632149218872533 6760493295647628497317325)
                ·
                  refine ⟨2535184985867860686493997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6760493295647628497317325 2535184985867860686493997)
                  ·
                    refine ⟨950694369700447757435249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535184985867860686493997 950694369700447757435249)
                    ·
                      refine ⟨713020777275335818076437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950694369700447757435249 713020777275335818076437)
                      ·
                        rfl

theorem cell23_1388603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3, 2].length) (baseStart_1388603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388603 prefixEnd_1388603 := by exact prefixLift 1388603
  have htrace : WordTrace (prefixWord ++ tailWord_1388603) baseStart_1388603 baseEnd_1388603 := by
    simpa [prefixWord, tailWord_1388603, baseEnd_1388603] using wordTrace_append hprefix tailTrace_1388603
  have hstable : (prefixWord ++ tailWord_1388603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388603).length < 2 ^ (prefixWord ++ tailWord_1388603).sum := by decide
  have hdescent : baseEnd_1388603 < baseStart_1388603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388614 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1388614 : Nat := 118140960795 + 1388614 * 2 ^ 59
def prefixEnd_1388614 : Nat := 4983230072969 + 3 ^ 40 * 1388614 * 2
def baseEnd_1388614 : Nat := 713026425562535275038887

theorem tailTrace_1388614 : CollatzResearch.WordTrace tailWord_1388614 prefixEnd_1388614 713026425562535275038887 := by
  unfold tailWord_1388614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582716043478003413603903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33764608927530739490216597 1582716043478003413603903)
  ·
    refine ⟨2374074065217005120405855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582716043478003413603903 2374074065217005120405855)
    ·
      refine ⟨3561111097825507680608783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374074065217005120405855 3561111097825507680608783)
      ·
        refine ⟨5341666646738261520913175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561111097825507680608783 5341666646738261520913175)
        ·
          refine ⟨8012499970107392281369763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341666646738261520913175 8012499970107392281369763)
          ·
            refine ⟨12018749955161088422054645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012499970107392281369763 12018749955161088422054645)
            ·
              refine ⟨1126757808296352039567623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12018749955161088422054645 1126757808296352039567623)
              ·
                refine ⟨1690136712444528059351435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126757808296352039567623 1690136712444528059351435)
                ·
                  refine ⟨2535205068666792089027153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690136712444528059351435 2535205068666792089027153)
                  ·
                    refine ⟨1901403801500094066770365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535205068666792089027153 1901403801500094066770365)
                    ·
                      refine ⟨713026425562535275038887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901403801500094066770365 713026425562535275038887)
                      ·
                        rfl

theorem cell23_1388614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1388614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388614 prefixEnd_1388614 := by exact prefixLift 1388614
  have htrace : WordTrace (prefixWord ++ tailWord_1388614) baseStart_1388614 baseEnd_1388614 := by
    simpa [prefixWord, tailWord_1388614, baseEnd_1388614] using wordTrace_append hprefix tailTrace_1388614
  have hstable : (prefixWord ++ tailWord_1388614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388614).length < 2 ^ (prefixWord ++ tailWord_1388614).sum := by decide
  have hdescent : baseEnd_1388614 < baseStart_1388614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388620 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1388620 : Nat := 118140960795 + 1388620 * 2 ^ 59
def prefixEnd_1388620 : Nat := 4983230072969 + 3 ^ 40 * 1388620 * 2
def baseEnd_1388620 : Nat := 713029506446462251563859

theorem tailTrace_1388620 : CollatzResearch.WordTrace tailWord_1388620 prefixEnd_1388620 713029506446462251563859 := by
  unfold tailWord_1388620
  simp only [CollatzResearch.WordTrace]
  refine ⟨25323566114637186130021657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33764754819516248173362209 25323566114637186130021657)
  ·
    refine ⟨18992674585977889597516243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25323566114637186130021657 18992674585977889597516243)
    ·
      refine ⟨28489011878966834396274365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18992674585977889597516243 28489011878966834396274365)
      ·
        refine ⟨10683379454612562898602887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28489011878966834396274365 10683379454612562898602887)
        ·
          refine ⟨16025069181918844347904331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10683379454612562898602887 16025069181918844347904331)
          ·
            refine ⟨24037603772878266521856497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16025069181918844347904331 24037603772878266521856497)
            ·
              refine ⟨18028202829658699891392373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24037603772878266521856497 18028202829658699891392373)
              ·
                refine ⟨1690144015280503114818035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18028202829658699891392373 1690144015280503114818035)
                ·
                  refine ⟨2535216022920754672227053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690144015280503114818035 2535216022920754672227053)
                  ·
                    refine ⟨950706008595283002085145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535216022920754672227053 950706008595283002085145)
                    ·
                      refine ⟨713029506446462251563859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950706008595283002085145 713029506446462251563859)
                      ·
                        rfl

theorem cell23_1388620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1388620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388620 prefixEnd_1388620 := by exact prefixLift 1388620
  have htrace : WordTrace (prefixWord ++ tailWord_1388620) baseStart_1388620 baseEnd_1388620 := by
    simpa [prefixWord, tailWord_1388620, baseEnd_1388620] using wordTrace_append hprefix tailTrace_1388620
  have hstable : (prefixWord ++ tailWord_1388620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388620).length < 2 ^ (prefixWord ++ tailWord_1388620).sum := by decide
  have hdescent : baseEnd_1388620 < baseStart_1388620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388630 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1388630 : Nat := 118140960795 + 1388630 * 2 ^ 59
def prefixEnd_1388630 : Nat := 4983230072969 + 3 ^ 40 * 1388630 * 2
def baseEnd_1388630 : Nat := 237678213751002404146271

theorem tailTrace_1388630 : CollatzResearch.WordTrace tailWord_1388630 prefixEnd_1388630 237678213751002404146271 := by
  unfold tailWord_1388630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165468559952383997994209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33764997972825429311938229 3165468559952383997994209)
  ·
    refine ⟨2374101419964287998495657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3165468559952383997994209 2374101419964287998495657)
    ·
      refine ⟨1780576064973215998871743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374101419964287998495657 1780576064973215998871743)
      ·
        refine ⟨2670864097459823998307615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780576064973215998871743 2670864097459823998307615)
        ·
          refine ⟨4006296146189735997461423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670864097459823998307615 4006296146189735997461423)
          ·
            refine ⟨6009444219284603996192135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006296146189735997461423 6009444219284603996192135)
            ·
              refine ⟨9014166328926905994288203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009444219284603996192135 9014166328926905994288203)
              ·
                refine ⟨13521249493390358991432305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014166328926905994288203 13521249493390358991432305)
                ·
                  refine ⟨10140937120042769243574229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13521249493390358991432305 10140937120042769243574229)
                  ·
                    refine ⟨237678213751002404146271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10140937120042769243574229 237678213751002404146271)
                    ·
                      rfl

theorem cell23_1388630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1388630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388630 prefixEnd_1388630 := by exact prefixLift 1388630
  have htrace : WordTrace (prefixWord ++ tailWord_1388630) baseStart_1388630 baseEnd_1388630 := by
    simpa [prefixWord, tailWord_1388630, baseEnd_1388630] using wordTrace_append hprefix tailTrace_1388630
  have hstable : (prefixWord ++ tailWord_1388630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388630).length < 2 ^ (prefixWord ++ tailWord_1388630).sum := by decide
  have hdescent : baseEnd_1388630 < baseStart_1388630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388633 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 4, 2]
def baseStart_1388633 : Nat := 118140960795 + 1388633 * 2 ^ 59
def prefixEnd_1388633 : Nat := 4983230072969 + 3 ^ 40 * 1388633 * 2
def baseEnd_1388633 : Nat := 713036181694970700701299

theorem tailTrace_1388633 : CollatzResearch.WordTrace tailWord_1388633 prefixEnd_1388633 713036181694970700701299 := by
  unfold tailWord_1388633
  simp only [CollatzResearch.WordTrace]
  refine ⟨50647606378227275480266553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33765070918818183653511035 50647606378227275480266553)
  ·
    refine ⟨37985704783670456610199915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50647606378227275480266553 37985704783670456610199915)
    ·
      refine ⟨56978557175505684915299873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37985704783670456610199915 56978557175505684915299873)
      ·
        refine ⟨42733917881629263686474905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56978557175505684915299873 42733917881629263686474905)
        ·
          refine ⟨32050438411221947764856179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42733917881629263686474905 32050438411221947764856179)
          ·
            refine ⟨48075657616832921647284269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32050438411221947764856179 48075657616832921647284269)
            ·
              refine ⟨18028371606312345617731601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48075657616832921647284269 18028371606312345617731601)
              ·
                refine ⟨13521278704734259213298701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18028371606312345617731601 13521278704734259213298701)
                ·
                  refine ⟨5070479514275347204987013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13521278704734259213298701 5070479514275347204987013)
                  ·
                    refine ⟨950714908926627600935065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070479514275347204987013 950714908926627600935065)
                    ·
                      refine ⟨713036181694970700701299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950714908926627600935065 713036181694970700701299)
                      ·
                        rfl

theorem cell23_1388633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_1388633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388633 prefixEnd_1388633 := by exact prefixLift 1388633
  have htrace : WordTrace (prefixWord ++ tailWord_1388633) baseStart_1388633 baseEnd_1388633 := by
    simpa [prefixWord, tailWord_1388633, baseEnd_1388633] using wordTrace_append hprefix tailTrace_1388633
  have hstable : (prefixWord ++ tailWord_1388633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388633).length < 2 ^ (prefixWord ++ tailWord_1388633).sum := by decide
  have hdescent : baseEnd_1388633 < baseStart_1388633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388637 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1388637 : Nat := 118140960795 + 1388637 * 2 ^ 59
def prefixEnd_1388637 : Nat := 4983230072969 + 3 ^ 40 * 1388637 * 2
def baseEnd_1388637 : Nat := 713038235617588685051281

theorem tailTrace_1388637 : CollatzResearch.WordTrace tailWord_1388637 prefixEnd_1388637 713038235617588685051281 := by
  unfold tailWord_1388637
  simp only [CollatzResearch.WordTrace]
  refine ⟨50647752270212784163412165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33765168180141856108941443 50647752270212784163412165)
  ·
    refine ⟨9496453550664897030639781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50647752270212784163412165 9496453550664897030639781)
    ·
      refine ⟨1780585040749668193244959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9496453550664897030639781 1780585040749668193244959)
      ·
        refine ⟨2670877561124502289867439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780585040749668193244959 2670877561124502289867439)
        ·
          refine ⟨4006316341686753434801159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670877561124502289867439 4006316341686753434801159)
          ·
            refine ⟨6009474512530130152201739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006316341686753434801159 6009474512530130152201739)
            ·
              refine ⟨9014211768795195228302609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009474512530130152201739 9014211768795195228302609)
              ·
                refine ⟨6760658826596396421226957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014211768795195228302609 6760658826596396421226957)
                ·
                  refine ⟨2535247059973648657960109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6760658826596396421226957 2535247059973648657960109)
                  ·
                    refine ⟨950717647490118246735041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535247059973648657960109 950717647490118246735041)
                    ·
                      refine ⟨713038235617588685051281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950717647490118246735041 713038235617588685051281)
                      ·
                        rfl

theorem cell23_1388637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1388637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388637 prefixEnd_1388637 := by exact prefixLift 1388637
  have htrace : WordTrace (prefixWord ++ tailWord_1388637) baseStart_1388637 baseEnd_1388637 := by
    simpa [prefixWord, tailWord_1388637, baseEnd_1388637] using wordTrace_append hprefix tailTrace_1388637
  have hstable : (prefixWord ++ tailWord_1388637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388637).length < 2 ^ (prefixWord ++ tailWord_1388637).sum := by decide
  have hdescent : baseEnd_1388637 < baseStart_1388637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388653 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1388653 : Nat := 118140960795 + 1388653 * 2 ^ 59
def prefixEnd_1388653 : Nat := 4983230072969 + 3 ^ 40 * 1388653 * 2
def baseEnd_1388653 : Nat := 713046451308060622451207

theorem tailTrace_1388653 : CollatzResearch.WordTrace tailWord_1388653 prefixEnd_1388653 713046451308060622451207 := by
  unfold tailWord_1388653
  simp only [CollatzResearch.WordTrace]
  refine ⟨50648335838154818895994613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33765557225436545930663075 50648335838154818895994613)
  ·
    refine ⟨4748281484827014271499495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50648335838154818895994613 4748281484827014271499495)
    ·
      refine ⟨7122422227240521407249243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748281484827014271499495 7122422227240521407249243)
      ·
        refine ⟨10683633340860782110873865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7122422227240521407249243 10683633340860782110873865)
        ·
          refine ⟨8012725005645586583155399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10683633340860782110873865 8012725005645586583155399)
          ·
            refine ⟨12019087508468379874733099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012725005645586583155399 12019087508468379874733099)
            ·
              refine ⟨18028631262702569812099649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019087508468379874733099 18028631262702569812099649)
              ·
                refine ⟨13521473447026927359074737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18028631262702569812099649 13521473447026927359074737)
                ·
                  refine ⟨10141105085270195519306053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13521473447026927359074737 10141105085270195519306053)
                  ·
                    refine ⟨1901457203488161659869885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10141105085270195519306053 1901457203488161659869885)
                    ·
                      refine ⟨713046451308060622451207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901457203488161659869885 713046451308060622451207)
                      ·
                        rfl

theorem cell23_1388653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1388653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388653 prefixEnd_1388653 := by exact prefixLift 1388653
  have htrace : WordTrace (prefixWord ++ tailWord_1388653) baseStart_1388653 baseEnd_1388653 := by
    simpa [prefixWord, tailWord_1388653, baseEnd_1388653] using wordTrace_append hprefix tailTrace_1388653
  have hstable : (prefixWord ++ tailWord_1388653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388653).length < 2 ^ (prefixWord ++ tailWord_1388653).sum := by decide
  have hdescent : baseEnd_1388653 < baseStart_1388653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388656 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 9]
def baseStart_1388656 : Nat := 118140960795 + 1388656 * 2 ^ 59
def prefixEnd_1388656 : Nat := 4983230072969 + 3 ^ 40 * 1388656 * 2
def baseEnd_1388656 : Nat := 79227554638891567857077

theorem tailTrace_1388656 : CollatzResearch.WordTrace tailWord_1388656 prefixEnd_1388656 79227554638891567857077 := by
  unfold tailWord_1388656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25324222628571975204176911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33765630171429300272235881 25324222628571975204176911)
  ·
    refine ⟨37986333942857962806265367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25324222628571975204176911 37986333942857962806265367)
    ·
      refine ⟨56979500914286944209398051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37986333942857962806265367 56979500914286944209398051)
      ·
        refine ⟨85469251371430416314097077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56979500914286944209398051 85469251371430416314097077)
        ·
          refine ⟨8012742316071601529446601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85469251371430416314097077 8012742316071601529446601)
          ·
            refine ⟨6009556737053701147084951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012742316071601529446601 6009556737053701147084951)
            ·
              refine ⟨9014335105580551720627427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009556737053701147084951 9014335105580551720627427)
              ·
                refine ⟨13521502658370827580941141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014335105580551720627427 13521502658370827580941141)
                ·
                  refine ⟨79227554638891567857077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13521502658370827580941141 79227554638891567857077)
                  ·
                    rfl

theorem cell23_1388656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_1388656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388656 prefixEnd_1388656 := by exact prefixLift 1388656
  have htrace : WordTrace (prefixWord ++ tailWord_1388656) baseStart_1388656 baseEnd_1388656 := by
    simpa [prefixWord, tailWord_1388656, baseEnd_1388656] using wordTrace_append hprefix tailTrace_1388656
  have hstable : (prefixWord ++ tailWord_1388656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388656).length < 2 ^ (prefixWord ++ tailWord_1388656).sum := by decide
  have hdescent : baseEnd_1388656 < baseStart_1388656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388690 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_1388690 : Nat := 118140960795 + 1388690 * 2 ^ 59
def prefixEnd_1388690 : Nat := 4983230072969 + 3 ^ 40 * 1388690 * 2
def baseEnd_1388690 : Nat := 79229494454697441965393

theorem tailTrace_1388690 : CollatzResearch.WordTrace tailWord_1388690 prefixEnd_1388690 79229494454697441965393 := by
  unfold tailWord_1388690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662421334755193553772881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33766456892680516143394349 12662421334755193553772881)
  ·
    refine ⟨9496816001066395165329661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12662421334755193553772881 9496816001066395165329661)
    ·
      refine ⟨3561306000399898186998623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9496816001066395165329661 3561306000399898186998623)
      ·
        refine ⟨5341959000599847280497935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561306000399898186998623 5341959000599847280497935)
        ·
          refine ⟨8012938500899770920746903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341959000599847280497935 8012938500899770920746903)
          ·
            refine ⟨12019407751349656381120355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012938500899770920746903 12019407751349656381120355)
            ·
              refine ⟨18029111627024484571680533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019407751349656381120355 18029111627024484571680533)
              ·
                refine ⟨845114607516772714297525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18029111627024484571680533 845114607516772714297525)
                ·
                  refine ⟨79229494454697441965393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845114607516772714297525 79229494454697441965393)
                  ·
                    rfl

theorem cell23_1388690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_1388690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388690 prefixEnd_1388690 := by exact prefixLift 1388690
  have htrace : WordTrace (prefixWord ++ tailWord_1388690) baseStart_1388690 baseEnd_1388690 := by
    simpa [prefixWord, tailWord_1388690, baseEnd_1388690] using wordTrace_append hprefix tailTrace_1388690
  have hstable : (prefixWord ++ tailWord_1388690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388690).length < 2 ^ (prefixWord ++ tailWord_1388690).sum := by decide
  have hdescent : baseEnd_1388690 < baseStart_1388690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388703 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 7]
def baseStart_1388703 : Nat := 118140960795 + 1388703 * 2 ^ 59
def prefixEnd_1388703 : Nat := 4983230072969 + 3 ^ 40 * 1388703 * 2
def baseEnd_1388703 : Nat := 237690708446928475608659

theorem tailTrace_1388703 : CollatzResearch.WordTrace tailWord_1388703 prefixEnd_1388703 237690708446928475608659 := by
  unfold tailWord_1388703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50650159487973677435314763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33766772991982451623543175 50650159487973677435314763)
  ·
    refine ⟨75975239231960516152972145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50650159487973677435314763 75975239231960516152972145)
    ·
      refine ⟨56981429423970387114729109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75975239231960516152972145 56981429423970387114729109)
      ·
        refine ⟨2671004504248611896002927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56981429423970387114729109 2671004504248611896002927)
        ·
          refine ⟨4006506756372917844004391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671004504248611896002927 4006506756372917844004391)
          ·
            refine ⟨6009760134559376766006587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006506756372917844004391 6009760134559376766006587)
            ·
              refine ⟨9014640201839065149009881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009760134559376766006587 9014640201839065149009881)
              ·
                refine ⟨6760980151379298861757411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014640201839065149009881 6760980151379298861757411)
                ·
                  refine ⟨10141470227068948292636117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760980151379298861757411 10141470227068948292636117)
                  ·
                    refine ⟨237690708446928475608659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10141470227068948292636117 237690708446928475608659)
                    ·
                      rfl

theorem cell23_1388703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_1388703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388703 prefixEnd_1388703 := by exact prefixLift 1388703
  have htrace : WordTrace (prefixWord ++ tailWord_1388703) baseStart_1388703 baseEnd_1388703 := by
    simpa [prefixWord, tailWord_1388703, baseEnd_1388703] using wordTrace_append hprefix tailTrace_1388703
  have hstable : (prefixWord ++ tailWord_1388703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388703).length < 2 ^ (prefixWord ++ tailWord_1388703).sum := by decide
  have hdescent : baseEnd_1388703 < baseStart_1388703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388723 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4]
def baseStart_1388723 : Nat := 118140960795 + 1388723 * 2 ^ 59
def prefixEnd_1388723 : Nat := 4983230072969 + 3 ^ 40 * 1388723 * 2
def baseEnd_1388723 : Nat := 713082394953875348575885

theorem tailTrace_1388723 : CollatzResearch.WordTrace tailWord_1388723 prefixEnd_1388723 713082394953875348575885 := by
  unfold tailWord_1388723
  simp only [CollatzResearch.WordTrace]
  refine ⟨50650888947901220851042823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33767259298600813900695215 50650888947901220851042823)
  ·
    refine ⟨75976333421851831276564235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50650888947901220851042823 75976333421851831276564235)
    ·
      refine ⟨113964500132777746914846353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75976333421851831276564235 113964500132777746914846353)
      ·
        refine ⟨85473375099583310186134765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113964500132777746914846353 85473375099583310186134765)
        ·
          refine ⟨32052515662343741319800537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85473375099583310186134765 32052515662343741319800537)
          ·
            refine ⟨24039386746757805989850403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32052515662343741319800537 24039386746757805989850403)
            ·
              refine ⟨36059080120136708984775605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24039386746757805989850403 36059080120136708984775605)
              ·
                refine ⟨3380538761262816467322713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36059080120136708984775605 3380538761262816467322713)
                ·
                  refine ⟨2535404070947112350492035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380538761262816467322713 2535404070947112350492035)
                  ·
                    refine ⟨3803106106420668525738053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535404070947112350492035 3803106106420668525738053)
                    ·
                      refine ⟨713082394953875348575885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3803106106420668525738053 713082394953875348575885)
                      ·
                        rfl

theorem cell23_1388723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_1388723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388723 prefixEnd_1388723 := by exact prefixLift 1388723
  have htrace : WordTrace (prefixWord ++ tailWord_1388723) baseStart_1388723 baseEnd_1388723 := by
    simpa [prefixWord, tailWord_1388723, baseEnd_1388723] using wordTrace_append hprefix tailTrace_1388723
  have hstable : (prefixWord ++ tailWord_1388723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388723).length < 2 ^ (prefixWord ++ tailWord_1388723).sum := by decide
  have hdescent : baseEnd_1388723 < baseStart_1388723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388737 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1388737 : Nat := 118140960795 + 1388737 * 2 ^ 59
def prefixEnd_1388737 : Nat := 4983230072969 + 3 ^ 40 * 1388737 * 2
def baseEnd_1388737 : Nat := 237696527894346097933607

theorem tailTrace_1388737 : CollatzResearch.WordTrace tailWord_1388737 prefixEnd_1388737 237696527894346097933607 := by
  unfold tailWord_1388737
  simp only [CollatzResearch.WordTrace]
  refine ⟨50651399569850501242052465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33767599713233667494701643 50651399569850501242052465)
  ·
    refine ⟨37988549677387875931539349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50651399569850501242052465 37988549677387875931539349)
    ·
      refine ⟨1780713266127556684290907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37988549677387875931539349 1780713266127556684290907)
      ·
        refine ⟨2671069899191335026436361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780713266127556684290907 2671069899191335026436361)
        ·
          refine ⟨2003302424393501269827271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671069899191335026436361 2003302424393501269827271)
          ·
            refine ⟨3004953636590251904740907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003302424393501269827271 3004953636590251904740907)
            ·
              refine ⟨4507430454885377857111361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004953636590251904740907 4507430454885377857111361)
              ·
                refine ⟨3380572841164033392833521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507430454885377857111361 3380572841164033392833521)
                ·
                  refine ⟨2535429630873025044625141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380572841164033392833521 2535429630873025044625141)
                  ·
                    refine ⟨237696527894346097933607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2535429630873025044625141 237696527894346097933607)
                    ·
                      rfl

theorem cell23_1388737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1388737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388737 prefixEnd_1388737 := by exact prefixLift 1388737
  have htrace : WordTrace (prefixWord ++ tailWord_1388737) baseStart_1388737 baseEnd_1388737 := by
    simpa [prefixWord, tailWord_1388737, baseEnd_1388737] using wordTrace_append hprefix tailTrace_1388737
  have hstable : (prefixWord ++ tailWord_1388737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388737).length < 2 ^ (prefixWord ++ tailWord_1388737).sum := by decide
  have hdescent : baseEnd_1388737 < baseStart_1388737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388740 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1388740 : Nat := 118140960795 + 1388740 * 2 ^ 59
def prefixEnd_1388740 : Nat := 4983230072969 + 3 ^ 40 * 1388740 * 2
def baseEnd_1388740 : Nat := 713091124125001782063307

theorem tailTrace_1388740 : CollatzResearch.WordTrace tailWord_1388740 prefixEnd_1388740 713091124125001782063307 := by
  unfold tailWord_1388740
  simp only [CollatzResearch.WordTrace]
  refine ⟨25325754494419816377205837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33767672659226421836274449 25325754494419816377205837)
  ·
    refine ⟨9497157935407431141452189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25325754494419816377205837 9497157935407431141452189)
    ·
      refine ⟨3561434225777786678044571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9497157935407431141452189 3561434225777786678044571)
      ·
        refine ⟨5342151338666680017066857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561434225777786678044571 5342151338666680017066857)
        ·
          refine ⟨4006613504000010012800143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342151338666680017066857 4006613504000010012800143)
          ·
            refine ⟨6009920256000015019200215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006613504000010012800143 6009920256000015019200215)
            ·
              refine ⟨9014880384000022528800323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009920256000015019200215 9014880384000022528800323)
              ·
                refine ⟨13522320576000033793200485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014880384000022528800323 13522320576000033793200485)
                ·
                  refine ⟨2535435108000006336225091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13522320576000033793200485 2535435108000006336225091)
                  ·
                    refine ⟨3803152662000009504337637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535435108000006336225091 3803152662000009504337637)
                    ·
                      refine ⟨713091124125001782063307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3803152662000009504337637 713091124125001782063307)
                      ·
                        rfl

theorem cell23_1388740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1388740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388740 prefixEnd_1388740 := by exact prefixLift 1388740
  have htrace : WordTrace (prefixWord ++ tailWord_1388740) baseStart_1388740 baseEnd_1388740 := by
    simpa [prefixWord, tailWord_1388740, baseEnd_1388740] using wordTrace_append hprefix tailTrace_1388740
  have hstable : (prefixWord ++ tailWord_1388740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388740).length < 2 ^ (prefixWord ++ tailWord_1388740).sum := by decide
  have hdescent : baseEnd_1388740 < baseStart_1388740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388834 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_1388834 : Nat := 118140960795 + 1388834 * 2 ^ 59
def prefixEnd_1388834 : Nat := 4983230072969 + 3 ^ 40 * 1388834 * 2
def baseEnd_1388834 : Nat := 713139391306524414287875

theorem tailTrace_1388834 : CollatzResearch.WordTrace tailWord_1388834 prefixEnd_1388834 713139391306524414287875 := by
  unfold tailWord_1388834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663734362624771702083389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33769958300332724538889037 12663734362624771702083389)
  ·
    refine ⟨4748900385984289388281271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12663734362624771702083389 4748900385984289388281271)
    ·
      refine ⟨7123350578976434082421907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748900385984289388281271 7123350578976434082421907)
      ·
        refine ⟨10685025868464651123632861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123350578976434082421907 10685025868464651123632861)
        ·
          refine ⟨4006884700674244171362323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10685025868464651123632861 4006884700674244171362323)
          ·
            refine ⟨6010327051011366257043485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006884700674244171362323 6010327051011366257043485)
            ·
              refine ⟨2253872644129262346391307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6010327051011366257043485 2253872644129262346391307)
              ·
                refine ⟨3380808966193893519586961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253872644129262346391307 3380808966193893519586961)
                ·
                  refine ⟨2535606724645420139690221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380808966193893519586961 2535606724645420139690221)
                  ·
                    refine ⟨950852521742032552383833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2535606724645420139690221 950852521742032552383833)
                    ·
                      refine ⟨713139391306524414287875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950852521742032552383833 713139391306524414287875)
                      ·
                        rfl

theorem cell23_1388834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_1388834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388834 prefixEnd_1388834 := by exact prefixLift 1388834
  have htrace : WordTrace (prefixWord ++ tailWord_1388834) baseStart_1388834 baseEnd_1388834 := by
    simpa [prefixWord, tailWord_1388834, baseEnd_1388834] using wordTrace_append hprefix tailTrace_1388834
  have hstable : (prefixWord ++ tailWord_1388834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388834).length < 2 ^ (prefixWord ++ tailWord_1388834).sum := by decide
  have hdescent : baseEnd_1388834 < baseStart_1388834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388847 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 1, 1, 4]
def baseStart_1388847 : Nat := 118140960795 + 1388847 * 2 ^ 59
def prefixEnd_1388847 : Nat := 4983230072969 + 3 ^ 40 * 1388847 * 2
def baseEnd_1388847 : Nat := 713146066555032863425315

theorem tailTrace_1388847 : CollatzResearch.WordTrace tailWord_1388847 prefixEnd_1388847 713146066555032863425315 := by
  unfold tailWord_1388847
  simp only [CollatzResearch.WordTrace]
  refine ⟨50655411599451990028556795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33770274399634660019037863 50655411599451990028556795)
  ·
    refine ⟨75983117399177985042835193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50655411599451990028556795 75983117399177985042835193)
    ·
      refine ⟨56987338049383488782126395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75983117399177985042835193 56987338049383488782126395)
      ·
        refine ⟨85481007074075233173189593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56987338049383488782126395 85481007074075233173189593)
        ·
          refine ⟨64110755305556424879892195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85481007074075233173189593 64110755305556424879892195)
          ·
            refine ⟨96166132958334637319838293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64110755305556424879892195 96166132958334637319838293)
            ·
              refine ⟨1126946870605484031091855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 96166132958334637319838293 1126946870605484031091855)
              ·
                refine ⟨1690420305908226046637783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126946870605484031091855 1690420305908226046637783)
                ·
                  refine ⟨2535630458862339069956675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690420305908226046637783 2535630458862339069956675)
                  ·
                    refine ⟨3803445688293508604935013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535630458862339069956675 3803445688293508604935013)
                    ·
                      refine ⟨713146066555032863425315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3803445688293508604935013 713146066555032863425315)
                      ·
                        rfl

theorem cell23_1388847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 1, 4].length) (baseStart_1388847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388847 prefixEnd_1388847 := by exact prefixLift 1388847
  have htrace : WordTrace (prefixWord ++ tailWord_1388847) baseStart_1388847 baseEnd_1388847 := by
    simpa [prefixWord, tailWord_1388847, baseEnd_1388847] using wordTrace_append hprefix tailTrace_1388847
  have hstable : (prefixWord ++ tailWord_1388847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388847).length < 2 ^ (prefixWord ++ tailWord_1388847).sum := by decide
  have hdescent : baseEnd_1388847 < baseStart_1388847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388853 : List Nat := [1, 3, 3, 1, 2, 1, 12]
def baseStart_1388853 : Nat := 118140960795 + 1388853 * 2 ^ 59
def prefixEnd_1388853 : Nat := 4983230072969 + 3 ^ 40 * 1388853 * 2
def baseEnd_1388853 : Nat := 8804310462209380740127

theorem tailTrace_1388853 : CollatzResearch.WordTrace tailWord_1388853 prefixEnd_1388853 8804310462209380740127 := by
  unfold tailWord_1388853
  simp only [CollatzResearch.WordTrace]
  refine ⟨50655630437430253053275213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33770420291620168702183475 50655630437430253053275213)
  ·
    refine ⟨18995861414036344894978205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50655630437430253053275213 18995861414036344894978205)
    ·
      refine ⟨7123448030263629335616827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18995861414036344894978205 7123448030263629335616827)
      ·
        refine ⟨10685172045395444003425241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123448030263629335616827 10685172045395444003425241)
        ·
          refine ⟨8013879034046583002568931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10685172045395444003425241 8013879034046583002568931)
          ·
            refine ⟨12020818551069874503853397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013879034046583002568931 12020818551069874503853397)
            ·
              refine ⟨8804310462209380740127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 12020818551069874503853397 8804310462209380740127)
              ·
                rfl

theorem cell23_1388853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 12].length) (baseStart_1388853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388853 prefixEnd_1388853 := by exact prefixLift 1388853
  have htrace : WordTrace (prefixWord ++ tailWord_1388853) baseStart_1388853 baseEnd_1388853 := by
    simpa [prefixWord, tailWord_1388853, baseEnd_1388853] using wordTrace_append hprefix tailTrace_1388853
  have hstable : (prefixWord ++ tailWord_1388853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388853).length < 2 ^ (prefixWord ++ tailWord_1388853).sum := by decide
  have hdescent : baseEnd_1388853 < baseStart_1388853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388857 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_1388857 : Nat := 118140960795 + 1388857 * 2 ^ 59
def prefixEnd_1388857 : Nat := 4983230072969 + 3 ^ 40 * 1388857 * 2
def baseEnd_1388857 : Nat := 237717067120525941433423

theorem tailTrace_1388857 : CollatzResearch.WordTrace tailWord_1388857 prefixEnd_1388857 237717067120525941433423 := by
  unfold tailWord_1388857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50655776329415761736420825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33770517552943841157613883 50655776329415761736420825)
  ·
    refine ⟨37991832247061821302315619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50655776329415761736420825 37991832247061821302315619)
    ·
      refine ⟨56987748370592731953473429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37991832247061821302315619 56987748370592731953473429)
      ·
        refine ⟨2671300704871534310319067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56987748370592731953473429 2671300704871534310319067)
        ·
          refine ⟨4006951057307301465478601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671300704871534310319067 4006951057307301465478601)
          ·
            refine ⟨3005213292980476099108951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006951057307301465478601 3005213292980476099108951)
            ·
              refine ⟨4507819939470714148663427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005213292980476099108951 4507819939470714148663427)
              ·
                refine ⟨6761729909206071222995141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507819939470714148663427 6761729909206071222995141)
                ·
                  refine ⟨1267824357976138354311589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6761729909206071222995141 1267824357976138354311589)
                  ·
                    refine ⟨237717067120525941433423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1267824357976138354311589 237717067120525941433423)
                    ·
                      rfl

theorem cell23_1388857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_1388857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388857 prefixEnd_1388857 := by exact prefixLift 1388857
  have htrace : WordTrace (prefixWord ++ tailWord_1388857) baseStart_1388857 baseEnd_1388857 := by
    simpa [prefixWord, tailWord_1388857, baseEnd_1388857] using wordTrace_append hprefix tailTrace_1388857
  have hstable : (prefixWord ++ tailWord_1388857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388857).length < 2 ^ (prefixWord ++ tailWord_1388857).sum := by decide
  have hdescent : baseEnd_1388857 < baseStart_1388857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388884 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1388884 : Nat := 118140960795 + 1388884 * 2 ^ 59
def prefixEnd_1388884 : Nat := 4983230072969 + 3 ^ 40 * 1388884 * 2
def baseEnd_1388884 : Nat := 713165065339249218662645

theorem tailTrace_1388884 : CollatzResearch.WordTrace tailWord_1388884 prefixEnd_1388884 713165065339249218662645 := by
  unfold tailWord_1388884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25328380550158972673826853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33771174066878630231769137 25328380550158972673826853)
  ·
    refine ⟨4749071353154807376342535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25328380550158972673826853 4749071353154807376342535)
    ·
      refine ⟨7123607029732211064513803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4749071353154807376342535 7123607029732211064513803)
      ·
        refine ⟨10685410544598316596770705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123607029732211064513803 10685410544598316596770705)
        ·
          refine ⟨8014057908448737447578029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10685410544598316596770705 8014057908448737447578029)
          ·
            refine ⟨3005271715668276542841761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8014057908448737447578029 3005271715668276542841761)
            ·
              refine ⟨2253953786751207407131321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005271715668276542841761 2253953786751207407131321)
              ·
                refine ⟨1690465340063405555348491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253953786751207407131321 1690465340063405555348491)
                ·
                  refine ⟨2535698010095108333022737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690465340063405555348491 2535698010095108333022737)
                  ·
                    refine ⟨1901773507571331249767053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535698010095108333022737 1901773507571331249767053)
                    ·
                      refine ⟨713165065339249218662645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1901773507571331249767053 713165065339249218662645)
                      ·
                        rfl

theorem cell23_1388884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1388884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388884 prefixEnd_1388884 := by exact prefixLift 1388884
  have htrace : WordTrace (prefixWord ++ tailWord_1388884) baseStart_1388884 baseEnd_1388884 := by
    simpa [prefixWord, tailWord_1388884, baseEnd_1388884] using wordTrace_append hprefix tailTrace_1388884
  have hstable : (prefixWord ++ tailWord_1388884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388884).length < 2 ^ (prefixWord ++ tailWord_1388884).sum := by decide
  have hdescent : baseEnd_1388884 < baseStart_1388884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388898 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1388898 : Nat := 118140960795 + 1388898 * 2 ^ 59
def prefixEnd_1388898 : Nat := 4983230072969 + 3 ^ 40 * 1388898 * 2
def baseEnd_1388898 : Nat := 713172254068412163887581

theorem tailTrace_1388898 : CollatzResearch.WordTrace tailWord_1388898 prefixEnd_1388898 713172254068412163887581 := by
  unfold tailWord_1388898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664317930566806434665837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33771514481511483825775565 12664317930566806434665837)
  ·
    refine ⟨4749119223962552412999689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12664317930566806434665837 4749119223962552412999689)
    ·
      refine ⟨3561839417971914309749767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4749119223962552412999689 3561839417971914309749767)
      ·
        refine ⟨5342759126957871464624651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561839417971914309749767 5342759126957871464624651)
        ·
          refine ⟨8014138690436807196936977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342759126957871464624651 8014138690436807196936977)
          ·
            refine ⟨6010604017827605397702733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8014138690436807196936977 6010604017827605397702733)
            ·
              refine ⟨2253976506685352024138525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6010604017827605397702733 2253976506685352024138525)
              ·
                refine ⟨845241190007007009051947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2253976506685352024138525 845241190007007009051947)
                ·
                  refine ⟨1267861785010510513577921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845241190007007009051947 1267861785010510513577921)
                  ·
                    refine ⟨950896338757882885183441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1267861785010510513577921 950896338757882885183441)
                    ·
                      refine ⟨713172254068412163887581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950896338757882885183441 713172254068412163887581)
                      ·
                        rfl

theorem cell23_1388898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1388898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388898 prefixEnd_1388898 := by exact prefixLift 1388898
  have htrace : WordTrace (prefixWord ++ tailWord_1388898) baseStart_1388898 baseEnd_1388898 := by
    simpa [prefixWord, tailWord_1388898, baseEnd_1388898] using wordTrace_append hprefix tailTrace_1388898
  have hstable : (prefixWord ++ tailWord_1388898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388898).length < 2 ^ (prefixWord ++ tailWord_1388898).sum := by decide
  have hdescent : baseEnd_1388898 < baseStart_1388898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388940 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1388940 : Nat := 118140960795 + 1388940 * 2 ^ 59
def prefixEnd_1388940 : Nat := 4983230072969 + 3 ^ 40 * 1388940 * 2
def baseEnd_1388940 : Nat := 713193820255900999562387

theorem tailTrace_1388940 : CollatzResearch.WordTrace tailWord_1388940 prefixEnd_1388940 713193820255900999562387 := by
  unfold tailWord_1388940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25329401794057533455846137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33772535725410044607794849 25329401794057533455846137)
  ·
    refine ⟨18997051345543150091884603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25329401794057533455846137 18997051345543150091884603)
    ·
      refine ⟨28495577018314725137826905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18997051345543150091884603 28495577018314725137826905)
      ·
        refine ⟨21371682763736043853370179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28495577018314725137826905 21371682763736043853370179)
        ·
          refine ⟨32057524145604065780055269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21371682763736043853370179 32057524145604065780055269)
          ·
            refine ⟨6010785777300762333760363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32057524145604065780055269 6010785777300762333760363)
            ·
              refine ⟨9016178665951143500640545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010785777300762333760363 9016178665951143500640545)
              ·
                refine ⟨6762133999463357625480409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9016178665951143500640545 6762133999463357625480409)
                ·
                  refine ⟨5071600499597518219110307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762133999463357625480409 5071600499597518219110307)
                  ·
                    refine ⟨7607400749396277328665461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5071600499597518219110307 7607400749396277328665461)
                    ·
                      refine ⟨713193820255900999562387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7607400749396277328665461 713193820255900999562387)
                      ·
                        rfl

theorem cell23_1388940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1388940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388940 prefixEnd_1388940 := by exact prefixLift 1388940
  have htrace : WordTrace (prefixWord ++ tailWord_1388940) baseStart_1388940 baseEnd_1388940 := by
    simpa [prefixWord, tailWord_1388940, baseEnd_1388940] using wordTrace_append hprefix tailTrace_1388940
  have hstable : (prefixWord ++ tailWord_1388940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388940).length < 2 ^ (prefixWord ++ tailWord_1388940).sum := by decide
  have hdescent : baseEnd_1388940 < baseStart_1388940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1388954 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1388954 : Nat := 118140960795 + 1388954 * 2 ^ 59
def prefixEnd_1388954 : Nat := 4983230072969 + 3 ^ 40 * 1388954 * 2
def baseEnd_1388954 : Nat := 713201008985063944787323

theorem tailTrace_1388954 : CollatzResearch.WordTrace tailWord_1388954 prefixEnd_1388954 713201008985063944787323 := by
  unfold tailWord_1388954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664828552516086825675479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33772876140042898201801277 12664828552516086825675479)
  ·
    refine ⟨18997242828774130238513219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12664828552516086825675479 18997242828774130238513219)
    ·
      refine ⟨28495864243161195357769829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18997242828774130238513219 28495864243161195357769829)
      ·
        refine ⟨5342974545592724129581843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28495864243161195357769829 5342974545592724129581843)
        ·
          refine ⟨8014461818389086194372765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342974545592724129581843 8014461818389086194372765)
          ·
            refine ⟨3005423181895907322889787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8014461818389086194372765 3005423181895907322889787)
            ·
              refine ⟨4508134772843860984334681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005423181895907322889787 4508134772843860984334681)
              ·
                refine ⟨3381101079632895738251011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508134772843860984334681 3381101079632895738251011)
                ·
                  refine ⟨5071651619449343607376517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381101079632895738251011 5071651619449343607376517)
                  ·
                    refine ⟨950934678646751926383097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071651619449343607376517 950934678646751926383097)
                    ·
                      refine ⟨713201008985063944787323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 950934678646751926383097 713201008985063944787323)
                      ·
                        rfl

theorem cell23_1388954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1388954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1388954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1388954 prefixEnd_1388954 := by exact prefixLift 1388954
  have htrace : WordTrace (prefixWord ++ tailWord_1388954) baseStart_1388954 baseEnd_1388954 := by
    simpa [prefixWord, tailWord_1388954, baseEnd_1388954] using wordTrace_append hprefix tailTrace_1388954
  have hstable : (prefixWord ++ tailWord_1388954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1388954).length < 2 ^ (prefixWord ++ tailWord_1388954).sum := by decide
  have hdescent : baseEnd_1388954 < baseStart_1388954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1388954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389040 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1389040 : Nat := 118140960795 + 1389040 * 2 ^ 59
def prefixEnd_1389040 : Nat := 4983230072969 + 3 ^ 40 * 1389040 * 2
def baseEnd_1389040 : Nat := 713245168321350608311927

theorem tailTrace_1389040 : CollatzResearch.WordTrace tailWord_1389040 prefixEnd_1389040 713245168321350608311927 := by
  unfold tailWord_1389040
  simp only [CollatzResearch.WordTrace]
  refine ⟨25331225443876391995166287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33774967258501855993555049 25331225443876391995166287)
  ·
    refine ⟨37996838165814587992749431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25331225443876391995166287 37996838165814587992749431)
    ·
      refine ⟨56995257248721881989124147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37996838165814587992749431 56995257248721881989124147)
      ·
        refine ⟨85492885873082822983686221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56995257248721881989124147 85492885873082822983686221)
        ·
          refine ⟨32059832202406058618882333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85492885873082822983686221 32059832202406058618882333)
          ·
            refine ⟨12022437075902271982080875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32059832202406058618882333 12022437075902271982080875)
            ·
              refine ⟨18033655613853407973121313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12022437075902271982080875 18033655613853407973121313)
              ·
                refine ⟨13525241710390055979840985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18033655613853407973121313 13525241710390055979840985)
                ·
                  refine ⟨10143931282792541984880739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13525241710390055979840985 10143931282792541984880739)
                  ·
                    refine ⟨15215896924188812977321109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10143931282792541984880739 15215896924188812977321109)
                    ·
                      refine ⟨713245168321350608311927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15215896924188812977321109 713245168321350608311927)
                      ·
                        rfl

theorem cell23_1389040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1389040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389040 prefixEnd_1389040 := by exact prefixLift 1389040
  have htrace : WordTrace (prefixWord ++ tailWord_1389040) baseStart_1389040 baseEnd_1389040 := by
    simpa [prefixWord, tailWord_1389040, baseEnd_1389040] using wordTrace_append hprefix tailTrace_1389040
  have hstable : (prefixWord ++ tailWord_1389040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389040).length < 2 ^ (prefixWord ++ tailWord_1389040).sum := by decide
  have hdescent : baseEnd_1389040 < baseStart_1389040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389088 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_1389088 : Nat := 118140960795 + 1389088 * 2 ^ 59
def prefixEnd_1389088 : Nat := 4983230072969 + 3 ^ 40 * 1389088 * 2
def baseEnd_1389088 : Nat := 237756605130922140170569

theorem tailTrace_1389088 : CollatzResearch.WordTrace tailWord_1389088 prefixEnd_1389088 237756605130922140170569 := by
  unfold tailWord_1389088
  simp only [CollatzResearch.WordTrace]
  refine ⟨25332100795789444094039959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33776134394385925458719945 25332100795789444094039959)
  ·
    refine ⟨37998151193684166141059939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25332100795789444094039959 37998151193684166141059939)
    ·
      refine ⟨56997226790526249211589909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37998151193684166141059939 56997226790526249211589909)
      ·
        refine ⟨2671745005805917931793277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56997226790526249211589909 2671745005805917931793277)
        ·
          refine ⟨1001904377177219224422479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2671745005805917931793277 1001904377177219224422479)
          ·
            refine ⟨1502856565765828836633719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001904377177219224422479 1502856565765828836633719)
            ·
              refine ⟨2254284848648743254950579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502856565765828836633719 2254284848648743254950579)
              ·
                refine ⟨3381427272973114882425869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254284848648743254950579 3381427272973114882425869)
                ·
                  refine ⟨1268035227364918080909701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3381427272973114882425869 1268035227364918080909701)
                  ·
                    refine ⟨237756605130922140170569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1268035227364918080909701 237756605130922140170569)
                    ·
                      rfl

theorem cell23_1389088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_1389088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389088 prefixEnd_1389088 := by exact prefixLift 1389088
  have htrace : WordTrace (prefixWord ++ tailWord_1389088) baseStart_1389088 baseEnd_1389088 := by
    simpa [prefixWord, tailWord_1389088, baseEnd_1389088] using wordTrace_append hprefix tailTrace_1389088
  have hstable : (prefixWord ++ tailWord_1389088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389088).length < 2 ^ (prefixWord ++ tailWord_1389088).sum := by decide
  have hdescent : baseEnd_1389088 < baseStart_1389088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389114 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_1389114 : Nat := 118140960795 + 1389114 * 2 ^ 59
def prefixEnd_1389114 : Nat := 4983230072969 + 3 ^ 40 * 1389114 * 2
def baseEnd_1389114 : Nat := 237761055296594439595529

theorem tailTrace_1389114 : CollatzResearch.WordTrace tailWord_1389114 prefixEnd_1389114 237761055296594439595529 := by
  unfold tailWord_1389114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12666287472371173657131599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33776766592989796419017597 12666287472371173657131599)
  ·
    refine ⟨18999431208556760485697399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12666287472371173657131599 18999431208556760485697399)
    ·
      refine ⟨28499146812835140728546099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18999431208556760485697399 28499146812835140728546099)
      ·
        refine ⟨42748720219252711092819149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28499146812835140728546099 42748720219252711092819149)
        ·
          refine ⟨16030770082219766659807181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42748720219252711092819149 16030770082219766659807181)
          ·
            refine ⟨6011538780832412497427693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16030770082219766659807181 6011538780832412497427693)
            ·
              refine ⟨2254327042812154686535385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6011538780832412497427693 2254327042812154686535385)
              ·
                refine ⟨1690745282109116014901539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254327042812154686535385 1690745282109116014901539)
                ·
                  refine ⟨2536117923163674022352309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690745282109116014901539 2536117923163674022352309)
                  ·
                    refine ⟨237761055296594439595529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2536117923163674022352309 237761055296594439595529)
                    ·
                      rfl

theorem cell23_1389114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_1389114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389114 prefixEnd_1389114 := by exact prefixLift 1389114
  have htrace : WordTrace (prefixWord ++ tailWord_1389114) baseStart_1389114 baseEnd_1389114 := by
    simpa [prefixWord, tailWord_1389114, baseEnd_1389114] using wordTrace_append hprefix tailTrace_1389114
  have hstable : (prefixWord ++ tailWord_1389114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389114).length < 2 ^ (prefixWord ++ tailWord_1389114).sum := by decide
  have hdescent : baseEnd_1389114 < baseStart_1389114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389121 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1389121 : Nat := 118140960795 + 1389121 * 2 ^ 59
def prefixEnd_1389121 : Nat := 4983230072969 + 3 ^ 40 * 1389121 * 2
def baseEnd_1389121 : Nat := 713286760254364791399055

theorem tailTrace_1389121 : CollatzResearch.WordTrace tailWord_1389121 prefixEnd_1389121 713286760254364791399055 := by
  unfold tailWord_1389121
  simp only [CollatzResearch.WordTrace]
  refine ⟨50665405200459334824031217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33776936800306223216020811 50665405200459334824031217)
  ·
    refine ⟨37999053900344501118023413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50665405200459334824031217 37999053900344501118023413)
    ·
      refine ⟨3562411303157296979814695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37999053900344501118023413 3562411303157296979814695)
      ·
        refine ⟨5343616954735945469722043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562411303157296979814695 5343616954735945469722043)
        ·
          refine ⟨8015425432103918204583065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343616954735945469722043 8015425432103918204583065)
          ·
            refine ⟨6011569074077938653437299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8015425432103918204583065 6011569074077938653437299)
            ·
              refine ⟨9017353611116907980155949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011569074077938653437299 9017353611116907980155949)
              ·
                refine ⟨3381507604168840492558481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9017353611116907980155949 3381507604168840492558481)
                ·
                  refine ⟨2536130703126630369418861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3381507604168840492558481 2536130703126630369418861)
                  ·
                    refine ⟨951049013672486388532073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536130703126630369418861 951049013672486388532073)
                    ·
                      refine ⟨713286760254364791399055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951049013672486388532073 713286760254364791399055)
                      ·
                        rfl

theorem cell23_1389121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1389121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389121 prefixEnd_1389121 := by exact prefixLift 1389121
  have htrace : WordTrace (prefixWord ++ tailWord_1389121) baseStart_1389121 baseEnd_1389121 := by
    simpa [prefixWord, tailWord_1389121, baseEnd_1389121] using wordTrace_append hprefix tailTrace_1389121
  have hstable : (prefixWord ++ tailWord_1389121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389121).length < 2 ^ (prefixWord ++ tailWord_1389121).sum := by decide
  have hdescent : baseEnd_1389121 < baseStart_1389121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389127 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1389127 : Nat := 118140960795 + 1389127 * 2 ^ 59
def prefixEnd_1389127 : Nat := 4983230072969 + 3 ^ 40 * 1389127 * 2
def baseEnd_1389127 : Nat := 237763280379430589308009

theorem tailTrace_1389127 : CollatzResearch.WordTrace tailWord_1389127 prefixEnd_1389127 237763280379430589308009 := by
  unfold tailWord_1389127
  simp only [CollatzResearch.WordTrace]
  refine ⟨50665624038437597848749635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33777082692291731899166423 50665624038437597848749635)
  ·
    refine ⟨75998436057656396773124453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50665624038437597848749635 75998436057656396773124453)
    ·
      refine ⟨14249706760810574394960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75998436057656396773124453 14249706760810574394960835)
      ·
        refine ⟨21374560141215861592441253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249706760810574394960835 21374560141215861592441253)
        ·
          refine ⟨4007730026477974048582735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21374560141215861592441253 4007730026477974048582735)
          ·
            refine ⟨6011595039716961072874103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007730026477974048582735 6011595039716961072874103)
            ·
              refine ⟨9017392559575441609311155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011595039716961072874103 9017392559575441609311155)
              ·
                refine ⟨13526088839363162413966733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017392559575441609311155 13526088839363162413966733)
                ·
                  refine ⟨5072283314761185905237525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13526088839363162413966733 5072283314761185905237525)
                  ·
                    refine ⟨237763280379430589308009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5072283314761185905237525 237763280379430589308009)
                    ·
                      rfl

theorem cell23_1389127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1389127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389127 prefixEnd_1389127 := by exact prefixLift 1389127
  have htrace : WordTrace (prefixWord ++ tailWord_1389127) baseStart_1389127 baseEnd_1389127 := by
    simpa [prefixWord, tailWord_1389127, baseEnd_1389127] using wordTrace_append hprefix tailTrace_1389127
  have hstable : (prefixWord ++ tailWord_1389127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389127).length < 2 ^ (prefixWord ++ tailWord_1389127).sum := by decide
  have hdescent : baseEnd_1389127 < baseStart_1389127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389134 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_1389134 : Nat := 118140960795 + 1389134 * 2 ^ 59
def prefixEnd_1389134 : Nat := 4983230072969 + 3 ^ 40 * 1389134 * 2
def baseEnd_1389134 : Nat := 713293435502873240536495

theorem tailTrace_1389134 : CollatzResearch.WordTrace tailWord_1389134 prefixEnd_1389134 713293435502873240536495 := by
  unfold tailWord_1389134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333234918676529755531807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33777252899608158696169637 6333234918676529755531807)
  ·
    refine ⟨9499852378014794633297711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333234918676529755531807 9499852378014794633297711)
    ·
      refine ⟨14249778567022191949946567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499852378014794633297711 14249778567022191949946567)
      ·
        refine ⟨21374667850533287924919851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249778567022191949946567 21374667850533287924919851)
        ·
          refine ⟨32062001775799931887379777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21374667850533287924919851 32062001775799931887379777)
          ·
            refine ⟨24046501331849948915534833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32062001775799931887379777 24046501331849948915534833)
            ·
              refine ⟨18034875998887461686651125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24046501331849948915534833 18034875998887461686651125)
              ·
                refine ⟨1690769624895699533123543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18034875998887461686651125 1690769624895699533123543)
                ·
                  refine ⟨2536154437343549299685315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690769624895699533123543 2536154437343549299685315)
                  ·
                    refine ⟨3804231656015323949527973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536154437343549299685315 3804231656015323949527973)
                    ·
                      refine ⟨713293435502873240536495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3804231656015323949527973 713293435502873240536495)
                      ·
                        rfl

theorem cell23_1389134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_1389134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389134 prefixEnd_1389134 := by exact prefixLift 1389134
  have htrace : WordTrace (prefixWord ++ tailWord_1389134) baseStart_1389134 baseEnd_1389134 := by
    simpa [prefixWord, tailWord_1389134, baseEnd_1389134] using wordTrace_append hprefix tailTrace_1389134
  have hstable : (prefixWord ++ tailWord_1389134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389134).length < 2 ^ (prefixWord ++ tailWord_1389134).sum := by decide
  have hdescent : baseEnd_1389134 < baseStart_1389134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389144 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_1389144 : Nat := 118140960795 + 1389144 * 2 ^ 59
def prefixEnd_1389144 : Nat := 4983230072969 + 3 ^ 40 * 1389144 * 2
def baseEnd_1389144 : Nat := 237766190103139400470483

theorem tailTrace_1389144 : CollatzResearch.WordTrace tailWord_1389144 prefixEnd_1389144 237766190103139400470483 := by
  unfold tailWord_1389144
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333122039688004876059243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33777496052917339834745657 25333122039688004876059243)
  ·
    refine ⟨37999683059532007314088865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333122039688004876059243 37999683059532007314088865)
    ·
      refine ⟨28499762294649005485566649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37999683059532007314088865 28499762294649005485566649)
      ·
        refine ⟨21374821720986754114174987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28499762294649005485566649 21374821720986754114174987)
        ·
          refine ⟨32062232581480131171262481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21374821720986754114174987 32062232581480131171262481)
          ·
            refine ⟨24046674436110098378446861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32062232581480131171262481 24046674436110098378446861)
            ·
              refine ⟨9017502913541286891917573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24046674436110098378446861 9017502913541286891917573)
              ·
                refine ⟨1690781796288991292234545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9017502913541286891917573 1690781796288991292234545)
                ·
                  refine ⟨1268086347216743469175909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690781796288991292234545 1268086347216743469175909)
                  ·
                    refine ⟨237766190103139400470483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1268086347216743469175909 237766190103139400470483)
                    ·
                      rfl

theorem cell23_1389144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_1389144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389144 prefixEnd_1389144 := by exact prefixLift 1389144
  have htrace : WordTrace (prefixWord ++ tailWord_1389144) baseStart_1389144 baseEnd_1389144 := by
    simpa [prefixWord, tailWord_1389144, baseEnd_1389144] using wordTrace_append hprefix tailTrace_1389144
  have hstable : (prefixWord ++ tailWord_1389144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389144).length < 2 ^ (prefixWord ++ tailWord_1389144).sum := by decide
  have hdescent : baseEnd_1389144 < baseStart_1389144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389168 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2]
def baseStart_1389168 : Nat := 118140960795 + 1389168 * 2 ^ 59
def prefixEnd_1389168 : Nat := 4983230072969 + 3 ^ 40 * 1389168 * 2
def baseEnd_1389168 : Nat := 713310893845126107511339

theorem tailTrace_1389168 : CollatzResearch.WordTrace tailWord_1389168 prefixEnd_1389168 713310893845126107511339 := by
  unfold tailWord_1389168
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333559715644530925496079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33778079620859374567328105 25333559715644530925496079)
  ·
    refine ⟨38000339573466796388244119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333559715644530925496079 38000339573466796388244119)
    ·
      refine ⟨57000509360200194582366179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38000339573466796388244119 57000509360200194582366179)
      ·
        refine ⟨85500764040300291873549269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57000509360200194582366179 85500764040300291873549269)
        ·
          refine ⟨2003924157194538090786311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85500764040300291873549269 2003924157194538090786311)
          ·
            refine ⟨3005886235791807136179467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003924157194538090786311 3005886235791807136179467)
            ·
              refine ⟨4508829353687710704269201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005886235791807136179467 4508829353687710704269201)
              ·
                refine ⟨3381622015265783028201901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508829353687710704269201 3381622015265783028201901)
                ·
                  refine ⟨1268108255724668635575713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3381622015265783028201901 1268108255724668635575713)
                  ·
                    refine ⟨951081191793501476681785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268108255724668635575713 951081191793501476681785)
                    ·
                      refine ⟨713310893845126107511339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951081191793501476681785 713310893845126107511339)
                      ·
                        rfl

theorem cell23_1389168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2].length) (baseStart_1389168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389168 prefixEnd_1389168 := by exact prefixLift 1389168
  have htrace : WordTrace (prefixWord ++ tailWord_1389168) baseStart_1389168 baseEnd_1389168 := by
    simpa [prefixWord, tailWord_1389168, baseEnd_1389168] using wordTrace_append hprefix tailTrace_1389168
  have hstable : (prefixWord ++ tailWord_1389168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389168).length < 2 ^ (prefixWord ++ tailWord_1389168).sum := by decide
  have hdescent : baseEnd_1389168 < baseStart_1389168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389184 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_1389184 : Nat := 118140960795 + 1389184 * 2 ^ 59
def prefixEnd_1389184 : Nat := 4983230072969 + 3 ^ 40 * 1389184 * 2
def baseEnd_1389184 : Nat := 713319109535598044911265

theorem tailTrace_1389184 : CollatzResearch.WordTrace tailWord_1389184 prefixEnd_1389184 713319109535598044911265 := by
  unfold tailWord_1389184
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333851499615548291787303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33778468666154064389049737 25333851499615548291787303)
  ·
    refine ⟨38000777249423322437680955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333851499615548291787303 38000777249423322437680955)
    ·
      refine ⟨57001165874134983656521433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38000777249423322437680955 57001165874134983656521433)
      ·
        refine ⟨42750874405601237742391075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57001165874134983656521433 42750874405601237742391075)
        ·
          refine ⟨64126311608401856613586613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42750874405601237742391075 64126311608401856613586613)
          ·
            refine ⟨6011841713287674057523745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64126311608401856613586613 6011841713287674057523745)
            ·
              refine ⟨4508881284965755543142809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011841713287674057523745 4508881284965755543142809)
              ·
                refine ⟨3381660963724316657357107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508881284965755543142809 3381660963724316657357107)
                ·
                  refine ⟨5072491445586474986035661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381660963724316657357107 5072491445586474986035661)
                  ·
                    refine ⟨1902184292094928119763373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5072491445586474986035661 1902184292094928119763373)
                    ·
                      refine ⟨713319109535598044911265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902184292094928119763373 713319109535598044911265)
                      ·
                        rfl

theorem cell23_1389184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_1389184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389184 prefixEnd_1389184 := by exact prefixLift 1389184
  have htrace : WordTrace (prefixWord ++ tailWord_1389184) baseStart_1389184 baseEnd_1389184 := by
    simpa [prefixWord, tailWord_1389184, baseEnd_1389184] using wordTrace_append hprefix tailTrace_1389184
  have hstable : (prefixWord ++ tailWord_1389184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389184).length < 2 ^ (prefixWord ++ tailWord_1389184).sum := by decide
  have hdescent : baseEnd_1389184 < baseStart_1389184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389185 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1389185 : Nat := 118140960795 + 1389185 * 2 ^ 59
def prefixEnd_1389185 : Nat := 4983230072969 + 3 ^ 40 * 1389185 * 2
def baseEnd_1389185 : Nat := 713319623016252540998761

theorem tailTrace_1389185 : CollatzResearch.WordTrace tailWord_1389185 prefixEnd_1389185 713319623016252540998761 := by
  unfold tailWord_1389185
  simp only [CollatzResearch.WordTrace]
  refine ⟨50667739472227473754361009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33778492981484982502907339 50667739472227473754361009)
  ·
    refine ⟨38000804604170605315770757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50667739472227473754361009 38000804604170605315770757)
    ·
      refine ⟨7125150863281988496707017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38000804604170605315770757 7125150863281988496707017)
      ·
        refine ⟨5343863147461491372530263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7125150863281988496707017 5343863147461491372530263)
        ·
          refine ⟨8015794721192237058795395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343863147461491372530263 8015794721192237058795395)
          ·
            refine ⟨12023692081788355588193093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015794721192237058795395 12023692081788355588193093)
            ·
              refine ⟨2254442265335316672786205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12023692081788355588193093 2254442265335316672786205)
              ·
                refine ⟨845415849500743752294827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254442265335316672786205 845415849500743752294827)
                ·
                  refine ⟨1268123774251115628442241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845415849500743752294827 1268123774251115628442241)
                  ·
                    refine ⟨951092830688336721331681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268123774251115628442241 951092830688336721331681)
                    ·
                      refine ⟨713319623016252540998761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951092830688336721331681 713319623016252540998761)
                      ·
                        rfl

theorem cell23_1389185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1389185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389185 prefixEnd_1389185 := by exact prefixLift 1389185
  have htrace : WordTrace (prefixWord ++ tailWord_1389185) baseStart_1389185 baseEnd_1389185 := by
    simpa [prefixWord, tailWord_1389185, baseEnd_1389185] using wordTrace_append hprefix tailTrace_1389185
  have hstable : (prefixWord ++ tailWord_1389185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389185).length < 2 ^ (prefixWord ++ tailWord_1389185).sum := by decide
  have hdescent : baseEnd_1389185 < baseStart_1389185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389188 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_1389188 : Nat := 118140960795 + 1389188 * 2 ^ 59
def prefixEnd_1389188 : Nat := 4983230072969 + 3 ^ 40 * 1389188 * 2
def baseEnd_1389188 : Nat := 713321163458216029261247

theorem tailTrace_1389188 : CollatzResearch.WordTrace tailWord_1389188 prefixEnd_1389188 713321163458216029261247 := by
  unfold tailWord_1389188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333924445608302633360109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33778565927477736844480145 25333924445608302633360109)
  ·
    refine ⟨9500221667103113487510041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25333924445608302633360109 9500221667103113487510041)
    ·
      refine ⟨7125166250327335115632531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9500221667103113487510041 7125166250327335115632531)
      ·
        refine ⟨10687749375491002673448797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7125166250327335115632531 10687749375491002673448797)
        ·
          refine ⟨4007906015809126002543299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10687749375491002673448797 4007906015809126002543299)
          ·
            refine ⟨6011859023713689003814949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007906015809126002543299 6011859023713689003814949)
            ·
              refine ⟨1127223566946316688215303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6011859023713689003814949 1127223566946316688215303)
              ·
                refine ⟨1690835350419475032322955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127223566946316688215303 1690835350419475032322955)
                ·
                  refine ⟨2536253025629212548484433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690835350419475032322955 2536253025629212548484433)
                  ·
                    refine ⟨1902189769221909411363325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2536253025629212548484433 1902189769221909411363325)
                    ·
                      refine ⟨713321163458216029261247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902189769221909411363325 713321163458216029261247)
                      ·
                        rfl

theorem cell23_1389188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_1389188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389188 prefixEnd_1389188 := by exact prefixLift 1389188
  have htrace : WordTrace (prefixWord ++ tailWord_1389188) baseStart_1389188 baseEnd_1389188 := by
    simpa [prefixWord, tailWord_1389188, baseEnd_1389188] using wordTrace_append hprefix tailTrace_1389188
  have hstable : (prefixWord ++ tailWord_1389188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389188).length < 2 ^ (prefixWord ++ tailWord_1389188).sum := by decide
  have hdescent : baseEnd_1389188 < baseStart_1389188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389244 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1389244 : Nat := 118140960795 + 1389244 * 2 ^ 59
def prefixEnd_1389244 : Nat := 4983230072969 + 3 ^ 40 * 1389244 * 2
def baseEnd_1389244 : Nat := 713349918374867810160989

theorem tailTrace_1389244 : CollatzResearch.WordTrace tailWord_1389244 prefixEnd_1389244 713349918374867810160989 := by
  unfold tailWord_1389244
  simp only [CollatzResearch.WordTrace]
  refine ⟨25334945689506863415379393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33779927586009151220505857 25334945689506863415379393)
  ·
    refine ⟨19001209267130147561534545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25334945689506863415379393 19001209267130147561534545)
    ·
      refine ⟨14250906950347610671150909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19001209267130147561534545 14250906950347610671150909)
      ·
        refine ⟨5344090106380354001681591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14250906950347610671150909 5344090106380354001681591)
        ·
          refine ⟨8016135159570531002522387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344090106380354001681591 8016135159570531002522387)
          ·
            refine ⟨12024202739355796503783581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016135159570531002522387 12024202739355796503783581)
            ·
              refine ⟨4509076027258423688918843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12024202739355796503783581 4509076027258423688918843)
              ·
                refine ⟨6763614040887635533378265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509076027258423688918843 6763614040887635533378265)
                ·
                  refine ⟨5072710530665726650033699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763614040887635533378265 5072710530665726650033699)
                  ·
                    refine ⟨7609065795998589975050549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072710530665726650033699 7609065795998589975050549)
                    ·
                      refine ⟨713349918374867810160989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7609065795998589975050549 713349918374867810160989)
                      ·
                        rfl

theorem cell23_1389244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1389244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389244 prefixEnd_1389244 := by exact prefixLift 1389244
  have htrace : WordTrace (prefixWord ++ tailWord_1389244) baseStart_1389244 baseEnd_1389244 := by
    simpa [prefixWord, tailWord_1389244, baseEnd_1389244] using wordTrace_append hprefix tailTrace_1389244
  have hstable : (prefixWord ++ tailWord_1389244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389244).length < 2 ^ (prefixWord ++ tailWord_1389244).sum := by decide
  have hdescent : baseEnd_1389244 < baseStart_1389244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389258 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_1389258 : Nat := 118140960795 + 1389258 * 2 ^ 59
def prefixEnd_1389258 : Nat := 4983230072969 + 3 ^ 40 * 1389258 * 2
def baseEnd_1389258 : Nat := 713357107104030755385925

theorem tailTrace_1389258 : CollatzResearch.WordTrace tailWord_1389258 prefixEnd_1389258 713357107104030755385925 := by
  unfold tailWord_1389258
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667600500240751805442107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33780268000642004814512285 12667600500240751805442107)
  ·
    refine ⟨19001400750361127708163161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667600500240751805442107 19001400750361127708163161)
    ·
      refine ⟨14251050562770845781122371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19001400750361127708163161 14251050562770845781122371)
      ·
        refine ⟨21376575844156268671683557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14251050562770845781122371 21376575844156268671683557)
        ·
          refine ⟨4008107970779300375940667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21376575844156268671683557 4008107970779300375940667)
          ·
            refine ⟨6012161956168950563911001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008107970779300375940667 6012161956168950563911001)
            ·
              refine ⟨4509121467126712922933251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012161956168950563911001 4509121467126712922933251)
              ·
                refine ⟨6763682200690069384399877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509121467126712922933251 6763682200690069384399877)
                ·
                  refine ⟨1268190412629388009574977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6763682200690069384399877 1268190412629388009574977)
                  ·
                    refine ⟨951142809472041007181233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268190412629388009574977 951142809472041007181233)
                    ·
                      refine ⟨713357107104030755385925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951142809472041007181233 713357107104030755385925)
                      ·
                        rfl

theorem cell23_1389258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_1389258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389258 prefixEnd_1389258 := by exact prefixLift 1389258
  have htrace : WordTrace (prefixWord ++ tailWord_1389258) baseStart_1389258 baseEnd_1389258 := by
    simpa [prefixWord, tailWord_1389258, baseEnd_1389258] using wordTrace_append hprefix tailTrace_1389258
  have hstable : (prefixWord ++ tailWord_1389258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389258).length < 2 ^ (prefixWord ++ tailWord_1389258).sum := by decide
  have hdescent : baseEnd_1389258 < baseStart_1389258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389269 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1389269 : Nat := 118140960795 + 1389269 * 2 ^ 59
def prefixEnd_1389269 : Nat := 4983230072969 + 3 ^ 40 * 1389269 * 2
def baseEnd_1389269 : Nat := 713362755391230212348375

theorem tailTrace_1389269 : CollatzResearch.WordTrace tailWord_1389269 prefixEnd_1389269 713362755391230212348375 := by
  unfold tailWord_1389269
  simp only [CollatzResearch.WordTrace]
  refine ⟨50670803203923156100418861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33780535469282104066945907 50670803203923156100418861)
  ·
    refine ⟨19001551201471183537657073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50670803203923156100418861 19001551201471183537657073)
    ·
      refine ⟨14251163401103387653242805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19001551201471183537657073 14251163401103387653242805)
      ·
        refine ⟨1336046568853442592491513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14251163401103387653242805 1336046568853442592491513)
        ·
          refine ⟨1002034926640081944368635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336046568853442592491513 1002034926640081944368635)
          ·
            refine ⟨1503052389960122916552953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002034926640081944368635 1503052389960122916552953)
            ·
              refine ⟨1127289292470092187414715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1503052389960122916552953 1127289292470092187414715)
              ·
                refine ⟨1690933938705138281122073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127289292470092187414715 1690933938705138281122073)
                ·
                  refine ⟨1268200454028853710841555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690933938705138281122073 1268200454028853710841555)
                  ·
                    refine ⟨1902300681043280566262333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1268200454028853710841555 1902300681043280566262333)
                    ·
                      refine ⟨713362755391230212348375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902300681043280566262333 713362755391230212348375)
                      ·
                        rfl

theorem cell23_1389269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1389269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389269 prefixEnd_1389269 := by exact prefixLift 1389269
  have htrace : WordTrace (prefixWord ++ tailWord_1389269) baseStart_1389269 baseEnd_1389269 := by
    simpa [prefixWord, tailWord_1389269, baseEnd_1389269] using wordTrace_append hprefix tailTrace_1389269
  have hstable : (prefixWord ++ tailWord_1389269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389269).length < 2 ^ (prefixWord ++ tailWord_1389269).sum := by decide
  have hdescent : baseEnd_1389269 < baseStart_1389269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389274 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_1389274 : Nat := 118140960795 + 1389274 * 2 ^ 59
def prefixEnd_1389274 : Nat := 4983230072969 + 3 ^ 40 * 1389274 * 2
def baseEnd_1389274 : Nat := 713365322794502692785851

theorem tailTrace_1389274 : CollatzResearch.WordTrace tailWord_1389274 prefixEnd_1389274 713365322794502692785851 := by
  unfold tailWord_1389274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667746392226260488587719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33780657045936694636233917 12667746392226260488587719)
  ·
    refine ⟨19001619588339390732881579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667746392226260488587719 19001619588339390732881579)
    ·
      refine ⟨28502429382509086099322369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19001619588339390732881579 28502429382509086099322369)
      ·
        refine ⟨21376822036881814574491777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28502429382509086099322369 21376822036881814574491777)
        ·
          refine ⟨16032616527661360930868833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21376822036881814574491777 16032616527661360930868833)
          ·
            refine ⟨12024462395746020698151625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16032616527661360930868833 12024462395746020698151625)
            ·
              refine ⟨9018346796809515523613719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12024462395746020698151625 9018346796809515523613719)
              ·
                refine ⟨13527520195214273285420579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9018346796809515523613719 13527520195214273285420579)
                ·
                  refine ⟨20291280292821409928130869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13527520195214273285420579 20291280292821409928130869)
                  ·
                    refine ⟨1902307527452007180762269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20291280292821409928130869 1902307527452007180762269)
                    ·
                      refine ⟨713365322794502692785851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902307527452007180762269 713365322794502692785851)
                      ·
                        rfl

theorem cell23_1389274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_1389274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389274 prefixEnd_1389274 := by exact prefixLift 1389274
  have htrace : WordTrace (prefixWord ++ tailWord_1389274) baseStart_1389274 baseEnd_1389274 := by
    simpa [prefixWord, tailWord_1389274, baseEnd_1389274] using wordTrace_append hprefix tailTrace_1389274
  have hstable : (prefixWord ++ tailWord_1389274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389274).length < 2 ^ (prefixWord ++ tailWord_1389274).sum := by decide
  have hdescent : baseEnd_1389274 < baseStart_1389274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389307 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 8]
def baseStart_1389307 : Nat := 118140960795 + 1389307 * 2 ^ 59
def prefixEnd_1389307 : Nat := 4983230072969 + 3 ^ 40 * 1389307 * 2
def baseEnd_1389307 : Nat := 237794089218700354557733

theorem tailTrace_1389307 : CollatzResearch.WordTrace tailWord_1389307 prefixEnd_1389307 237794089218700354557733 := by
  unfold tailWord_1389307
  simp only [CollatzResearch.WordTrace]
  refine ⟨50672189177785488590302175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33781459451856992393534783 50672189177785488590302175)
  ·
    refine ⟨76008283766678232885453263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50672189177785488590302175 76008283766678232885453263)
    ·
      refine ⟨114012425650017349328179895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76008283766678232885453263 114012425650017349328179895)
      ·
        refine ⟨171018638475026023992269843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114012425650017349328179895 171018638475026023992269843)
        ·
          refine ⟨256527957712539035988404765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171018638475026023992269843 256527957712539035988404765)
          ·
            refine ⟨96197984142202138495651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256527957712539035988404765 96197984142202138495651787)
            ·
              refine ⟨144296976213303207743477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96197984142202138495651787 144296976213303207743477681)
              ·
                refine ⟨108222732159977405807608261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144296976213303207743477681 108222732159977405807608261)
                ·
                  refine ⟨20291762279995763588926549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108222732159977405807608261 20291762279995763588926549)
                  ·
                    refine ⟨237794089218700354557733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20291762279995763588926549 237794089218700354557733)
                    ·
                      rfl

theorem cell23_1389307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_1389307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389307 prefixEnd_1389307 := by exact prefixLift 1389307
  have htrace : WordTrace (prefixWord ++ tailWord_1389307) baseStart_1389307 baseEnd_1389307 := by
    simpa [prefixWord, tailWord_1389307, baseEnd_1389307] using wordTrace_append hprefix tailTrace_1389307
  have hstable : (prefixWord ++ tailWord_1389307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389307).length < 2 ^ (prefixWord ++ tailWord_1389307).sum := by decide
  have hdescent : baseEnd_1389307 < baseStart_1389307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389331 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 4, 2]
def baseStart_1389331 : Nat := 118140960795 + 1389331 * 2 ^ 59
def prefixEnd_1389331 : Nat := 4983230072969 + 3 ^ 40 * 1389331 * 2
def baseEnd_1389331 : Nat := 713394591191808969773089

theorem tailTrace_1389331 : CollatzResearch.WordTrace tailWord_1389331 prefixEnd_1389331 713394591191808969773089 := by
  unfold tailWord_1389331
  simp only [CollatzResearch.WordTrace]
  refine ⟨50673064529698540689175847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33782043019799027126117231 50673064529698540689175847)
  ·
    refine ⟨76009596794547811033763771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50673064529698540689175847 76009596794547811033763771)
    ·
      refine ⟨114014395191821716550645657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76009596794547811033763771 114014395191821716550645657)
      ·
        refine ⟨85510796393866287412984243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114014395191821716550645657 85510796393866287412984243)
        ·
          refine ⟨128266194590799431119476365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85510796393866287412984243 128266194590799431119476365)
          ·
            refine ⟨48099822971549786669803637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128266194590799431119476365 48099822971549786669803637)
            ·
              refine ⟨4509358403582792500294091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48099822971549786669803637 4509358403582792500294091)
              ·
                refine ⟨6764037605374188750441137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509358403582792500294091 6764037605374188750441137)
                ·
                  refine ⟨5073028204030641562830853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764037605374188750441137 5073028204030641562830853)
                  ·
                    refine ⟨951192788255745293030785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073028204030641562830853 951192788255745293030785)
                    ·
                      refine ⟨713394591191808969773089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951192788255745293030785 713394591191808969773089)
                      ·
                        rfl

theorem cell23_1389331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4, 2].length) (baseStart_1389331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389331 prefixEnd_1389331 := by exact prefixLift 1389331
  have htrace : WordTrace (prefixWord ++ tailWord_1389331) baseStart_1389331 baseEnd_1389331 := by
    simpa [prefixWord, tailWord_1389331, baseEnd_1389331] using wordTrace_append hprefix tailTrace_1389331
  have hstable : (prefixWord ++ tailWord_1389331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389331).length < 2 ^ (prefixWord ++ tailWord_1389331).sum := by decide
  have hdescent : baseEnd_1389331 < baseStart_1389331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389388 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 6]
def baseStart_1389388 : Nat := 118140960795 + 1389388 * 2 ^ 59
def prefixEnd_1389388 : Nat := 4983230072969 + 3 ^ 40 * 1389388 * 2
def baseEnd_1389388 : Nat := 79269317732123916306703

theorem tailTrace_1389388 : CollatzResearch.WordTrace tailWord_1389388 prefixEnd_1389388 79269317732123916306703 := by
  unfold tailWord_1389388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337571745246019712000409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33783428993661359616000545 25337571745246019712000409)
  ·
    refine ⟨19003178808934514784000307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25337571745246019712000409 19003178808934514784000307)
    ·
      refine ⟨28504768213401772176000461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19003178808934514784000307 28504768213401772176000461)
      ·
        refine ⟨10689288080025664566000173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28504768213401772176000461 10689288080025664566000173)
        ·
          refine ⟨4008483030009624212250065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10689288080025664566000173 4008483030009624212250065)
          ·
            refine ⟨3006362272507218159187549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008483030009624212250065 3006362272507218159187549)
            ·
              refine ⟨1127385852190206809695331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3006362272507218159187549 1127385852190206809695331)
              ·
                refine ⟨1691078778285310214542997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127385852190206809695331 1691078778285310214542997)
                ·
                  refine ⟨79269317732123916306703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1691078778285310214542997 79269317732123916306703)
                  ·
                    rfl

theorem cell23_1389388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_1389388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389388 prefixEnd_1389388 := by exact prefixLift 1389388
  have htrace : WordTrace (prefixWord ++ tailWord_1389388) baseStart_1389388 baseEnd_1389388 := by
    simpa [prefixWord, tailWord_1389388, baseEnd_1389388] using wordTrace_append hprefix tailTrace_1389388
  have hstable : (prefixWord ++ tailWord_1389388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389388).length < 2 ^ (prefixWord ++ tailWord_1389388).sum := by decide
  have hdescent : baseEnd_1389388 < baseStart_1389388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389401 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_1389401 : Nat := 118140960795 + 1389401 * 2 ^ 59
def prefixEnd_1389401 : Nat := 4983230072969 + 3 ^ 40 * 1389401 * 2
def baseEnd_1389401 : Nat := 237810178279207898632589

theorem tailTrace_1389401 : CollatzResearch.WordTrace tailWord_1389401 prefixEnd_1389401 237810178279207898632589 := by
  unfold tailWord_1389401
  simp only [CollatzResearch.WordTrace]
  refine ⟨50675617639444942644224057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33783745092963295096149371 50675617639444942644224057)
  ·
    refine ⟨38006713229583706983168043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50675617639444942644224057 38006713229583706983168043)
    ·
      refine ⟨57010069844375560474752065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38006713229583706983168043 57010069844375560474752065)
      ·
        refine ⟨42757552383281670356064049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57010069844375560474752065 42757552383281670356064049)
        ·
          refine ⟨32068164287461252767048037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42757552383281670356064049 32068164287461252767048037)
          ·
            refine ⟨6012780803898984893821507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32068164287461252767048037 6012780803898984893821507)
            ·
              refine ⟨9019171205848477340732261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012780803898984893821507 9019171205848477340732261)
              ·
                refine ⟨1691094601096589501387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9019171205848477340732261 1691094601096589501387299)
                ·
                  refine ⟨2536641901644884252080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691094601096589501387299 2536641901644884252080949)
                  ·
                    refine ⟨237810178279207898632589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2536641901644884252080949 237810178279207898632589)
                    ·
                      rfl

theorem cell23_1389401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_1389401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389401 prefixEnd_1389401 := by exact prefixLift 1389401
  have htrace : WordTrace (prefixWord ++ tailWord_1389401) baseStart_1389401 baseEnd_1389401 := by
    simpa [prefixWord, tailWord_1389401, baseEnd_1389401] using wordTrace_append hprefix tailTrace_1389401
  have hstable : (prefixWord ++ tailWord_1389401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389401).length < 2 ^ (prefixWord ++ tailWord_1389401).sum := by decide
  have hdescent : baseEnd_1389401 < baseStart_1389401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389408 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2]
def baseStart_1389408 : Nat := 118140960795 + 1389408 * 2 ^ 59
def prefixEnd_1389408 : Nat := 4983230072969 + 3 ^ 40 * 1389408 * 2
def baseEnd_1389408 : Nat := 713434129202205168510235

theorem tailTrace_1389408 : CollatzResearch.WordTrace tailWord_1389408 prefixEnd_1389408 713434129202205168510235 := by
  unfold tailWord_1389408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25337936475209791419864439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33783915300279721893152585 25337936475209791419864439)
  ·
    refine ⟨38006904712814687129796659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25337936475209791419864439 38006904712814687129796659)
    ·
      refine ⟨57010357069222030694694989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38006904712814687129796659 57010357069222030694694989)
      ·
        refine ⟨21378883900958261510510621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57010357069222030694694989 21378883900958261510510621)
        ·
          refine ⟨8017081462859348066441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21378883900958261510510621 8017081462859348066441483)
          ·
            refine ⟨12025622194289022099662225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8017081462859348066441483 12025622194289022099662225)
            ·
              refine ⟨9019216645716766574746669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12025622194289022099662225 9019216645716766574746669)
              ·
                refine ⟨3382206242143787465530001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9019216645716766574746669 3382206242143787465530001)
                ·
                  refine ⟨2536654681607840599147501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382206242143787465530001 2536654681607840599147501)
                  ·
                    refine ⟨951245505602940224680313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536654681607840599147501 951245505602940224680313)
                    ·
                      refine ⟨713434129202205168510235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951245505602940224680313 713434129202205168510235)
                      ·
                        rfl

theorem cell23_1389408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_1389408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389408 prefixEnd_1389408 := by exact prefixLift 1389408
  have htrace : WordTrace (prefixWord ++ tailWord_1389408) baseStart_1389408 baseEnd_1389408 := by
    simpa [prefixWord, tailWord_1389408, baseEnd_1389408] using wordTrace_append hprefix tailTrace_1389408
  have hstable : (prefixWord ++ tailWord_1389408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389408).length < 2 ^ (prefixWord ++ tailWord_1389408).sum := by decide
  have hdescent : baseEnd_1389408 < baseStart_1389408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389421 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1389421 : Nat := 118140960795 + 1389421 * 2 ^ 59
def prefixEnd_1389421 : Nat := 4983230072969 + 3 ^ 40 * 1389421 * 2
def baseEnd_1389421 : Nat := 713440804450713617647675

theorem tailTrace_1389421 : CollatzResearch.WordTrace tailWord_1389421 prefixEnd_1389421 713440804450713617647675 := by
  unfold tailWord_1389421
  simp only [CollatzResearch.WordTrace]
  refine ⟨50676347099372486059952117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33784231399581657373301411 50676347099372486059952117)
  ·
    refine ⟨4750907540566170568120511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50676347099372486059952117 4750907540566170568120511)
    ·
      refine ⟨7126361310849255852180767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750907540566170568120511 7126361310849255852180767)
      ·
        refine ⟨10689541966273883778271151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7126361310849255852180767 10689541966273883778271151)
        ·
          refine ⟨16034312949410825667406727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689541966273883778271151 16034312949410825667406727)
          ·
            refine ⟨24051469424116238501110091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16034312949410825667406727 24051469424116238501110091)
            ·
              refine ⟨36077204136174357751665137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24051469424116238501110091 36077204136174357751665137)
              ·
                refine ⟨27057903102130768313748853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36077204136174357751665137 27057903102130768313748853)
                ·
                  refine ⟨2536678415824759529413955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27057903102130768313748853 2536678415824759529413955)
                  ·
                    refine ⟨3805017623737139294120933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536678415824759529413955 3805017623737139294120933)
                    ·
                      refine ⟨713440804450713617647675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3805017623737139294120933 713440804450713617647675)
                      ·
                        rfl

theorem cell23_1389421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1389421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389421 prefixEnd_1389421 := by exact prefixLift 1389421
  have htrace : WordTrace (prefixWord ++ tailWord_1389421) baseStart_1389421 baseEnd_1389421 := by
    simpa [prefixWord, tailWord_1389421, baseEnd_1389421] using wordTrace_append hprefix tailTrace_1389421
  have hstable : (prefixWord ++ tailWord_1389421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389421).length < 2 ^ (prefixWord ++ tailWord_1389421).sum := by decide
  have hdescent : baseEnd_1389421 < baseStart_1389421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389489 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1389489 : Nat := 118140960795 + 1389489 * 2 ^ 59
def prefixEnd_1389489 : Nat := 4983230072969 + 3 ^ 40 * 1389489 * 2
def baseEnd_1389489 : Nat := 713475721135219351597363

theorem tailTrace_1389489 : CollatzResearch.WordTrace tailWord_1389489 prefixEnd_1389489 713475721135219351597363 := by
  unfold tailWord_1389489
  simp only [CollatzResearch.WordTrace]
  refine ⟨50678827263126133673427521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33785884842084089115618347 50678827263126133673427521)
  ·
    refine ⟨38009120447344600255070641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50678827263126133673427521 38009120447344600255070641)
    ·
      refine ⟨28506840335508450191302981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38009120447344600255070641 28506840335508450191302981)
      ·
        refine ⟨5345032562907834410869309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28506840335508450191302981 5345032562907834410869309)
        ·
          refine ⟨2004387211090437904075991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5345032562907834410869309 2004387211090437904075991)
          ·
            refine ⟨3006580816635656856113987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004387211090437904075991 3006580816635656856113987)
            ·
              refine ⟨4509871224953485284170981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006580816635656856113987 4509871224953485284170981)
              ·
                refine ⟨845600854678778490782059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4509871224953485284170981 845600854678778490782059)
                ·
                  refine ⟨1268401282018167736173089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845600854678778490782059 1268401282018167736173089)
                  ·
                    refine ⟨951300961513625802129817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268401282018167736173089 951300961513625802129817)
                    ·
                      refine ⟨713475721135219351597363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951300961513625802129817 713475721135219351597363)
                      ·
                        rfl

theorem cell23_1389489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1389489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389489 prefixEnd_1389489 := by exact prefixLift 1389489
  have htrace : WordTrace (prefixWord ++ tailWord_1389489) baseStart_1389489 baseEnd_1389489 := by
    simpa [prefixWord, tailWord_1389489, baseEnd_1389489] using wordTrace_append hprefix tailTrace_1389489
  have hstable : (prefixWord ++ tailWord_1389489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389489).length < 2 ^ (prefixWord ++ tailWord_1389489).sum := by decide
  have hdescent : baseEnd_1389489 < baseStart_1389489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389498 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_1389498 : Nat := 118140960795 + 1389498 * 2 ^ 59
def prefixEnd_1389498 : Nat := 4983230072969 + 3 ^ 40 * 1389498 * 2
def baseEnd_1389498 : Nat := 713480342461109816384821

theorem tailTrace_1389498 : CollatzResearch.WordTrace tailWord_1389498 prefixEnd_1389498 713480342461109816384821 := by
  unfold tailWord_1389498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669788880023382052626287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33786103680062352140336765 12669788880023382052626287)
  ·
    refine ⟨19004683320035073078939431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12669788880023382052626287 19004683320035073078939431)
    ·
      refine ⟨28507024980052609618409147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19004683320035073078939431 28507024980052609618409147)
      ·
        refine ⟨42760537470078914427613721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28507024980052609618409147 42760537470078914427613721)
        ·
          refine ⟨32070403102559185820710291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42760537470078914427613721 32070403102559185820710291)
          ·
            refine ⟨48105604653838778731065437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32070403102559185820710291 48105604653838778731065437)
            ·
              refine ⟨18039601745189542024149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48105604653838778731065437 18039601745189542024149539)
              ·
                refine ⟨27059402617784313036224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18039601745189542024149539 27059402617784313036224309)
                ·
                  refine ⟨2536818995417279347146029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27059402617784313036224309 2536818995417279347146029)
                  ·
                    refine ⟨951307123281479755179761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536818995417279347146029 951307123281479755179761)
                    ·
                      refine ⟨713480342461109816384821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951307123281479755179761 713480342461109816384821)
                      ·
                        rfl

theorem cell23_1389498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_1389498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389498 prefixEnd_1389498 := by exact prefixLift 1389498
  have htrace : WordTrace (prefixWord ++ tailWord_1389498) baseStart_1389498 baseEnd_1389498 := by
    simpa [prefixWord, tailWord_1389498, baseEnd_1389498] using wordTrace_append hprefix tailTrace_1389498
  have hstable : (prefixWord ++ tailWord_1389498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389498).length < 2 ^ (prefixWord ++ tailWord_1389498).sum := by decide
  have hdescent : baseEnd_1389498 < baseStart_1389498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389510 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1389510 : Nat := 118140960795 + 1389510 * 2 ^ 59
def prefixEnd_1389510 : Nat := 4983230072969 + 3 ^ 40 * 1389510 * 2
def baseEnd_1389510 : Nat := 713486504228963769434767

theorem tailTrace_1389510 : CollatzResearch.WordTrace tailWord_1389510 prefixEnd_1389510 713486504228963769434767 := by
  unfold tailWord_1389510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583737287376564195623187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33786395464033369506627989 1583737287376564195623187)
  ·
    refine ⟨2375605931064846293434781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583737287376564195623187 2375605931064846293434781)
    ·
      refine ⟨890852224149317360038043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2375605931064846293434781 890852224149317360038043)
      ·
        refine ⟨1336278336223976040057065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890852224149317360038043 1336278336223976040057065)
        ·
          refine ⟨1002208752167982030042799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336278336223976040057065 1002208752167982030042799)
          ·
            refine ⟨1503313128251973045064199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002208752167982030042799 1503313128251973045064199)
            ·
              refine ⟨2254969692377959567596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503313128251973045064199 2254969692377959567596299)
              ·
                refine ⟨3382454538566939351394449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254969692377959567596299 3382454538566939351394449)
                ·
                  refine ⟨2536840903925204513545837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382454538566939351394449 2536840903925204513545837)
                  ·
                    refine ⟨951315338971951692579689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2536840903925204513545837 951315338971951692579689)
                    ·
                      refine ⟨713486504228963769434767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951315338971951692579689 713486504228963769434767)
                      ·
                        rfl

theorem cell23_1389510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1389510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389510 prefixEnd_1389510 := by exact prefixLift 1389510
  have htrace : WordTrace (prefixWord ++ tailWord_1389510) baseStart_1389510 baseEnd_1389510 := by
    simpa [prefixWord, tailWord_1389510, baseEnd_1389510] using wordTrace_append hprefix tailTrace_1389510
  have hstable : (prefixWord ++ tailWord_1389510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389510).length < 2 ^ (prefixWord ++ tailWord_1389510).sum := by decide
  have hdescent : baseEnd_1389510 < baseStart_1389510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389551 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 7]
def baseStart_1389551 : Nat := 118140960795 + 1389551 * 2 ^ 59
def prefixEnd_1389551 : Nat := 4983230072969 + 3 ^ 40 * 1389551 * 2
def baseEnd_1389551 : Nat := 79278617437310901002453

theorem tailTrace_1389551 : CollatzResearch.WordTrace tailWord_1389551 prefixEnd_1389551 79278617437310901002453 := by
  unfold tailWord_1389551
  simp only [CollatzResearch.WordTrace]
  refine ⟨50681088588901518262184507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33787392392601012174789671 50681088588901518262184507)
  ·
    refine ⟨76021632883352277393276761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50681088588901518262184507 76021632883352277393276761)
    ·
      refine ⟨57016224662514208044957571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76021632883352277393276761 57016224662514208044957571)
      ·
        refine ⟨85524336993771312067436357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57016224662514208044957571 85524336993771312067436357)
        ·
          refine ⟨16035813186332121012644317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85524336993771312067436357 16035813186332121012644317)
          ·
            refine ⟨6013429944874545379741619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16035813186332121012644317 6013429944874545379741619)
            ·
              refine ⟨9020144917311818069612429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013429944874545379741619 9020144917311818069612429)
              ·
                refine ⟨3382554343991931776104661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9020144917311818069612429 3382554343991931776104661)
                ·
                  refine ⟨79278617437310901002453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3382554343991931776104661 79278617437310901002453)
                  ·
                    rfl

theorem cell23_1389551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 7].length) (baseStart_1389551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389551 prefixEnd_1389551 := by exact prefixLift 1389551
  have htrace : WordTrace (prefixWord ++ tailWord_1389551) baseStart_1389551 baseEnd_1389551 := by
    simpa [prefixWord, tailWord_1389551, baseEnd_1389551] using wordTrace_append hprefix tailTrace_1389551
  have hstable : (prefixWord ++ tailWord_1389551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389551).length < 2 ^ (prefixWord ++ tailWord_1389551).sum := by decide
  have hdescent : baseEnd_1389551 < baseStart_1389551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389602 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1389602 : Nat := 118140960795 + 1389602 * 2 ^ 59
def prefixEnd_1389602 : Nat := 4983230072969 + 3 ^ 40 * 1389602 * 2
def baseEnd_1389602 : Nat := 79281527161019712164927

theorem tailTrace_1389602 : CollatzResearch.WordTrace tailWord_1389602 prefixEnd_1389602 79281527161019712164927 := by
  unfold tailWord_1389602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670737177929188493072765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33788632474477835981527373 12670737177929188493072765)
  ·
    refine ⟨4751526441723445684902287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12670737177929188493072765 4751526441723445684902287)
    ·
      refine ⟨7127289662585168527353431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751526441723445684902287 7127289662585168527353431)
      ·
        refine ⟨10690934493877752791030147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127289662585168527353431 10690934493877752791030147)
        ·
          refine ⟨16036401740816629186545221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690934493877752791030147 16036401740816629186545221)
          ·
            refine ⟨3006825326403117972477229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16036401740816629186545221 3006825326403117972477229)
            ·
              refine ⟨1127559497401169239678961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3006825326403117972477229 1127559497401169239678961)
              ·
                refine ⟨845669623050876929759221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127559497401169239678961 845669623050876929759221)
                ·
                  refine ⟨79281527161019712164927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845669623050876929759221 79281527161019712164927)
                  ·
                    rfl

theorem cell23_1389602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1389602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389602 prefixEnd_1389602 := by exact prefixLift 1389602
  have htrace : WordTrace (prefixWord ++ tailWord_1389602) baseStart_1389602 baseEnd_1389602 := by
    simpa [prefixWord, tailWord_1389602, baseEnd_1389602] using wordTrace_append hprefix tailTrace_1389602
  have hstable : (prefixWord ++ tailWord_1389602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389602).length < 2 ^ (prefixWord ++ tailWord_1389602).sum := by decide
  have hdescent : baseEnd_1389602 < baseStart_1389602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389618 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1389618 : Nat := 118140960795 + 1389618 * 2 ^ 59
def prefixEnd_1389618 : Nat := 4983230072969 + 3 ^ 40 * 1389618 * 2
def baseEnd_1389618 : Nat := 713541960139649346884269

theorem tailTrace_1389618 : CollatzResearch.WordTrace tailWord_1389618 prefixEnd_1389618 713541960139649346884269 := by
  unfold tailWord_1389618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12670883069914697176218377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33789021519772525803249005 12670883069914697176218377)
  ·
    refine ⟨9503162302436022882163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12670883069914697176218377 9503162302436022882163783)
    ·
      refine ⟨14254743453654034323245675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503162302436022882163783 14254743453654034323245675)
      ·
        refine ⟨21382115180481051484868513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14254743453654034323245675 21382115180481051484868513)
        ·
          refine ⟨16036586385360788613651385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21382115180481051484868513 16036586385360788613651385)
          ·
            refine ⟨12027439789020591460238539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16036586385360788613651385 12027439789020591460238539)
            ·
              refine ⟨18041159683530887190357809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12027439789020591460238539 18041159683530887190357809)
              ·
                refine ⟨13530869762648165392768357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18041159683530887190357809 13530869762648165392768357)
                ·
                  refine ⟨2537038080496531011144067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13530869762648165392768357 2537038080496531011144067)
                  ·
                    refine ⟨3805557120744796516716101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2537038080496531011144067 3805557120744796516716101)
                    ·
                      refine ⟨713541960139649346884269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3805557120744796516716101 713541960139649346884269)
                      ·
                        rfl

theorem cell23_1389618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1389618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389618 prefixEnd_1389618 := by exact prefixLift 1389618
  have htrace : WordTrace (prefixWord ++ tailWord_1389618) baseStart_1389618 baseEnd_1389618 := by
    simpa [prefixWord, tailWord_1389618, baseEnd_1389618] using wordTrace_append hprefix tailTrace_1389618
  have hstable : (prefixWord ++ tailWord_1389618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389618).length < 2 ^ (prefixWord ++ tailWord_1389618).sum := by decide
  have hdescent : baseEnd_1389618 < baseStart_1389618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389631 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1389631 : Nat := 118140960795 + 1389631 * 2 ^ 59
def prefixEnd_1389631 : Nat := 4983230072969 + 3 ^ 40 * 1389631 * 2
def baseEnd_1389631 : Nat := 713548635388157796021709

theorem tailTrace_1389631 : CollatzResearch.WordTrace tailWord_1389631 prefixEnd_1389631 713548635388157796021709 := by
  unfold tailWord_1389631
  simp only [CollatzResearch.WordTrace]
  refine ⟨50684006428611691925096747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33789337619074461283397831 50684006428611691925096747)
  ·
    refine ⟨76026009642917537887645121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50684006428611691925096747 76026009642917537887645121)
    ·
      refine ⟨57019507232188153415733841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76026009642917537887645121 57019507232188153415733841)
      ·
        refine ⟨42764630424141115061800381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57019507232188153415733841 42764630424141115061800381)
        ·
          refine ⟨16036736409052918148175143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42764630424141115061800381 16036736409052918148175143)
          ·
            refine ⟨24055104613579377222262715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036736409052918148175143 24055104613579377222262715)
            ·
              refine ⟨36082656920369065833394073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24055104613579377222262715 36082656920369065833394073)
              ·
                refine ⟨27061992690276799375045555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36082656920369065833394073 27061992690276799375045555)
                ·
                  refine ⟨40592989035415199062568333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27061992690276799375045555 40592989035415199062568333)
                  ·
                    refine ⟨15222370888280699648463125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40592989035415199062568333 15222370888280699648463125)
                    ·
                      refine ⟨713548635388157796021709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15222370888280699648463125 713548635388157796021709)
                      ·
                        rfl

theorem cell23_1389631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1389631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389631 prefixEnd_1389631 := by exact prefixLift 1389631
  have htrace : WordTrace (prefixWord ++ tailWord_1389631) baseStart_1389631 baseEnd_1389631 := by
    simpa [prefixWord, tailWord_1389631, baseEnd_1389631] using wordTrace_append hprefix tailTrace_1389631
  have hstable : (prefixWord ++ tailWord_1389631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389631).length < 2 ^ (prefixWord ++ tailWord_1389631).sum := by decide
  have hdescent : baseEnd_1389631 < baseStart_1389631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389641 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 8]
def baseStart_1389641 : Nat := 118140960795 + 1389641 * 2 ^ 59
def prefixEnd_1389641 : Nat := 4983230072969 + 3 ^ 40 * 1389641 * 2
def baseEnd_1389641 : Nat := 79283752243855861877407

theorem tailTrace_1389641 : CollatzResearch.WordTrace tailWord_1389641 prefixEnd_1389641 79283752243855861877407 := by
  unfold tailWord_1389641
  simp only [CollatzResearch.WordTrace]
  refine ⟨50684371158575463632960777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33789580772383642421973851 50684371158575463632960777)
  ·
    refine ⟨38013278368931597724720583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50684371158575463632960777 38013278368931597724720583)
    ·
      refine ⟨57019917553397396587080875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38013278368931597724720583 57019917553397396587080875)
      ·
        refine ⟨85529876330096094880621313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57019917553397396587080875 85529876330096094880621313)
        ·
          refine ⟨64147407247572071160465985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85529876330096094880621313 64147407247572071160465985)
          ·
            refine ⟨48110555435679053370349489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64147407247572071160465985 48110555435679053370349489)
            ·
              refine ⟨36082916576759290027762117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48110555435679053370349489 36082916576759290027762117)
              ·
                refine ⟨6765546858142366880205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36082916576759290027762117 6765546858142366880205397)
                ·
                  refine ⟨79283752243855861877407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6765546858142366880205397 79283752243855861877407)
                  ·
                    rfl

theorem cell23_1389641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_1389641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389641 prefixEnd_1389641 := by exact prefixLift 1389641
  have htrace : WordTrace (prefixWord ++ tailWord_1389641) baseStart_1389641 baseEnd_1389641 := by
    simpa [prefixWord, tailWord_1389641, baseEnd_1389641] using wordTrace_append hprefix tailTrace_1389641
  have hstable : (prefixWord ++ tailWord_1389641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389641).length < 2 ^ (prefixWord ++ tailWord_1389641).sum := by decide
  have hdescent : baseEnd_1389641 < baseStart_1389641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389668 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_1389668 : Nat := 118140960795 + 1389668 * 2 ^ 59
def prefixEnd_1389668 : Nat := 4983230072969 + 3 ^ 40 * 1389668 * 2
def baseEnd_1389668 : Nat := 713567634172374151259039

theorem tailTrace_1389668 : CollatzResearch.WordTrace tailWord_1389668 prefixEnd_1389668 713567634172374151259039 := by
  unfold tailWord_1389668
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342677964738823622096829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33790237286318431496129105 25342677964738823622096829)
  ·
    refine ⟨9503504236777058858286311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25342677964738823622096829 9503504236777058858286311)
    ·
      refine ⟨14255256355165588287429467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503504236777058858286311 14255256355165588287429467)
      ·
        refine ⟨21382884532748382431144201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255256355165588287429467 21382884532748382431144201)
        ·
          refine ⟨16037163399561286823358151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21382884532748382431144201 16037163399561286823358151)
          ·
            refine ⟨24055745099341930235037227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037163399561286823358151 24055745099341930235037227)
            ·
              refine ⟨36083617649012895352555841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24055745099341930235037227 36083617649012895352555841)
              ·
                refine ⟨27062713236759671514416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36083617649012895352555841 27062713236759671514416881)
                ·
                  refine ⟨20297034927569753635812661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27062713236759671514416881 20297034927569753635812661)
                  ·
                    refine ⟨1902847024459664403357437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20297034927569753635812661 1902847024459664403357437)
                    ·
                      refine ⟨713567634172374151259039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902847024459664403357437 713567634172374151259039)
                      ·
                        rfl

theorem cell23_1389668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_1389668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389668 prefixEnd_1389668 := by exact prefixLift 1389668
  have htrace : WordTrace (prefixWord ++ tailWord_1389668) baseStart_1389668 baseEnd_1389668 := by
    simpa [prefixWord, tailWord_1389668, baseEnd_1389668] using wordTrace_append hprefix tailTrace_1389668
  have hstable : (prefixWord ++ tailWord_1389668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389668).length < 2 ^ (prefixWord ++ tailWord_1389668).sum := by decide
  have hdescent : baseEnd_1389668 < baseStart_1389668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389688 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_1389688 : Nat := 118140960795 + 1389688 * 2 ^ 59
def prefixEnd_1389688 : Nat := 4983230072969 + 3 ^ 40 * 1389688 * 2
def baseEnd_1389688 : Nat := 237859301261821357669649

theorem tailTrace_1389688 : CollatzResearch.WordTrace tailWord_1389688 prefixEnd_1389688 237859301261821357669649 := by
  unfold tailWord_1389688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25343042694702595329960859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33790723592936793773281145 25343042694702595329960859)
  ·
    refine ⟨38014564042053892994941289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25343042694702595329960859 38014564042053892994941289)
    ·
      refine ⟨28510923031540419746205967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38014564042053892994941289 28510923031540419746205967)
      ·
        refine ⟨42766384547310629619308951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28510923031540419746205967 42766384547310629619308951)
        ·
          refine ⟨64149576820965944428963427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42766384547310629619308951 64149576820965944428963427)
          ·
            refine ⟨96224365231448916643445141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64149576820965944428963427 96224365231448916643445141)
            ·
              refine ⟨4510517120224167967661491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96224365231448916643445141 4510517120224167967661491)
              ·
                refine ⟨6765775680336251951492237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510517120224167967661491 6765775680336251951492237)
                ·
                  refine ⟨2537165880126094481809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6765775680336251951492237 2537165880126094481809589)
                  ·
                    refine ⟨237859301261821357669649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2537165880126094481809589 237859301261821357669649)
                    ·
                      rfl

theorem cell23_1389688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_1389688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389688 prefixEnd_1389688 := by exact prefixLift 1389688
  have htrace : WordTrace (prefixWord ++ tailWord_1389688) baseStart_1389688 baseEnd_1389688 := by
    simpa [prefixWord, tailWord_1389688, baseEnd_1389688] using wordTrace_append hprefix tailTrace_1389688
  have hstable : (prefixWord ++ tailWord_1389688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389688).length < 2 ^ (prefixWord ++ tailWord_1389688).sum := by decide
  have hdescent : baseEnd_1389688 < baseStart_1389688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389689 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 2, 2, 3]
def baseStart_1389689 : Nat := 118140960795 + 1389689 * 2 ^ 59
def prefixEnd_1389689 : Nat := 4983230072969 + 3 ^ 40 * 1389689 * 2
def baseEnd_1389689 : Nat := 713578417266118569096443

theorem tailTrace_1389689 : CollatzResearch.WordTrace tailWord_1389689 prefixEnd_1389689 713578417266118569096443 := by
  unfold tailWord_1389689
  simp only [CollatzResearch.WordTrace]
  refine ⟨50686121862401567830708121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33790747908267711887138747 50686121862401567830708121)
  ·
    refine ⟨38014591396801175873031091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50686121862401567830708121 38014591396801175873031091)
    ·
      refine ⟨57021887095201763809546637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38014591396801175873031091 57021887095201763809546637)
      ·
        refine ⟨21383207660700661428579989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57021887095201763809546637 21383207660700661428579989)
        ·
          refine ⟨1002337859095343504464687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21383207660700661428579989 1002337859095343504464687)
          ·
            refine ⟨1503506788643015256697031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002337859095343504464687 1503506788643015256697031)
            ·
              refine ⟨2255260182964522885045547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503506788643015256697031 2255260182964522885045547)
              ·
                refine ⟨3382890274446784327568321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255260182964522885045547 3382890274446784327568321)
                ·
                  refine ⟨2537167705835088245676241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382890274446784327568321 2537167705835088245676241)
                  ·
                    refine ⟨1902875779376316184257181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537167705835088245676241 1902875779376316184257181)
                    ·
                      refine ⟨713578417266118569096443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902875779376316184257181 713578417266118569096443)
                      ·
                        rfl

theorem cell23_1389689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_1389689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389689 prefixEnd_1389689 := by exact prefixLift 1389689
  have htrace : WordTrace (prefixWord ++ tailWord_1389689) baseStart_1389689 baseEnd_1389689 := by
    simpa [prefixWord, tailWord_1389689, baseEnd_1389689] using wordTrace_append hprefix tailTrace_1389689
  have hstable : (prefixWord ++ tailWord_1389689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389689).length < 2 ^ (prefixWord ++ tailWord_1389689).sum := by decide
  have hdescent : baseEnd_1389689 < baseStart_1389689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389705 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_1389705 : Nat := 118140960795 + 1389705 * 2 ^ 59
def prefixEnd_1389705 : Nat := 4983230072969 + 3 ^ 40 * 1389705 * 2
def baseEnd_1389705 : Nat := 237862210985530168832123

theorem tailTrace_1389705 : CollatzResearch.WordTrace tailWord_1389705 prefixEnd_1389705 237862210985530168832123 := by
  unfold tailWord_1389705
  simp only [CollatzResearch.WordTrace]
  refine ⟨50686705430343602563290569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33791136953562401708860379 50686705430343602563290569)
  ·
    refine ⟨38015029072757701922467927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50686705430343602563290569 38015029072757701922467927)
    ·
      refine ⟨57022543609136552883701891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38015029072757701922467927 57022543609136552883701891)
      ·
        refine ⟨85533815413704829325552837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57022543609136552883701891 85533815413704829325552837)
        ·
          refine ⟨16037590390069655498541157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85533815413704829325552837 16037590390069655498541157)
          ·
            refine ⟨3007048198138060405976467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16037590390069655498541157 3007048198138060405976467)
            ·
              refine ⟨4510572297207090608964701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007048198138060405976467 4510572297207090608964701)
              ·
                refine ⟨1691464611452658978361763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4510572297207090608964701 1691464611452658978361763)
                ·
                  refine ⟨2537196917178988467542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691464611452658978361763 2537196917178988467542645)
                  ·
                    refine ⟨237862210985530168832123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2537196917178988467542645 237862210985530168832123)
                    ·
                      rfl

theorem cell23_1389705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_1389705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389705 prefixEnd_1389705 := by exact prefixLift 1389705
  have htrace : WordTrace (prefixWord ++ tailWord_1389705) baseStart_1389705 baseEnd_1389705 := by
    simpa [prefixWord, tailWord_1389705, baseEnd_1389705] using wordTrace_append hprefix tailTrace_1389705
  have hstable : (prefixWord ++ tailWord_1389705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389705).length < 2 ^ (prefixWord ++ tailWord_1389705).sum := by decide
  have hdescent : baseEnd_1389705 < baseStart_1389705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389719 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_1389719 : Nat := 118140960795 + 1389719 * 2 ^ 59
def prefixEnd_1389719 : Nat := 4983230072969 + 3 ^ 40 * 1389719 * 2
def baseEnd_1389719 : Nat := 713593821685753451721305

theorem tailTrace_1389719 : CollatzResearch.WordTrace tailWord_1389719 prefixEnd_1389719 713593821685753451721305 := by
  unfold tailWord_1389719
  simp only [CollatzResearch.WordTrace]
  refine ⟨50687216052292882954300211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33791477368195255302866807 50687216052292882954300211)
  ·
    refine ⟨76030824078439324431450317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50687216052292882954300211 76030824078439324431450317)
    ·
      refine ⟨28511559029414746661793869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76030824078439324431450317 28511559029414746661793869)
      ·
        refine ⟨10691834636030529998172701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28511559029414746661793869 10691834636030529998172701)
        ·
          refine ⟨4009437988511448749314763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10691834636030529998172701 4009437988511448749314763)
          ·
            refine ⟨6014156982767173123972145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009437988511448749314763 6014156982767173123972145)
            ·
              refine ⟨4510617737075379842979109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014156982767173123972145 4510617737075379842979109)
              ·
                refine ⟨845740825701633720558583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4510617737075379842979109 845740825701633720558583)
                ·
                  refine ⟨1268611238552450580837875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845740825701633720558583 1268611238552450580837875)
                  ·
                    refine ⟨1902916857828675871256813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1268611238552450580837875 1902916857828675871256813)
                    ·
                      refine ⟨713593821685753451721305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1902916857828675871256813 713593821685753451721305)
                      ·
                        rfl

theorem cell23_1389719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_1389719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389719 prefixEnd_1389719 := by exact prefixLift 1389719
  have htrace : WordTrace (prefixWord ++ tailWord_1389719) baseStart_1389719 baseEnd_1389719 := by
    simpa [prefixWord, tailWord_1389719, baseEnd_1389719] using wordTrace_append hprefix tailTrace_1389719
  have hstable : (prefixWord ++ tailWord_1389719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389719).length < 2 ^ (prefixWord ++ tailWord_1389719).sum := by decide
  have hdescent : baseEnd_1389719 < baseStart_1389719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389785 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 7, 2]
def baseStart_1389785 : Nat := 118140960795 + 1389785 * 2 ^ 59
def prefixEnd_1389785 : Nat := 4983230072969 + 3 ^ 40 * 1389785 * 2
def baseEnd_1389785 : Nat := 713627711408950193496001

theorem tailTrace_1389785 : CollatzResearch.WordTrace tailWord_1389785 prefixEnd_1389785 713627711408950193496001 := by
  unfold tailWord_1389785
  simp only [CollatzResearch.WordTrace]
  refine ⟨50689623270053776226202809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33793082180035850817468539 50689623270053776226202809)
  ·
    refine ⟨38017217452540332169652107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50689623270053776226202809 38017217452540332169652107)
    ·
      refine ⟨57025826178810498254478161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38017217452540332169652107 57025826178810498254478161)
      ·
        refine ⟨42769369634107873690858621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57025826178810498254478161 42769369634107873690858621)
        ·
          refine ⟨16038513612790452634071983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42769369634107873690858621 16038513612790452634071983)
          ·
            refine ⟨24057770419185678951107975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16038513612790452634071983 24057770419185678951107975)
            ·
              refine ⟨36086655628778518426661963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24057770419185678951107975 36086655628778518426661963)
              ·
                refine ⟨54129983443167777639992945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36086655628778518426661963 54129983443167777639992945)
                ·
                  refine ⟨40597487582375833229994709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54129983443167777639992945 40597487582375833229994709)
                  ·
                    refine ⟨951503615211933591328001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40597487582375833229994709 951503615211933591328001)
                    ·
                      refine ⟨713627711408950193496001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951503615211933591328001 713627711408950193496001)
                      ·
                        rfl

theorem cell23_1389785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_1389785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389785 prefixEnd_1389785 := by exact prefixLift 1389785
  have htrace : WordTrace (prefixWord ++ tailWord_1389785) baseStart_1389785 baseEnd_1389785 := by
    simpa [prefixWord, tailWord_1389785, baseEnd_1389785] using wordTrace_append hprefix tailTrace_1389785
  have hstable : (prefixWord ++ tailWord_1389785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389785).length < 2 ^ (prefixWord ++ tailWord_1389785).sum := by decide
  have hdescent : baseEnd_1389785 < baseStart_1389785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389808 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_1389808 : Nat := 118140960795 + 1389808 * 2 ^ 59
def prefixEnd_1389808 : Nat := 4983230072969 + 3 ^ 40 * 1389808 * 2
def baseEnd_1389808 : Nat := 237879840488001201169465

theorem tailTrace_1389808 : CollatzResearch.WordTrace tailWord_1389808 prefixEnd_1389808 237879840488001201169465 := by
  unfold tailWord_1389808
  simp only [CollatzResearch.WordTrace]
  refine ⟨25345231074485225577145039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33793641432646967436193385 25345231074485225577145039)
  ·
    refine ⟨38017846611727838365717559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25345231074485225577145039 38017846611727838365717559)
    ·
      refine ⟨57026769917591757548576339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38017846611727838365717559 57026769917591757548576339)
      ·
        refine ⟨85540154876387636322864509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57026769917591757548576339 85540154876387636322864509)
        ·
          refine ⟨32077558078645363621074191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85540154876387636322864509 32077558078645363621074191)
          ·
            refine ⟨48116337117968045431611287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32077558078645363621074191 48116337117968045431611287)
            ·
              refine ⟨72174505676952068147416931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48116337117968045431611287 72174505676952068147416931)
              ·
                refine ⟨108261758515428102221125397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72174505676952068147416931 108261758515428102221125397)
                ·
                  refine ⟨5074769930410692291615253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108261758515428102221125397 5074769930410692291615253)
                  ·
                    refine ⟨237879840488001201169465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5074769930410692291615253 237879840488001201169465)
                    ·
                      rfl

theorem cell23_1389808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_1389808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389808 prefixEnd_1389808 := by exact prefixLift 1389808
  have htrace : WordTrace (prefixWord ++ tailWord_1389808) baseStart_1389808 baseEnd_1389808 := by
    simpa [prefixWord, tailWord_1389808, baseEnd_1389808] using wordTrace_append hprefix tailTrace_1389808
  have hstable : (prefixWord ++ tailWord_1389808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389808).length < 2 ^ (prefixWord ++ tailWord_1389808).sum := by decide
  have hdescent : baseEnd_1389808 < baseStart_1389808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389835 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3]
def baseStart_1389835 : Nat := 118140960795 + 1389835 * 2 ^ 59
def prefixEnd_1389835 : Nat := 4983230072969 + 3 ^ 40 * 1389835 * 2
def baseEnd_1389835 : Nat := 713653385441674997870771

theorem tailTrace_1389835 : CollatzResearch.WordTrace tailWord_1389835 prefixEnd_1389835 713653385441674997870771 := by
  unfold tailWord_1389835
  simp only [CollatzResearch.WordTrace]
  refine ⟨50691446919872634765522959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33794297946581756510348639 50691446919872634765522959)
  ·
    refine ⟨76037170379808952148284439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50691446919872634765522959 76037170379808952148284439)
    ·
      refine ⟨114055755569713428222426659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76037170379808952148284439 114055755569713428222426659)
      ·
        refine ⟨171083633354570142333639989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114055755569713428222426659 171083633354570142333639989)
        ·
          refine ⟨16039090626990950843778749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171083633354570142333639989 16039090626990950843778749)
          ·
            refine ⟨6014658985121606566417031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16039090626990950843778749 6014658985121606566417031)
            ·
              refine ⟨9021988477682409849625547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014658985121606566417031 9021988477682409849625547)
              ·
                refine ⟨13532982716523614774438321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9021988477682409849625547 13532982716523614774438321)
                ·
                  refine ⟨10149737037392711080828741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13532982716523614774438321 10149737037392711080828741)
                  ·
                    refine ⟨1903075694511133327655389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10149737037392711080828741 1903075694511133327655389)
                    ·
                      refine ⟨713653385441674997870771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903075694511133327655389 713653385441674997870771)
                      ·
                        rfl

theorem cell23_1389835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 3].length) (baseStart_1389835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389835 prefixEnd_1389835 := by exact prefixLift 1389835
  have htrace : WordTrace (prefixWord ++ tailWord_1389835) baseStart_1389835 baseEnd_1389835 := by
    simpa [prefixWord, tailWord_1389835, baseEnd_1389835] using wordTrace_append hprefix tailTrace_1389835
  have hstable : (prefixWord ++ tailWord_1389835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389835).length < 2 ^ (prefixWord ++ tailWord_1389835).sum := by decide
  have hdescent : baseEnd_1389835 < baseStart_1389835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389872 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 5]
def baseStart_1389872 : Nat := 118140960795 + 1389872 * 2 ^ 59
def prefixEnd_1389872 : Nat := 4983230072969 + 3 ^ 40 * 1389872 * 2
def baseEnd_1389872 : Nat := 79296931580654594789789

theorem tailTrace_1389872 : CollatzResearch.WordTrace tailWord_1389872 prefixEnd_1389872 79296931580654594789789 := by
  unfold tailWord_1389872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25346398210369295042309935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33795197613825726723079913 25346398210369295042309935)
  ·
    refine ⟨38019597315553942563464903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25346398210369295042309935 38019597315553942563464903)
    ·
      refine ⟨57029395973330913845197355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38019597315553942563464903 57029395973330913845197355)
      ·
        refine ⟨85544093959996370767796033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57029395973330913845197355 85544093959996370767796033)
        ·
          refine ⟨64158070469997278075847025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85544093959996370767796033 64158070469997278075847025)
          ·
            refine ⟨48118552852497958556885269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64158070469997278075847025 48118552852497958556885269)
            ·
              refine ⟨2255557164960841807353997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48118552852497958556885269 2255557164960841807353997)
              ·
                refine ⟨845833936860315677757749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255557164960841807353997 845833936860315677757749)
                ·
                  refine ⟨79296931580654594789789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845833936860315677757749 79296931580654594789789)
                  ·
                    rfl

theorem cell23_1389872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 5].length) (baseStart_1389872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389872 prefixEnd_1389872 := by exact prefixLift 1389872
  have htrace : WordTrace (prefixWord ++ tailWord_1389872) baseStart_1389872 baseEnd_1389872 := by
    simpa [prefixWord, tailWord_1389872, baseEnd_1389872] using wordTrace_append hprefix tailTrace_1389872
  have hstable : (prefixWord ++ tailWord_1389872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389872).length < 2 ^ (prefixWord ++ tailWord_1389872).sum := by decide
  have hdescent : baseEnd_1389872 < baseStart_1389872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389889 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 5]
def baseStart_1389889 : Nat := 118140960795 + 1389889 * 2 ^ 59
def prefixEnd_1389889 : Nat := 4983230072969 + 3 ^ 40 * 1389889 * 2
def baseEnd_1389889 : Nat := 79297901488557531843947

theorem tailTrace_1389889 : CollatzResearch.WordTrace tailWord_1389889 prefixEnd_1389889 79297901488557531843947 := by
  unfold tailWord_1389889
  simp only [CollatzResearch.WordTrace]
  refine ⟨50693416461677001987988721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33795610974451334658659147 50693416461677001987988721)
  ·
    refine ⟨38020062346257751490991541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50693416461677001987988721 38020062346257751490991541)
    ·
      refine ⟨3564380844961664202280457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38020062346257751490991541 3564380844961664202280457)
      ·
        refine ⟨2673285633721248151710343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564380844961664202280457 2673285633721248151710343)
        ·
          refine ⟨4009928450581872227565515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673285633721248151710343 4009928450581872227565515)
          ·
            refine ⟨6014892675872808341348273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009928450581872227565515 6014892675872808341348273)
            ·
              refine ⟨4511169506904606256011205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6014892675872808341348273 4511169506904606256011205)
              ·
                refine ⟨845844282544613673002101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4511169506904606256011205 845844282544613673002101)
                ·
                  refine ⟨79297901488557531843947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845844282544613673002101 79297901488557531843947)
                  ·
                    rfl

theorem cell23_1389889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 5].length) (baseStart_1389889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389889 prefixEnd_1389889 := by exact prefixLift 1389889
  have htrace : WordTrace (prefixWord ++ tailWord_1389889) baseStart_1389889 baseEnd_1389889 := by
    simpa [prefixWord, tailWord_1389889, baseEnd_1389889] using wordTrace_append hprefix tailTrace_1389889
  have hstable : (prefixWord ++ tailWord_1389889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389889).length < 2 ^ (prefixWord ++ tailWord_1389889).sum := by decide
  have hdescent : baseEnd_1389889 < baseStart_1389889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389905 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1389905 : Nat := 118140960795 + 1389905 * 2 ^ 59
def prefixEnd_1389905 : Nat := 4983230072969 + 3 ^ 40 * 1389905 * 2
def baseEnd_1389905 : Nat := 713689329087489723995449

theorem tailTrace_1389905 : CollatzResearch.WordTrace tailWord_1389905 prefixEnd_1389905 713689329087489723995449 := by
  unfold tailWord_1389905
  simp only [CollatzResearch.WordTrace]
  refine ⟨50694000029619036720571169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33796000019746024480380779 50694000029619036720571169)
  ·
    refine ⟨38020500022214277540428377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50694000029619036720571169 38020500022214277540428377)
    ·
      refine ⟨28515375016660708155321283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38020500022214277540428377 28515375016660708155321283)
      ·
        refine ⟨42773062524991062232981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28515375016660708155321283 42773062524991062232981925)
        ·
          refine ⟨8019949223435824168684111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42773062524991062232981925 8019949223435824168684111)
          ·
            refine ⟨12029923835153736253026167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019949223435824168684111 12029923835153736253026167)
            ·
              refine ⟨18044885752730604379539251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029923835153736253026167 18044885752730604379539251)
              ·
                refine ⟨27067328629095906569308877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18044885752730604379539251 27067328629095906569308877)
                ·
                  refine ⟨10150248235910964963490829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27067328629095906569308877 10150248235910964963490829)
                  ·
                    refine ⟨3806343088466611861309061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10150248235910964963490829 3806343088466611861309061)
                    ·
                      refine ⟨713689329087489723995449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3806343088466611861309061 713689329087489723995449)
                      ·
                        rfl

theorem cell23_1389905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1389905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389905 prefixEnd_1389905 := by exact prefixLift 1389905
  have htrace : WordTrace (prefixWord ++ tailWord_1389905) baseStart_1389905 baseEnd_1389905 := by
    simpa [prefixWord, tailWord_1389905, baseEnd_1389905] using wordTrace_append hprefix tailTrace_1389905
  have hstable : (prefixWord ++ tailWord_1389905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389905).length < 2 ^ (prefixWord ++ tailWord_1389905).sum := by decide
  have hdescent : baseEnd_1389905 < baseStart_1389905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389922 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1389922 : Nat := 118140960795 + 1389922 * 2 ^ 59
def prefixEnd_1389922 : Nat := 4983230072969 + 3 ^ 40 * 1389922 * 2
def baseEnd_1389922 : Nat := 713698058258616157482871

theorem tailTrace_1389922 : CollatzResearch.WordTrace tailWord_1389922 prefixEnd_1389922 713698058258616157482871 := by
  unfold tailWord_1389922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673655017639362155985005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33796413380371632415960013 12673655017639362155985005)
  ·
    refine ⟨4752620631614760808494377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12673655017639362155985005 4752620631614760808494377)
    ·
      refine ⟨3564465473711070606370783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4752620631614760808494377 3564465473711070606370783)
      ·
        refine ⟨5346698210566605909556175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564465473711070606370783 5346698210566605909556175)
        ·
          refine ⟨8020047315849908864334263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346698210566605909556175 8020047315849908864334263)
          ·
            refine ⟨12030070973774863296501395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020047315849908864334263 12030070973774863296501395)
            ·
              refine ⟨18045106460662294944752093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12030070973774863296501395 18045106460662294944752093)
              ·
                refine ⟨6766914922748360604282035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18045106460662294944752093 6766914922748360604282035)
                ·
                  refine ⟨10150372384122540906423053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766914922748360604282035 10150372384122540906423053)
                  ·
                    refine ⟨3806389644045952839908645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10150372384122540906423053 3806389644045952839908645)
                    ·
                      refine ⟨713698058258616157482871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3806389644045952839908645 713698058258616157482871)
                      ·
                        rfl

theorem cell23_1389922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1389922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389922 prefixEnd_1389922 := by exact prefixLift 1389922
  have htrace : WordTrace (prefixWord ++ tailWord_1389922) baseStart_1389922 baseEnd_1389922 := by
    simpa [prefixWord, tailWord_1389922, baseEnd_1389922] using wordTrace_append hprefix tailTrace_1389922
  have hstable : (prefixWord ++ tailWord_1389922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389922).length < 2 ^ (prefixWord ++ tailWord_1389922).sum := by decide
  have hdescent : baseEnd_1389922 < baseStart_1389922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389945 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 8]
def baseStart_1389945 : Nat := 118140960795 + 1389945 * 2 ^ 59
def prefixEnd_1389945 : Nat := 4983230072969 + 3 ^ 40 * 1389945 * 2
def baseEnd_1389945 : Nat := 79301096479296618610585

theorem tailTrace_1389945 : CollatzResearch.WordTrace tailWord_1389945 prefixEnd_1389945 79301096479296618610585 := by
  unfold tailWord_1389945
  simp only [CollatzResearch.WordTrace]
  refine ⟨50695458949474123552027289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33796972632982749034684859 50695458949474123552027289)
  ·
    refine ⟨38021594212105592664020467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50695458949474123552027289 38021594212105592664020467)
    ·
      refine ⟨57032391318158388996030701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38021594212105592664020467 57032391318158388996030701)
      ·
        refine ⟨21387146744309395873511513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57032391318158388996030701 21387146744309395873511513)
        ·
          refine ⟨16040360058232046905133635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21387146744309395873511513 16040360058232046905133635)
          ·
            refine ⟨24060540087348070357700453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16040360058232046905133635 24060540087348070357700453)
            ·
              refine ⟨4511351266377763192068835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24060540087348070357700453 4511351266377763192068835)
              ·
                refine ⟨6767026899566644788103253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511351266377763192068835 6767026899566644788103253)
                ·
                  refine ⟨79301096479296618610585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6767026899566644788103253 79301096479296618610585)
                  ·
                    rfl

theorem cell23_1389945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_1389945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389945 prefixEnd_1389945 := by exact prefixLift 1389945
  have htrace : WordTrace (prefixWord ++ tailWord_1389945) baseStart_1389945 baseEnd_1389945 := by
    simpa [prefixWord, tailWord_1389945, baseEnd_1389945] using wordTrace_append hprefix tailTrace_1389945
  have hstable : (prefixWord ++ tailWord_1389945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389945).length < 2 ^ (prefixWord ++ tailWord_1389945).sum := by decide
  have hdescent : baseEnd_1389945 < baseStart_1389945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389976 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1389976 : Nat := 118140960795 + 1389976 * 2 ^ 59
def prefixEnd_1389976 : Nat := 4983230072969 + 3 ^ 40 * 1389976 * 2
def baseEnd_1389976 : Nat := 713725786213958946207623

theorem tailTrace_1389976 : CollatzResearch.WordTrace tailWord_1389976 prefixEnd_1389976 713725786213958946207623 := by
  unfold tailWord_1389976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348294806180907923202891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33797726408241210564270521 25348294806180907923202891)
  ·
    refine ⟨38022442209271361884804337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25348294806180907923202891 38022442209271361884804337)
    ·
      refine ⟨28516831656953521413603253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38022442209271361884804337 28516831656953521413603253)
      ·
        refine ⟨2673452967839392632525305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28516831656953521413603253 2673452967839392632525305)
        ·
          refine ⟨2005089725879544474393979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673452967839392632525305 2005089725879544474393979)
          ·
            refine ⟨3007634588819316711590969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005089725879544474393979 3007634588819316711590969)
            ·
              refine ⟨2255725941614487533693227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007634588819316711590969 2255725941614487533693227)
              ·
                refine ⟨3383588912421731300539841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255725941614487533693227 3383588912421731300539841)
                ·
                  refine ⟨2537691684316298475404881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383588912421731300539841 2537691684316298475404881)
                  ·
                    refine ⟨1903268763237223856553661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537691684316298475404881 1903268763237223856553661)
                    ·
                      refine ⟨713725786213958946207623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903268763237223856553661 713725786213958946207623)
                      ·
                        rfl

theorem cell23_1389976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1389976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389976 prefixEnd_1389976 := by exact prefixLift 1389976
  have htrace : WordTrace (prefixWord ++ tailWord_1389976) baseStart_1389976 baseEnd_1389976 := by
    simpa [prefixWord, tailWord_1389976, baseEnd_1389976] using wordTrace_append hprefix tailTrace_1389976
  have hstable : (prefixWord ++ tailWord_1389976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389976).length < 2 ^ (prefixWord ++ tailWord_1389976).sum := by decide
  have hdescent : baseEnd_1389976 < baseStart_1389976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1389995 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_1389995 : Nat := 118140960795 + 1389995 * 2 ^ 59
def prefixEnd_1389995 : Nat := 4983230072969 + 3 ^ 40 * 1389995 * 2
def baseEnd_1389995 : Nat := 713735542346394371870035

theorem tailTrace_1389995 : CollatzResearch.WordTrace tailWord_1389995 prefixEnd_1389995 713735542346394371870035 := by
  unfold tailWord_1389995
  simp only [CollatzResearch.WordTrace]
  refine ⟨50697282599292982091347439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33798188399528654727564959 50697282599292982091347439)
  ·
    refine ⟨76045923898939473137021159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50697282599292982091347439 76045923898939473137021159)
    ·
      refine ⟨114068885848409209705531739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76045923898939473137021159 114068885848409209705531739)
      ·
        refine ⟨171103328772613814558297609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114068885848409209705531739 171103328772613814558297609)
        ·
          refine ⟨128327496579460360918723207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171103328772613814558297609 128327496579460360918723207)
          ·
            refine ⟨192491244869190541378084811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128327496579460360918723207 192491244869190541378084811)
            ·
              refine ⟨288736867303785812067127217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192491244869190541378084811 288736867303785812067127217)
              ·
                refine ⟨216552650477839359050345413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288736867303785812067127217 216552650477839359050345413)
                ·
                  refine ⟨40603621964594879821939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216552650477839359050345413 40603621964594879821939765)
                  ·
                    refine ⟨3806589559180769983306853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40603621964594879821939765 3806589559180769983306853)
                    ·
                      refine ⟨713735542346394371870035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3806589559180769983306853 713735542346394371870035)
                      ·
                        rfl

theorem cell23_1389995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_1389995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1389995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1389995 prefixEnd_1389995 := by exact prefixLift 1389995
  have htrace : WordTrace (prefixWord ++ tailWord_1389995) baseStart_1389995 baseEnd_1389995 := by
    simpa [prefixWord, tailWord_1389995, baseEnd_1389995] using wordTrace_append hprefix tailTrace_1389995
  have hstable : (prefixWord ++ tailWord_1389995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1389995).length < 2 ^ (prefixWord ++ tailWord_1389995).sum := by decide
  have hdescent : baseEnd_1389995 < baseStart_1389995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1389995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390063 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 1, 2, 2]
def baseStart_1390063 : Nat := 118140960795 + 1390063 * 2 ^ 59
def prefixEnd_1390063 : Nat := 4983230072969 + 3 ^ 40 * 1390063 * 2
def baseEnd_1390063 : Nat := 713770459030900105819723

theorem tailTrace_1390063 : CollatzResearch.WordTrace tailWord_1390063 prefixEnd_1390063 713770459030900105819723 := by
  unfold tailWord_1390063
  simp only [CollatzResearch.WordTrace]
  refine ⟨50699762763046629704822843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33799841842031086469881895 50699762763046629704822843)
  ·
    refine ⟨76049644144569944557234265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50699762763046629704822843 76049644144569944557234265)
    ·
      refine ⟨57037233108427458417925699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76049644144569944557234265 57037233108427458417925699)
      ·
        refine ⟨85555849662641187626888549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57037233108427458417925699 85555849662641187626888549)
        ·
          refine ⟨16041721811745222680041603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85555849662641187626888549 16041721811745222680041603)
          ·
            refine ⟨24062582717617834020062405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16041721811745222680041603 24062582717617834020062405)
            ·
              refine ⟨4511734259553343878761701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24062582717617834020062405 4511734259553343878761701)
              ·
                refine ⟨845950173666251977267819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4511734259553343878761701 845950173666251977267819)
                ·
                  refine ⟨1268925260499377965901729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845950173666251977267819 1268925260499377965901729)
                  ·
                    refine ⟨951693945374533474426297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268925260499377965901729 951693945374533474426297)
                    ·
                      refine ⟨713770459030900105819723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951693945374533474426297 713770459030900105819723)
                      ·
                        rfl

theorem cell23_1390063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 2, 2].length) (baseStart_1390063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390063 prefixEnd_1390063 := by exact prefixLift 1390063
  have htrace : WordTrace (prefixWord ++ tailWord_1390063) baseStart_1390063 baseEnd_1390063 := by
    simpa [prefixWord, tailWord_1390063, baseEnd_1390063] using wordTrace_append hprefix tailTrace_1390063
  have hstable : (prefixWord ++ tailWord_1390063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390063).length < 2 ^ (prefixWord ++ tailWord_1390063).sum := by decide
  have hdescent : baseEnd_1390063 < baseStart_1390063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390140 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_1390140 : Nat := 118140960795 + 1390140 * 2 ^ 59
def prefixEnd_1390140 : Nat := 4983230072969 + 3 ^ 40 * 1390140 * 2
def baseEnd_1390140 : Nat := 713809997041296304556869

theorem tailTrace_1390140 : CollatzResearch.WordTrace tailWord_1390140 prefixEnd_1390140 713809997041296304556869 := by
  unfold tailWord_1390140
  simp only [CollatzResearch.WordTrace]
  refine ⟨25351285591883835927687937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33801714122511781236917249 25351285591883835927687937)
  ·
    refine ⟨19013464193912876945765953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25351285591883835927687937 19013464193912876945765953)
    ·
      refine ⟨14260098145434657709324465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19013464193912876945765953 14260098145434657709324465)
      ·
        refine ⟨10695073609075993281993349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14260098145434657709324465 10695073609075993281993349)
        ·
          refine ⟨2005326301701748740373753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10695073609075993281993349 2005326301701748740373753)
          ·
            refine ⟨1503994726276311555280315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005326301701748740373753 1503994726276311555280315)
            ·
              refine ⟨2255992089414467332920473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503994726276311555280315 2255992089414467332920473)
              ·
                refine ⟨1691994067060850499690355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255992089414467332920473 1691994067060850499690355)
                ·
                  refine ⟨2537991100591275749535533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691994067060850499690355 2537991100591275749535533)
                  ·
                    refine ⟨951746662721728406075825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2537991100591275749535533 951746662721728406075825)
                    ·
                      refine ⟨713809997041296304556869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951746662721728406075825 713809997041296304556869)
                      ·
                        rfl

theorem cell23_1390140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_1390140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390140 prefixEnd_1390140 := by exact prefixLift 1390140
  have htrace : WordTrace (prefixWord ++ tailWord_1390140) baseStart_1390140 baseEnd_1390140 := by
    simpa [prefixWord, tailWord_1390140, baseEnd_1390140] using wordTrace_append hprefix tailTrace_1390140
  have hstable : (prefixWord ++ tailWord_1390140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390140).length < 2 ^ (prefixWord ++ tailWord_1390140).sum := by decide
  have hdescent : baseEnd_1390140 < baseStart_1390140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390157 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1390157 : Nat := 118140960795 + 1390157 * 2 ^ 59
def prefixEnd_1390157 : Nat := 4983230072969 + 3 ^ 40 * 1390157 * 2
def baseEnd_1390157 : Nat := 713818726212422738044291

theorem tailTrace_1390157 : CollatzResearch.WordTrace tailWord_1390157 prefixEnd_1390157 713818726212422738044291 := by
  unfold tailWord_1390157
  simp only [CollatzResearch.WordTrace]
  refine ⟨50703191224706083758744725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33802127483137389172496483 50703191224706083758744725)
  ·
    refine ⟨2376712088658097676191159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50703191224706083758744725 2376712088658097676191159)
    ·
      refine ⟨3565068132987146514286739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376712088658097676191159 3565068132987146514286739)
      ·
        refine ⟨5347602199480719771430109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565068132987146514286739 5347602199480719771430109)
        ·
          refine ⟨2005350824805269914286291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5347602199480719771430109 2005350824805269914286291)
          ·
            refine ⟨3008026237207904871429437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005350824805269914286291 3008026237207904871429437)
            ·
              refine ⟨1128009838952964326786039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3008026237207904871429437 1128009838952964326786039)
              ·
                refine ⟨1692014758429446490179059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128009838952964326786039 1692014758429446490179059)
                ·
                  refine ⟨2538022137644169735268589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692014758429446490179059 2538022137644169735268589)
                  ·
                    refine ⟨951758301616563650725721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2538022137644169735268589 951758301616563650725721)
                    ·
                      refine ⟨713818726212422738044291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951758301616563650725721 713818726212422738044291)
                      ·
                        rfl

theorem cell23_1390157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1390157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390157 prefixEnd_1390157 := by exact prefixLift 1390157
  have htrace : WordTrace (prefixWord ++ tailWord_1390157) baseStart_1390157 baseEnd_1390157 := by
    simpa [prefixWord, tailWord_1390157, baseEnd_1390157] using wordTrace_append hprefix tailTrace_1390157
  have hstable : (prefixWord ++ tailWord_1390157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390157).length < 2 ^ (prefixWord ++ tailWord_1390157).sum := by decide
  have hdescent : baseEnd_1390157 < baseStart_1390157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390159 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 5]
def baseStart_1390159 : Nat := 118140960795 + 1390159 * 2 ^ 59
def prefixEnd_1390159 : Nat := 4983230072969 + 3 ^ 40 * 1390159 * 2
def baseEnd_1390159 : Nat := 79313305908192414468809

theorem tailTrace_1390159 : CollatzResearch.WordTrace tailWord_1390159 prefixEnd_1390159 79313305908192414468809 := by
  unfold tailWord_1390159
  simp only [CollatzResearch.WordTrace]
  refine ⟨50703264170698838100317531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33802176113799225400211687 50703264170698838100317531)
  ·
    refine ⟨76054896256048257150476297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50703264170698838100317531 76054896256048257150476297)
    ·
      refine ⟨57041172192036192862857223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76054896256048257150476297 57041172192036192862857223)
      ·
        refine ⟨85561758288054289294285835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57041172192036192862857223 85561758288054289294285835)
        ·
          refine ⟨128342637432081433941428753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85561758288054289294285835 128342637432081433941428753)
          ·
            refine ⟨96256978074061075456071565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128342637432081433941428753 96256978074061075456071565)
            ·
              refine ⟨36096366777772903296026837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96256978074061075456071565 36096366777772903296026837)
              ·
                refine ⟨846008596354052421000629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36096366777772903296026837 846008596354052421000629)
                ·
                  refine ⟨79313305908192414468809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846008596354052421000629 79313305908192414468809)
                  ·
                    rfl

theorem cell23_1390159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 5].length) (baseStart_1390159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390159 prefixEnd_1390159 := by exact prefixLift 1390159
  have htrace : WordTrace (prefixWord ++ tailWord_1390159) baseStart_1390159 baseEnd_1390159 := by
    simpa [prefixWord, tailWord_1390159, baseEnd_1390159] using wordTrace_append hprefix tailTrace_1390159
  have hstable : (prefixWord ++ tailWord_1390159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390159).length < 2 ^ (prefixWord ++ tailWord_1390159).sum := by decide
  have hdescent : baseEnd_1390159 < baseStart_1390159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390186 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1390186 : Nat := 118140960795 + 1390186 * 2 ^ 59
def prefixEnd_1390186 : Nat := 4983230072969 + 3 ^ 40 * 1390186 * 2
def baseEnd_1390186 : Nat := 713833617151403124581657

theorem tailTrace_1390186 : CollatzResearch.WordTrace tailWord_1390186 prefixEnd_1390186 713833617151403124581657 := by
  unfold tailWord_1390186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676062235400255427887603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33802832627734014474366941 12676062235400255427887603)
  ·
    refine ⟨19014093353100383141831405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12676062235400255427887603 19014093353100383141831405)
    ·
      refine ⟨7130285007412643678186777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19014093353100383141831405 7130285007412643678186777)
      ·
        refine ⟨5347713755559482758640083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7130285007412643678186777 5347713755559482758640083)
        ·
          refine ⟨8021570633339224137960125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347713755559482758640083 8021570633339224137960125)
          ·
            refine ⟨3008088987502209051735047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8021570633339224137960125 3008088987502209051735047)
            ·
              refine ⟨4512133481253313577602571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008088987502209051735047 4512133481253313577602571)
              ·
                refine ⟨6768200221879970366403857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4512133481253313577602571 6768200221879970366403857)
                ·
                  refine ⟨5076150166409977774802893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6768200221879970366403857 5076150166409977774802893)
                  ·
                    refine ⟨1903556312403741665551085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5076150166409977774802893 1903556312403741665551085)
                    ·
                      refine ⟨713833617151403124581657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903556312403741665551085 713833617151403124581657)
                      ·
                        rfl

theorem cell23_1390186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1390186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390186 prefixEnd_1390186 := by exact prefixLift 1390186
  have htrace : WordTrace (prefixWord ++ tailWord_1390186) baseStart_1390186 baseEnd_1390186 := by
    simpa [prefixWord, tailWord_1390186, baseEnd_1390186] using wordTrace_append hprefix tailTrace_1390186
  have hstable : (prefixWord ++ tailWord_1390186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390186).length < 2 ^ (prefixWord ++ tailWord_1390186).sum := by decide
  have hdescent : baseEnd_1390186 < baseStart_1390186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390202 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_1390202 : Nat := 118140960795 + 1390202 * 2 ^ 59
def prefixEnd_1390202 : Nat := 4983230072969 + 3 ^ 40 * 1390202 * 2
def baseEnd_1390202 : Nat := 237947277613958353993861

theorem tailTrace_1390202 : CollatzResearch.WordTrace tailWord_1390202 prefixEnd_1390202 237947277613958353993861 := by
  unfold tailWord_1390202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676208127385764111033215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33803221673028704296088573 12676208127385764111033215)
  ·
    refine ⟨19014312191078646166549823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12676208127385764111033215 19014312191078646166549823)
    ·
      refine ⟨28521468286617969249824735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19014312191078646166549823 28521468286617969249824735)
      ·
        refine ⟨42782202429926953874737103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28521468286617969249824735 42782202429926953874737103)
        ·
          refine ⟨64173303644890430812105655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42782202429926953874737103 64173303644890430812105655)
          ·
            refine ⟨96259955467335646218158483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64173303644890430812105655 96259955467335646218158483)
            ·
              refine ⟨144389933201003469327237725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96259955467335646218158483 144389933201003469327237725)
              ·
                refine ⟨54146224950376300997714147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144389933201003469327237725 54146224950376300997714147)
                ·
                  refine ⟨81219337425564451496571221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54146224950376300997714147 81219337425564451496571221)
                  ·
                    refine ⟨237947277613958353993861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 81219337425564451496571221 237947277613958353993861)
                    ·
                      rfl

theorem cell23_1390202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_1390202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390202 prefixEnd_1390202 := by exact prefixLift 1390202
  have htrace : WordTrace (prefixWord ++ tailWord_1390202) baseStart_1390202 baseEnd_1390202 := by
    simpa [prefixWord, tailWord_1390202, baseEnd_1390202] using wordTrace_append hprefix tailTrace_1390202
  have hstable : (prefixWord ++ tailWord_1390202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390202).length < 2 ^ (prefixWord ++ tailWord_1390202).sum := by decide
  have hdescent : baseEnd_1390202 < baseStart_1390202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390219 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 5, 4]
def baseStart_1390219 : Nat := 118140960795 + 1390219 * 2 ^ 59
def prefixEnd_1390219 : Nat := 4983230072969 + 3 ^ 40 * 1390219 * 2
def baseEnd_1390219 : Nat := 237950187337667165156335

theorem tailTrace_1390219 : CollatzResearch.WordTrace tailWord_1390219 prefixEnd_1390219 237950187337667165156335 := by
  unfold tailWord_1390219
  simp only [CollatzResearch.WordTrace]
  refine ⟨50705452550481468347501711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33803635033654312231667807 50705452550481468347501711)
  ·
    refine ⟨76058178825722202521252567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50705452550481468347501711 76058178825722202521252567)
    ·
      refine ⟨114087268238583303781878851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76058178825722202521252567 114087268238583303781878851)
      ·
        refine ⟨171130902357874955672818277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114087268238583303781878851 171130902357874955672818277)
        ·
          refine ⟨32087044192101554188653427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171130902357874955672818277 32087044192101554188653427)
          ·
            refine ⟨48130566288152331282980141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32087044192101554188653427 48130566288152331282980141)
            ·
              refine ⟨18048962358057124231117553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48130566288152331282980141 18048962358057124231117553)
              ·
                refine ⟨13536721768542843173338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18048962358057124231117553 13536721768542843173338165)
                ·
                  refine ⟨1269067665800891547500453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13536721768542843173338165 1269067665800891547500453)
                  ·
                    refine ⟨237950187337667165156335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269067665800891547500453 237950187337667165156335)
                    ·
                      rfl

theorem cell23_1390219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 4].length) (baseStart_1390219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390219 prefixEnd_1390219 := by exact prefixLift 1390219
  have htrace : WordTrace (prefixWord ++ tailWord_1390219) baseStart_1390219 baseEnd_1390219 := by
    simpa [prefixWord, tailWord_1390219, baseEnd_1390219] using wordTrace_append hprefix tailTrace_1390219
  have hstable : (prefixWord ++ tailWord_1390219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390219).length < 2 ^ (prefixWord ++ tailWord_1390219).sum := by decide
  have hdescent : baseEnd_1390219 < baseStart_1390219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390259 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3]
def baseStart_1390259 : Nat := 118140960795 + 1390259 * 2 ^ 59
def prefixEnd_1390259 : Nat := 4983230072969 + 3 ^ 40 * 1390259 * 2
def baseEnd_1390259 : Nat := 713871101239181338968821

theorem tailTrace_1390259 : CollatzResearch.WordTrace tailWord_1390259 prefixEnd_1390259 713871101239181338968821 := by
  unfold tailWord_1390259
  simp only [CollatzResearch.WordTrace]
  refine ⟨50706911470336555178957831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33804607646891036785971887 50706911470336555178957831)
  ·
    refine ⟨76060367205504832768436747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50706911470336555178957831 76060367205504832768436747)
    ·
      refine ⟨114090550808257249152655121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76060367205504832768436747 114090550808257249152655121)
      ·
        refine ⟨85567913106192936864491341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114090550808257249152655121 85567913106192936864491341)
        ·
          refine ⟨32087967414822351324184253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85567913106192936864491341 32087967414822351324184253)
          ·
            refine ⟨12032987780558381746569095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32087967414822351324184253 12032987780558381746569095)
            ·
              refine ⟨18049481670837572619853643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12032987780558381746569095 18049481670837572619853643)
              ·
                refine ⟨27074222506256358929780465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18049481670837572619853643 27074222506256358929780465)
                ·
                  refine ⟨20305666879692269197335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27074222506256358929780465 20305666879692269197335349)
                  ·
                    refine ⟨1903656269971150237250189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20305666879692269197335349 1903656269971150237250189)
                    ·
                      refine ⟨713871101239181338968821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903656269971150237250189 713871101239181338968821)
                      ·
                        rfl

theorem cell23_1390259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_1390259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390259 prefixEnd_1390259 := by exact prefixLift 1390259
  have htrace : WordTrace (prefixWord ++ tailWord_1390259) baseStart_1390259 baseEnd_1390259 := by
    simpa [prefixWord, tailWord_1390259, baseEnd_1390259] using wordTrace_append hprefix tailTrace_1390259
  have hstable : (prefixWord ++ tailWord_1390259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390259).length < 2 ^ (prefixWord ++ tailWord_1390259).sum := by decide
  have hdescent : baseEnd_1390259 < baseStart_1390259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390270 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1390270 : Nat := 118140960795 + 1390270 * 2 ^ 59
def prefixEnd_1390270 : Nat := 4983230072969 + 3 ^ 40 * 1390270 * 2
def baseEnd_1390270 : Nat := 237958916508793598643757

theorem tailTrace_1390270 : CollatzResearch.WordTrace tailWord_1390270 prefixEnd_1390270 237958916508793598643757 := by
  unfold tailWord_1390270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338414084162088007201033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33804875115531136038405509 6338414084162088007201033)
  ·
    refine ⟨4753810563121566005400775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6338414084162088007201033 4753810563121566005400775)
    ·
      refine ⟨7130715844682349008101163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4753810563121566005400775 7130715844682349008101163)
      ·
        refine ⟨10696073767023523512151745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130715844682349008101163 10696073767023523512151745)
        ·
          refine ⟨8022055325267642634113809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10696073767023523512151745 8022055325267642634113809)
          ·
            refine ⟨6016541493950731975585357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022055325267642634113809 6016541493950731975585357)
            ·
              refine ⟨2256203060231524490844509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6016541493950731975585357 2256203060231524490844509)
              ·
                refine ⟨846076147586821684066691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256203060231524490844509 846076147586821684066691)
                ·
                  refine ⟨1269114221380232526100037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846076147586821684066691 1269114221380232526100037)
                  ·
                    refine ⟨237958916508793598643757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269114221380232526100037 237958916508793598643757)
                    ·
                      rfl

theorem cell23_1390270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1390270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390270 prefixEnd_1390270 := by exact prefixLift 1390270
  have htrace : WordTrace (prefixWord ++ tailWord_1390270) baseStart_1390270 baseEnd_1390270 := by
    simpa [prefixWord, tailWord_1390270, baseEnd_1390270] using wordTrace_append hprefix tailTrace_1390270
  have hstable : (prefixWord ++ tailWord_1390270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390270).length < 2 ^ (prefixWord ++ tailWord_1390270).sum := by decide
  have hdescent : baseEnd_1390270 < baseStart_1390270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390316 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_1390316 : Nat := 118140960795 + 1390316 * 2 ^ 59
def prefixEnd_1390316 : Nat := 4983230072969 + 3 ^ 40 * 1390316 * 2
def baseEnd_1390316 : Nat := 713900369636487615956059

theorem tailTrace_1390316 : CollatzResearch.WordTrace tailWord_1390316 prefixEnd_1390316 713900369636487615956059 := by
  unfold tailWord_1390316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25354495215565026956891401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33805993620753369275855201 25354495215565026956891401)
  ·
    refine ⟨19015871411673770217668551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25354495215565026956891401 19015871411673770217668551)
    ·
      refine ⟨28523807117510655326502827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19015871411673770217668551 28523807117510655326502827)
      ·
        refine ⟨42785710676265982989754241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28523807117510655326502827 42785710676265982989754241)
        ·
          refine ⟨32089283007199487242315681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42785710676265982989754241 32089283007199487242315681)
          ·
            refine ⟨24066962255399615431736761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32089283007199487242315681 24066962255399615431736761)
            ·
              refine ⟨18050221691549711573802571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24066962255399615431736761 18050221691549711573802571)
              ·
                refine ⟨27075332537324567360703857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18050221691549711573802571 27075332537324567360703857)
                ·
                  refine ⟨20306499402993425520527893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27075332537324567360703857 20306499402993425520527893)
                  ·
                    refine ⟨951867159515316821274745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20306499402993425520527893 951867159515316821274745)
                    ·
                      refine ⟨713900369636487615956059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951867159515316821274745 713900369636487615956059)
                      ·
                        rfl

theorem cell23_1390316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_1390316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390316 prefixEnd_1390316 := by exact prefixLift 1390316
  have htrace : WordTrace (prefixWord ++ tailWord_1390316) baseStart_1390316 baseEnd_1390316 := by
    simpa [prefixWord, tailWord_1390316, baseEnd_1390316] using wordTrace_append hprefix tailTrace_1390316
  have hstable : (prefixWord ++ tailWord_1390316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390316).length < 2 ^ (prefixWord ++ tailWord_1390316).sum := by decide
  have hdescent : baseEnd_1390316 < baseStart_1390316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390326 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1390326 : Nat := 118140960795 + 1390326 * 2 ^ 59
def prefixEnd_1390326 : Nat := 4983230072969 + 3 ^ 40 * 1390326 * 2
def baseEnd_1390326 : Nat := 237968501481010858943671

theorem tailTrace_1390326 : CollatzResearch.WordTrace tailWord_1390326 prefixEnd_1390326 237968501481010858943671 := by
  unfold tailWord_1390326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169334697568364101352927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33806236774062550414431221 3169334697568364101352927)
  ·
    refine ⟨4754002046352546152029391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169334697568364101352927 4754002046352546152029391)
    ·
      refine ⟨7131003069528819228044087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4754002046352546152029391 7131003069528819228044087)
      ·
        refine ⟨10696504604293228842066131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131003069528819228044087 10696504604293228842066131)
        ·
          refine ⟨16044756906439843263099197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10696504604293228842066131 16044756906439843263099197)
          ·
            refine ⟨6016783839914941223662199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16044756906439843263099197 6016783839914941223662199)
            ·
              refine ⟨9025175759872411835493299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016783839914941223662199 9025175759872411835493299)
              ·
                refine ⟨13537763639808617753239949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9025175759872411835493299 13537763639808617753239949)
                ·
                  refine ⟨5076661364928231657464981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13537763639808617753239949 5076661364928231657464981)
                  ·
                    refine ⟨237968501481010858943671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5076661364928231657464981 237968501481010858943671)
                    ·
                      rfl

theorem cell23_1390326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1390326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390326 prefixEnd_1390326 := by exact prefixLift 1390326
  have htrace : WordTrace (prefixWord ++ tailWord_1390326) baseStart_1390326 baseEnd_1390326 := by
    simpa [prefixWord, tailWord_1390326, baseEnd_1390326] using wordTrace_append hprefix tailTrace_1390326
  have hstable : (prefixWord ++ tailWord_1390326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390326).length < 2 ^ (prefixWord ++ tailWord_1390326).sum := by decide
  have hdescent : baseEnd_1390326 < baseStart_1390326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390333 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_1390333 : Nat := 118140960795 + 1390333 * 2 ^ 59
def prefixEnd_1390333 : Nat := 4983230072969 + 3 ^ 40 * 1390333 * 2
def baseEnd_1390333 : Nat := 713909098807614049443481

theorem tailTrace_1390333 : CollatzResearch.WordTrace tailWord_1390333 prefixEnd_1390333 713909098807614049443481 := by
  unfold tailWord_1390333
  simp only [CollatzResearch.WordTrace]
  refine ⟨50709610472068465817151653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33806406981378977211434435 50709610472068465817151653)
  ·
    refine ⟨9508051963512837340715935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50709610472068465817151653 9508051963512837340715935)
    ·
      refine ⟨14262077945269256011073903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508051963512837340715935 14262077945269256011073903)
      ·
        refine ⟨21393116917903884016610855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14262077945269256011073903 21393116917903884016610855)
        ·
          refine ⟨32089675376855826024916283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21393116917903884016610855 32089675376855826024916283)
          ·
            refine ⟨48134513065283739037374425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32089675376855826024916283 48134513065283739037374425)
            ·
              refine ⟨36100884798962804278030819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48134513065283739037374425 36100884798962804278030819)
              ·
                refine ⟨54151327198444206417046229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36100884798962804278030819 54151327198444206417046229)
                ·
                  refine ⟨1269171731213536087899521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 54151327198444206417046229 1269171731213536087899521)
                  ·
                    refine ⟨951878798410152065924641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269171731213536087899521 951878798410152065924641)
                    ·
                      refine ⟨713909098807614049443481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951878798410152065924641 713909098807614049443481)
                      ·
                        rfl

theorem cell23_1390333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_1390333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390333 prefixEnd_1390333 := by exact prefixLift 1390333
  have htrace : WordTrace (prefixWord ++ tailWord_1390333) baseStart_1390333 baseEnd_1390333 := by
    simpa [prefixWord, tailWord_1390333, baseEnd_1390333] using wordTrace_append hprefix tailTrace_1390333
  have hstable : (prefixWord ++ tailWord_1390333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390333).length < 2 ^ (prefixWord ++ tailWord_1390333).sum := by decide
  have hdescent : baseEnd_1390333 < baseStart_1390333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390387 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 1, 2, 3]
def baseStart_1390387 : Nat := 118140960795 + 1390387 * 2 ^ 59
def prefixEnd_1390387 : Nat := 4983230072969 + 3 ^ 40 * 1390387 * 2
def baseEnd_1390387 : Nat := 713936826762956838168233

theorem tailTrace_1390387 : CollatzResearch.WordTrace tailWord_1390387 prefixEnd_1390387 713936826762956838168233 := by
  unfold tailWord_1390387
  simp only [CollatzResearch.WordTrace]
  refine ⟨50711580013872833039617415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33807720009248555359744943 50711580013872833039617415)
  ·
    refine ⟨76067370020809249559426123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50711580013872833039617415 76067370020809249559426123)
    ·
      refine ⟨114101055031213874339139185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76067370020809249559426123 114101055031213874339139185)
      ·
        refine ⟨85575791273410405754354389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114101055031213874339139185 85575791273410405754354389)
        ·
          refine ⟨2005682607970556384867681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85575791273410405754354389 2005682607970556384867681)
          ·
            refine ⟨1504261955977917288650761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005682607970556384867681 1504261955977917288650761)
            ·
              refine ⟨1128196466983437966488071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504261955977917288650761 1128196466983437966488071)
              ·
                refine ⟨1692294700475156949732107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128196466983437966488071 1692294700475156949732107)
                ·
                  refine ⟨2538442050712735424598161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692294700475156949732107 2538442050712735424598161)
                  ·
                    refine ⟨1903831538034551568448621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538442050712735424598161 1903831538034551568448621)
                    ·
                      refine ⟨713936826762956838168233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903831538034551568448621 713936826762956838168233)
                      ·
                        rfl

theorem cell23_1390387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 2, 3].length) (baseStart_1390387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390387 prefixEnd_1390387 := by exact prefixLift 1390387
  have htrace : WordTrace (prefixWord ++ tailWord_1390387) baseStart_1390387 baseEnd_1390387 := by
    simpa [prefixWord, tailWord_1390387, baseEnd_1390387] using wordTrace_append hprefix tailTrace_1390387
  have hstable : (prefixWord ++ tailWord_1390387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390387).length < 2 ^ (prefixWord ++ tailWord_1390387).sum := by decide
  have hdescent : baseEnd_1390387 < baseStart_1390387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390417 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_1390417 : Nat := 118140960795 + 1390417 * 2 ^ 59
def prefixEnd_1390417 : Nat := 4983230072969 + 3 ^ 40 * 1390417 * 2
def baseEnd_1390417 : Nat := 713952231182591720793095

theorem tailTrace_1390417 : CollatzResearch.WordTrace tailWord_1390417 prefixEnd_1390417 713952231182591720793095 := by
  unfold tailWord_1390417
  simp only [CollatzResearch.WordTrace]
  refine ⟨50712674203764148163209505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33808449469176098775473003 50712674203764148163209505)
  ·
    refine ⟨38034505652823111122407129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50712674203764148163209505 38034505652823111122407129)
    ·
      refine ⟨28525879239617333341805347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38034505652823111122407129 28525879239617333341805347)
      ·
        refine ⟨42788818859426000012708021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28525879239617333341805347 42788818859426000012708021)
        ·
          refine ⟨4011451768071187501191377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42788818859426000012708021 4011451768071187501191377)
          ·
            refine ⟨3008588826053390625893533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4011451768071187501191377 3008588826053390625893533)
            ·
              refine ⟨1128220809770021484710075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3008588826053390625893533 1128220809770021484710075)
              ·
                refine ⟨1692331214655032227065113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128220809770021484710075 1692331214655032227065113)
                ·
                  refine ⟨1269248410991274170298835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692331214655032227065113 1269248410991274170298835)
                  ·
                    refine ⟨1903872616486911255448253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269248410991274170298835 1903872616486911255448253)
                    ·
                      refine ⟨713952231182591720793095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1903872616486911255448253 713952231182591720793095)
                      ·
                        rfl

theorem cell23_1390417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_1390417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390417 prefixEnd_1390417 := by exact prefixLift 1390417
  have htrace : WordTrace (prefixWord ++ tailWord_1390417) baseStart_1390417 baseEnd_1390417 := by
    simpa [prefixWord, tailWord_1390417, baseEnd_1390417] using wordTrace_append hprefix tailTrace_1390417
  have hstable : (prefixWord ++ tailWord_1390417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390417).length < 2 ^ (prefixWord ++ tailWord_1390417).sum := by decide
  have hdescent : baseEnd_1390417 < baseStart_1390417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390426 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1390426 : Nat := 118140960795 + 1390426 * 2 ^ 59
def prefixEnd_1390426 : Nat := 4983230072969 + 3 ^ 40 * 1390426 * 2
def baseEnd_1390426 : Nat := 713956852508482185580553

theorem tailTrace_1390426 : CollatzResearch.WordTrace tailWord_1390426 prefixEnd_1390426 713956852508482185580553 := by
  unfold tailWord_1390426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678250615182885675071783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33808668307154361800191421 12678250615182885675071783)
  ·
    refine ⟨19017375922774328512607675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12678250615182885675071783 19017375922774328512607675)
    ·
      refine ⟨28526063884161492768911513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19017375922774328512607675 28526063884161492768911513)
      ·
        refine ⟨21394547913121119576683635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28526063884161492768911513 21394547913121119576683635)
        ·
          refine ⟨32091821869681679365025453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21394547913121119576683635 32091821869681679365025453)
          ·
            refine ⟨12034433201130629761884545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32091821869681679365025453 12034433201130629761884545)
            ·
              refine ⟨9025824900847972321413409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12034433201130629761884545 9025824900847972321413409)
              ·
                refine ⟨6769368675635979241060057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9025824900847972321413409 6769368675635979241060057)
                ·
                  refine ⟨5077026506726984430795043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6769368675635979241060057 5077026506726984430795043)
                  ·
                    refine ⟨7615539760090476646192565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077026506726984430795043 7615539760090476646192565)
                    ·
                      refine ⟨713956852508482185580553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7615539760090476646192565 713956852508482185580553)
                      ·
                        rfl

theorem cell23_1390426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1390426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390426 prefixEnd_1390426 := by exact prefixLift 1390426
  have htrace : WordTrace (prefixWord ++ tailWord_1390426) baseStart_1390426 baseEnd_1390426 := by
    simpa [prefixWord, tailWord_1390426, baseEnd_1390426] using wordTrace_append hprefix tailTrace_1390426
  have hstable : (prefixWord ++ tailWord_1390426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390426).length < 2 ^ (prefixWord ++ tailWord_1390426).sum := by decide
  have hdescent : baseEnd_1390426 < baseStart_1390426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390440 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1390440 : Nat := 118140960795 + 1390440 * 2 ^ 59
def prefixEnd_1390440 : Nat := 4983230072969 + 3 ^ 40 * 1390440 * 2
def baseEnd_1390440 : Nat := 713964041237645130805489

theorem tailTrace_1390440 : CollatzResearch.WordTrace tailWord_1390440 prefixEnd_1390440 713964041237645130805489 := by
  unfold tailWord_1390440
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356756541340411545648387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33809008721787215394197849 25356756541340411545648387)
  ·
    refine ⟨38035134812010617318472581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25356756541340411545648387 38035134812010617318472581)
    ·
      refine ⟨7131587777251990747213609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38035134812010617318472581 7131587777251990747213609)
      ·
        refine ⟨5348690832938993060410207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7131587777251990747213609 5348690832938993060410207)
        ·
          refine ⟨8023036249408489590615311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5348690832938993060410207 8023036249408489590615311)
          ·
            refine ⟨12034554374112734385922967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8023036249408489590615311 12034554374112734385922967)
            ·
              refine ⟨18051831561169101578884451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12034554374112734385922967 18051831561169101578884451)
              ·
                refine ⟨27077747341753652368326677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18051831561169101578884451 27077747341753652368326677)
                ·
                  refine ⟨1269269406644702454765313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27077747341753652368326677 1269269406644702454765313)
                  ·
                    refine ⟨951952054983526841073985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269269406644702454765313 951952054983526841073985)
                    ·
                      refine ⟨713964041237645130805489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951952054983526841073985 713964041237645130805489)
                      ·
                        rfl

theorem cell23_1390440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1390440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390440 prefixEnd_1390440 := by exact prefixLift 1390440
  have htrace : WordTrace (prefixWord ++ tailWord_1390440) baseStart_1390440 baseEnd_1390440 := by
    simpa [prefixWord, tailWord_1390440, baseEnd_1390440] using wordTrace_append hprefix tailTrace_1390440
  have hstable : (prefixWord ++ tailWord_1390440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390440).length < 2 ^ (prefixWord ++ tailWord_1390440).sum := by decide
  have hdescent : baseEnd_1390440 < baseStart_1390440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390474 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1390474 : Nat := 118140960795 + 1390474 * 2 ^ 59
def prefixEnd_1390474 : Nat := 4983230072969 + 3 ^ 40 * 1390474 * 2
def baseEnd_1390474 : Nat := 713981499579897997780333

theorem tailTrace_1390474 : CollatzResearch.WordTrace tailWord_1390474 prefixEnd_1390474 713981499579897997780333 := by
  unfold tailWord_1390474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678688291139411724508619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33809835443038431265356317 12678688291139411724508619)
  ·
    refine ⟨19018032436709117586762929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12678688291139411724508619 19018032436709117586762929)
    ·
      refine ⟨14263524327531838190072197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19018032436709117586762929 14263524327531838190072197)
      ·
        refine ⟨2674410811412219660638537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14263524327531838190072197 2674410811412219660638537)
        ·
          refine ⟨2005808108559164745478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674410811412219660638537 2005808108559164745478903)
          ·
            refine ⟨3008712162838747118218355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005808108559164745478903 3008712162838747118218355)
            ·
              refine ⟨4513068244258120677327533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008712162838747118218355 4513068244258120677327533)
              ·
                refine ⟨1692400591596795253997825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4513068244258120677327533 1692400591596795253997825)
                ·
                  refine ⟨1269300443697596440498369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692400591596795253997825 1269300443697596440498369)
                  ·
                    refine ⟨951975332773197330373777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269300443697596440498369 951975332773197330373777)
                    ·
                      refine ⟨713981499579897997780333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 951975332773197330373777 713981499579897997780333)
                      ·
                        rfl

theorem cell23_1390474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1390474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390474 prefixEnd_1390474 := by exact prefixLift 1390474
  have htrace : WordTrace (prefixWord ++ tailWord_1390474) baseStart_1390474 baseEnd_1390474 := by
    simpa [prefixWord, tailWord_1390474, baseEnd_1390474] using wordTrace_append hprefix tailTrace_1390474
  have hstable : (prefixWord ++ tailWord_1390474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390474).length < 2 ^ (prefixWord ++ tailWord_1390474).sum := by decide
  have hdescent : baseEnd_1390474 < baseStart_1390474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390476 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1390476 : Nat := 118140960795 + 1390476 * 2 ^ 59
def prefixEnd_1390476 : Nat := 4983230072969 + 3 ^ 40 * 1390476 * 2
def baseEnd_1390476 : Nat := 237994175513735663318441

theorem tailTrace_1390476 : CollatzResearch.WordTrace tailWord_1390476 prefixEnd_1390476 237994175513735663318441 := by
  unfold tailWord_1390476
  simp only [CollatzResearch.WordTrace]
  refine ⟨25357413055275200619803641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33809884073700267493071521 25357413055275200619803641)
  ·
    refine ⟨19018059791456400464852731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25357413055275200619803641 19018059791456400464852731)
    ·
      refine ⟨28527089687184600697279097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19018059791456400464852731 28527089687184600697279097)
      ·
        refine ⟨21395317265388450522959323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28527089687184600697279097 21395317265388450522959323)
        ·
          refine ⟨32092975898082675784438985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21395317265388450522959323 32092975898082675784438985)
          ·
            refine ⟨24069731923562006838329239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32092975898082675784438985 24069731923562006838329239)
            ·
              refine ⟨36104597885343010257493859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24069731923562006838329239 36104597885343010257493859)
              ·
                refine ⟨54156896828014515386240789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36104597885343010257493859 54156896828014515386240789)
                ·
                  refine ⟨2538604538813180408730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54156896828014515386240789 2538604538813180408730037)
                  ·
                    refine ⟨237994175513735663318441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2538604538813180408730037 237994175513735663318441)
                    ·
                      rfl

theorem cell23_1390476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1390476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390476 prefixEnd_1390476 := by exact prefixLift 1390476
  have htrace : WordTrace (prefixWord ++ tailWord_1390476) baseStart_1390476 baseEnd_1390476 := by
    simpa [prefixWord, tailWord_1390476, baseEnd_1390476] using wordTrace_append hprefix tailTrace_1390476
  have hstable : (prefixWord ++ tailWord_1390476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390476).length < 2 ^ (prefixWord ++ tailWord_1390476).sum := by decide
  have hdescent : baseEnd_1390476 < baseStart_1390476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390493 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1390493 : Nat := 118140960795 + 1390493 * 2 ^ 59
def prefixEnd_1390493 : Nat := 4983230072969 + 3 ^ 40 * 1390493 * 2
def baseEnd_1390493 : Nat := 237997085237444474480915

theorem tailTrace_1390493 : CollatzResearch.WordTrace tailWord_1390493 prefixEnd_1390493 237997085237444474480915 := by
  unfold tailWord_1390493
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715446151488813142976133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33810297434325875428650755 50715446151488813142976133)
  ·
    refine ⟨9509146153404152464308025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50715446151488813142976133 9509146153404152464308025)
    ·
      refine ⟨7131859615053114348231019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509146153404152464308025 7131859615053114348231019)
      ·
        refine ⟨10697789422579671522346529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7131859615053114348231019 10697789422579671522346529)
        ·
          refine ⟨8023342066934753641759897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10697789422579671522346529 8023342066934753641759897)
          ·
            refine ⟨6017506550201065231319923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8023342066934753641759897 6017506550201065231319923)
            ·
              refine ⟨9026259825301597846979885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017506550201065231319923 9026259825301597846979885)
              ·
                refine ⟨3384847434488099192617457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9026259825301597846979885 3384847434488099192617457)
                ·
                  refine ⟨2538635575866074394463093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3384847434488099192617457 2538635575866074394463093)
                  ·
                    refine ⟨237997085237444474480915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2538635575866074394463093 237997085237444474480915)
                    ·
                      rfl

theorem cell23_1390493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1390493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390493 prefixEnd_1390493 := by exact prefixLift 1390493
  have htrace : WordTrace (prefixWord ++ tailWord_1390493) baseStart_1390493 baseEnd_1390493 := by
    simpa [prefixWord, tailWord_1390493, baseEnd_1390493] using wordTrace_append hprefix tailTrace_1390493
  have hstable : (prefixWord ++ tailWord_1390493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390493).length < 2 ^ (prefixWord ++ tailWord_1390493).sum := by decide
  have hdescent : baseEnd_1390493 < baseStart_1390493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390503 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1390503 : Nat := 118140960795 + 1390503 * 2 ^ 59
def prefixEnd_1390503 : Nat := 4983230072969 + 3 ^ 40 * 1390503 * 2
def baseEnd_1390503 : Nat := 713996390518878384317699

theorem tailTrace_1390503 : CollatzResearch.WordTrace tailWord_1390503 prefixEnd_1390503 713996390518878384317699 := by
  unfold tailWord_1390503
  simp only [CollatzResearch.WordTrace]
  refine ⟨50715810881452584850840163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33810540587635056567226775 50715810881452584850840163)
  ·
    refine ⟨76073716322178877276260245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50715810881452584850840163 76073716322178877276260245)
    ·
      refine ⟨3565955452602134872324699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76073716322178877276260245 3565955452602134872324699)
      ·
        refine ⟨5348933178903202308487049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565955452602134872324699 5348933178903202308487049)
        ·
          refine ⟨4011699884177401731365287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348933178903202308487049 4011699884177401731365287)
          ·
            refine ⟨6017549826266102597047931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011699884177401731365287 6017549826266102597047931)
            ·
              refine ⟨9026324739399153895571897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017549826266102597047931 9026324739399153895571897)
              ·
                refine ⟨6769743554549365421678923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9026324739399153895571897 6769743554549365421678923)
                ·
                  refine ⟨10154615331824048132518385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6769743554549365421678923 10154615331824048132518385)
                  ·
                    refine ⟨7615961498868036099388789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10154615331824048132518385 7615961498868036099388789)
                    ·
                      refine ⟨713996390518878384317699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7615961498868036099388789 713996390518878384317699)
                      ·
                        rfl

theorem cell23_1390503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1390503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390503 prefixEnd_1390503 := by exact prefixLift 1390503
  have htrace : WordTrace (prefixWord ++ tailWord_1390503) baseStart_1390503 baseEnd_1390503 := by
    simpa [prefixWord, tailWord_1390503, baseEnd_1390503] using wordTrace_append hprefix tailTrace_1390503
  have hstable : (prefixWord ++ tailWord_1390503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390503).length < 2 ^ (prefixWord ++ tailWord_1390503).sum := by decide
  have hdescent : baseEnd_1390503 < baseStart_1390503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390540 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_1390540 : Nat := 118140960795 + 1390540 * 2 ^ 59
def prefixEnd_1390540 : Nat := 4983230072969 + 3 ^ 40 * 1390540 * 2
def baseEnd_1390540 : Nat := 238005129767698246518343

theorem tailTrace_1390540 : CollatzResearch.WordTrace tailWord_1390540 prefixEnd_1390540 238005129767698246518343 := by
  unfold tailWord_1390540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25358580191159270084968537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33811440254879026779958049 25358580191159270084968537)
  ·
    refine ⟨19018935143369452563726403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25358580191159270084968537 19018935143369452563726403)
    ·
      refine ⟨28528402715054178845589605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19018935143369452563726403 28528402715054178845589605)
      ·
        refine ⟨5349075509072658533548051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28528402715054178845589605 5349075509072658533548051)
        ·
          refine ⟨8023613263608987800322077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5349075509072658533548051 8023613263608987800322077)
          ·
            refine ⟨3008854973853370425120779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8023613263608987800322077 3008854973853370425120779)
            ·
              refine ⟨4513282460780055637681169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3008854973853370425120779 4513282460780055637681169)
              ·
                refine ⟨3384961845585041728260877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513282460780055637681169 3384961845585041728260877)
                ·
                  refine ⟨1269360692094390648097829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3384961845585041728260877 1269360692094390648097829)
                  ·
                    refine ⟨238005129767698246518343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269360692094390648097829 238005129767698246518343)
                    ·
                      rfl

theorem cell23_1390540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_1390540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390540 prefixEnd_1390540 := by exact prefixLift 1390540
  have htrace : WordTrace (prefixWord ++ tailWord_1390540) baseStart_1390540 baseEnd_1390540 := by
    simpa [prefixWord, tailWord_1390540, baseEnd_1390540] using wordTrace_append hprefix tailTrace_1390540
  have hstable : (prefixWord ++ tailWord_1390540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390540).length < 2 ^ (prefixWord ++ tailWord_1390540).sum := by decide
  have hdescent : baseEnd_1390540 < baseStart_1390540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390600 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1390600 : Nat := 118140960795 + 1390600 * 2 ^ 59
def prefixEnd_1390600 : Nat := 4983230072969 + 3 ^ 40 * 1390600 * 2
def baseEnd_1390600 : Nat := 238015399380788168268251

theorem tailTrace_1390600 : CollatzResearch.WordTrace tailWord_1390600 prefixEnd_1390600 238015399380788168268251 := by
  unfold tailWord_1390600
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359674381050585208560627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33812899174734113611414169 25359674381050585208560627)
  ·
    refine ⟨38039511571575877812840941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25359674381050585208560627 38039511571575877812840941)
    ·
      refine ⟨14264816839340954179815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38039511571575877812840941 14264816839340954179815353)
      ·
        refine ⟨10698612629505715634861515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14264816839340954179815353 10698612629505715634861515)
        ·
          refine ⟨16047918944258573452292273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698612629505715634861515 16047918944258573452292273)
          ·
            refine ⟨12035939208193930089219205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16047918944258573452292273 12035939208193930089219205)
            ·
              refine ⟨2256738601536361891728601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12035939208193930089219205 2256738601536361891728601)
              ·
                refine ⟨1692553951152271418796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256738601536361891728601 1692553951152271418796451)
                ·
                  refine ⟨2538830926728407128194677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692553951152271418796451 2538830926728407128194677)
                  ·
                    refine ⟨238015399380788168268251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2538830926728407128194677 238015399380788168268251)
                    ·
                      rfl

theorem cell23_1390600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1390600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390600 prefixEnd_1390600 := by exact prefixLift 1390600
  have htrace : WordTrace (prefixWord ++ tailWord_1390600) baseStart_1390600 baseEnd_1390600 := by
    simpa [prefixWord, tailWord_1390600, baseEnd_1390600] using wordTrace_append hprefix tailTrace_1390600
  have hstable : (prefixWord ++ tailWord_1390600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390600).length < 2 ^ (prefixWord ++ tailWord_1390600).sum := by decide
  have hdescent : baseEnd_1390600 < baseStart_1390600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390631 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1390631 : Nat := 118140960795 + 1390631 * 2 ^ 59
def prefixEnd_1390631 : Nat := 4983230072969 + 3 ^ 40 * 1390631 * 2
def baseEnd_1390631 : Nat := 714062116042653883517111

theorem tailTrace_1390631 : CollatzResearch.WordTrace tailWord_1390631 prefixEnd_1390631 714062116042653883517111 := by
  unfold tailWord_1390631
  simp only [CollatzResearch.WordTrace]
  refine ⟨50720479424988862711499747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33813652949992575140999831 50720479424988862711499747)
  ·
    refine ⟨76080719137483294067249621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50720479424988862711499747 76080719137483294067249621)
    ·
      refine ⟨1783141854784764704701163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76080719137483294067249621 1783141854784764704701163)
      ·
        refine ⟨2674712782177147057051745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783141854784764704701163 2674712782177147057051745)
        ·
          refine ⟨2006034586632860292788809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674712782177147057051745 2006034586632860292788809)
          ·
            refine ⟨1504525939974645219591607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006034586632860292788809 1504525939974645219591607)
            ·
              refine ⟨2256788909961967829387411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504525939974645219591607 2256788909961967829387411)
              ·
                refine ⟨3385183364942951744081117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256788909961967829387411 3385183364942951744081117)
                ·
                  refine ⟨1269443761853606904030419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3385183364942951744081117 1269443761853606904030419)
                  ·
                    refine ⟨1904165642780410356045629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269443761853606904030419 1904165642780410356045629)
                    ·
                      refine ⟨714062116042653883517111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904165642780410356045629 714062116042653883517111)
                      ·
                        rfl

theorem cell23_1390631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1390631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390631 prefixEnd_1390631 := by exact prefixLift 1390631
  have htrace : WordTrace (prefixWord ++ tailWord_1390631) baseStart_1390631 baseEnd_1390631 := by
    simpa [prefixWord, tailWord_1390631, baseEnd_1390631] using wordTrace_append hprefix tailTrace_1390631
  have hstable : (prefixWord ++ tailWord_1390631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390631).length < 2 ^ (prefixWord ++ tailWord_1390631).sum := by decide
  have hdescent : baseEnd_1390631 < baseStart_1390631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390647 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 2, 4]
def baseStart_1390647 : Nat := 118140960795 + 1390647 * 2 ^ 59
def prefixEnd_1390647 : Nat := 4983230072969 + 3 ^ 40 * 1390647 * 2
def baseEnd_1390647 : Nat := 238023443911041940305679

theorem tailTrace_1390647 : CollatzResearch.WordTrace tailWord_1390647 prefixEnd_1390647 238023443911041940305679 := by
  unfold tailWord_1390647
  simp only [CollatzResearch.WordTrace]
  refine ⟨50721062992930897444082195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33814041995287264962721463 50721062992930897444082195)
  ·
    refine ⟨76081594489396346166123293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50721062992930897444082195 76081594489396346166123293)
    ·
      refine ⟨28530597933523629812296235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76081594489396346166123293 28530597933523629812296235)
      ·
        refine ⟨42795896900285444718444353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28530597933523629812296235 42795896900285444718444353)
        ·
          refine ⟨32096922675214083538833265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42795896900285444718444353 32096922675214083538833265)
          ·
            refine ⟨24072692006410562654124949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32096922675214083538833265 24072692006410562654124949)
            ·
              refine ⟨1128407437800495124412107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24072692006410562654124949 1128407437800495124412107)
              ·
                refine ⟨1692611156700742686618161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128407437800495124412107 1692611156700742686618161)
                ·
                  refine ⟨1269458367525557014963621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692611156700742686618161 1269458367525557014963621)
                  ·
                    refine ⟨238023443911041940305679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269458367525557014963621 238023443911041940305679)
                    ·
                      rfl

theorem cell23_1390647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_1390647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390647 prefixEnd_1390647 := by exact prefixLift 1390647
  have htrace : WordTrace (prefixWord ++ tailWord_1390647) baseStart_1390647 baseEnd_1390647 := by
    simpa [prefixWord, tailWord_1390647, baseEnd_1390647] using wordTrace_append hprefix tailTrace_1390647
  have hstable : (prefixWord ++ tailWord_1390647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390647).length < 2 ^ (prefixWord ++ tailWord_1390647).sum := by decide
  have hdescent : baseEnd_1390647 < baseStart_1390647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
