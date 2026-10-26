import V185TrunkScan23Chunk1334

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7906920 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7906920 : Nat := 118140960795 + 7906920 * 2 ^ 59
def prefixEnd_7906920 : Nat := 4983230072969 + 3 ^ 40 * 7906920 * 2
def baseEnd_7906920 : Nat := 4060050456648309372836743

theorem tailTrace_7906920 : CollatzResearch.WordTrace tailWord_7906920 prefixEnd_7906920 4060050456648309372836743 := by
  unfold tailWord_7906920
  simp only [CollatzResearch.WordTrace]
  refine ⟨144194532257293354635359107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192259376343057806180478809 144194532257293354635359107)
  ·
    refine ⟨216291798385940031953038661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144194532257293354635359107 216291798385940031953038661)
    ·
      refine ⟨40554712197363755991194749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216291798385940031953038661 40554712197363755991194749)
      ·
        refine ⟨15208017074011408496698031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40554712197363755991194749 15208017074011408496698031)
        ·
          refine ⟨22812025611017112745047047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208017074011408496698031 22812025611017112745047047)
          ·
            refine ⟨34218038416525669117570571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22812025611017112745047047 34218038416525669117570571)
            ·
              refine ⟨51327057624788503676355857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34218038416525669117570571 51327057624788503676355857)
              ·
                refine ⟨38495293218591377757266893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51327057624788503676355857 38495293218591377757266893)
                ·
                  refine ⟨14435734956971766658975085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38495293218591377757266893 14435734956971766658975085)
                  ·
                    refine ⟨5413400608864412497115657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14435734956971766658975085 5413400608864412497115657)
                    ·
                      refine ⟨4060050456648309372836743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413400608864412497115657 4060050456648309372836743)
                      ·
                        rfl

theorem cell23_7906920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7906920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906920 prefixEnd_7906920 := by exact prefixLift 7906920
  have htrace : WordTrace (prefixWord ++ tailWord_7906920) baseStart_7906920 baseEnd_7906920 := by
    simpa [prefixWord, tailWord_7906920, baseEnd_7906920] using wordTrace_append hprefix tailTrace_7906920
  have hstable : (prefixWord ++ tailWord_7906920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906920).length < 2 ^ (prefixWord ++ tailWord_7906920).sum := by decide
  have hdescent : baseEnd_7906920 < baseStart_7906920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906954 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_7906954 : Nat := 118140960795 + 7906954 * 2 ^ 59
def prefixEnd_7906954 : Nat := 4983230072969 + 3 ^ 40 * 7906954 * 2
def baseEnd_7906954 : Nat := 4060067914990562239811587

theorem tailTrace_7906954 : CollatzResearch.WordTrace tailWord_7906954 prefixEnd_7906954 4060067914990562239811587 := by
  unfold tailWord_7906954
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097576149115883269363979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192260203064309022051637277 72097576149115883269363979)
  ·
    refine ⟨108146364223673824904045969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72097576149115883269363979 108146364223673824904045969)
    ·
      refine ⟨81109773167755368678034477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108146364223673824904045969 81109773167755368678034477)
      ·
        refine ⟨30416164937908263254262929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81109773167755368678034477 30416164937908263254262929)
        ·
          refine ⟨22812123703431197440697197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30416164937908263254262929 22812123703431197440697197)
          ·
            refine ⟨8554546388786699040261449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22812123703431197440697197 8554546388786699040261449)
            ·
              refine ⟨6415909791590024280196087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554546388786699040261449 6415909791590024280196087)
              ·
                refine ⟨9623864687385036420294131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415909791590024280196087 9623864687385036420294131)
                ·
                  refine ⟨14435797031077554630441197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623864687385036420294131 14435797031077554630441197)
                  ·
                    refine ⟨5413423886654082986415449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14435797031077554630441197 5413423886654082986415449)
                    ·
                      refine ⟨4060067914990562239811587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413423886654082986415449 4060067914990562239811587)
                      ·
                        rfl

theorem cell23_7906954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_7906954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906954 prefixEnd_7906954 := by exact prefixLift 7906954
  have htrace : WordTrace (prefixWord ++ tailWord_7906954) baseStart_7906954 baseEnd_7906954 := by
    simpa [prefixWord, tailWord_7906954, baseEnd_7906954] using wordTrace_append hprefix tailTrace_7906954
  have hstable : (prefixWord ++ tailWord_7906954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906954).length < 2 ^ (prefixWord ++ tailWord_7906954).sum := by decide
  have hdescent : baseEnd_7906954 < baseStart_7906954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906967 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7906967 : Nat := 118140960795 + 7906967 * 2 ^ 59
def prefixEnd_7906967 : Nat := 4983230072969 + 3 ^ 40 * 7906967 * 2
def baseEnd_7906967 : Nat := 4060074590239070688949027

theorem tailTrace_7906967 : CollatzResearch.WordTrace tailWord_7906967 prefixEnd_7906967 4060074590239070688949027 := by
  unfold tailWord_7906967
  simp only [CollatzResearch.WordTrace]
  refine ⟨288390778745416436297679155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192260519163610957531786103 288390778745416436297679155)
  ·
    refine ⟨432586168118124654446518733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288390778745416436297679155 432586168118124654446518733)
    ·
      refine ⟨162219813044296745417444525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432586168118124654446518733 162219813044296745417444525)
      ·
        refine ⟨60832429891611279531541697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162219813044296745417444525 60832429891611279531541697)
        ·
          refine ⟨45624322418708459648656273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60832429891611279531541697 45624322418708459648656273)
          ·
            refine ⟨34218241814031344736492205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45624322418708459648656273 34218241814031344736492205)
            ·
              refine ⟨12831840680261754276184577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34218241814031344736492205 12831840680261754276184577)
              ·
                refine ⟨9623880510196315707138433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12831840680261754276184577 9623880510196315707138433)
                ·
                  refine ⟨7217910382647236780353825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623880510196315707138433 7217910382647236780353825)
                  ·
                    refine ⟨5413432786985427585265369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217910382647236780353825 5413432786985427585265369)
                    ·
                      refine ⟨4060074590239070688949027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413432786985427585265369 4060074590239070688949027)
                      ·
                        rfl

theorem cell23_7906967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7906967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906967 prefixEnd_7906967 := by exact prefixLift 7906967
  have htrace : WordTrace (prefixWord ++ tailWord_7906967) baseStart_7906967 baseEnd_7906967 := by
    simpa [prefixWord, tailWord_7906967, baseEnd_7906967] using wordTrace_append hprefix tailTrace_7906967
  have hstable : (prefixWord ++ tailWord_7906967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906967).length < 2 ^ (prefixWord ++ tailWord_7906967).sum := by decide
  have hdescent : baseEnd_7906967 < baseStart_7906967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907020 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_7907020 : Nat := 118140960795 + 7907020 * 2 ^ 59
def prefixEnd_7907020 : Nat := 4983230072969 + 3 ^ 40 * 7907020 * 2
def baseEnd_7907020 : Nat := 1353367268237919660528761

theorem tailTrace_7907020 : CollatzResearch.WordTrace tailWord_7907020 prefixEnd_7907020 1353367268237919660528761 := by
  unfold tailWord_7907020
  simp only [CollatzResearch.WordTrace]
  refine ⟨144196355907112213174679257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192261807876149617566239009 144196355907112213174679257)
  ·
    refine ⟨108147266930334159881009443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144196355907112213174679257 108147266930334159881009443)
    ·
      refine ⟨162220900395501239821514165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108147266930334159881009443 162220900395501239821514165)
      ·
        refine ⟨15208209412078241233266953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162220900395501239821514165 15208209412078241233266953)
        ·
          refine ⟨11406157059058680924950215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15208209412078241233266953 11406157059058680924950215)
          ·
            refine ⟨17109235588588021387425323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11406157059058680924950215 17109235588588021387425323)
            ·
              refine ⟨25663853382882032081137985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17109235588588021387425323 25663853382882032081137985)
              ·
                refine ⟨19247890037161524060853489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25663853382882032081137985 19247890037161524060853489)
                ·
                  refine ⟨14435917527871143045640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19247890037161524060853489 14435917527871143045640117)
                  ·
                    refine ⟨1353367268237919660528761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14435917527871143045640117 1353367268237919660528761)
                    ·
                      rfl

theorem cell23_7907020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_7907020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907020 prefixEnd_7907020 := by exact prefixLift 7907020
  have htrace : WordTrace (prefixWord ++ tailWord_7907020) baseStart_7907020 baseEnd_7907020 := by
    simpa [prefixWord, tailWord_7907020, baseEnd_7907020] using wordTrace_append hprefix tailTrace_7907020
  have hstable : (prefixWord ++ tailWord_7907020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907020).length < 2 ^ (prefixWord ++ tailWord_7907020).sum := by decide
  have hdescent : baseEnd_7907020 < baseStart_7907020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907023 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 4, 2]
def baseStart_7907023 : Nat := 118140960795 + 7907023 * 2 ^ 59
def prefixEnd_7907023 : Nat := 4983230072969 + 3 ^ 40 * 7907023 * 2
def baseEnd_7907023 : Nat := 4060103345155722469848769

theorem tailTrace_7907023 : CollatzResearch.WordTrace tailWord_7907023 prefixEnd_7907023 4060103345155722469848769 := by
  unfold tailWord_7907023
  simp only [CollatzResearch.WordTrace]
  refine ⟨288392821233213557861717723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192261880822142371907811815 288392821233213557861717723)
  ·
    refine ⟨432589231849820336792576585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288392821233213557861717723 432589231849820336792576585)
    ·
      refine ⟨324441923887365252594432439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432589231849820336792576585 324441923887365252594432439)
      ·
        refine ⟨486662885831047878891648659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324441923887365252594432439 486662885831047878891648659)
        ·
          refine ⟨729994328746571818337472989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486662885831047878891648659 729994328746571818337472989)
          ·
            refine ⟨273747873279964431876552371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729994328746571818337472989 273747873279964431876552371)
            ·
              refine ⟨410621809919946647814828557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273747873279964431876552371 410621809919946647814828557)
              ·
                refine ⟨153983178719979992930560709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410621809919946647814828557 153983178719979992930560709)
                ·
                  refine ⟨28871846009996248674480133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153983178719979992930560709 28871846009996248674480133)
                  ·
                    refine ⟨5413471126874296626465025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28871846009996248674480133 5413471126874296626465025)
                    ·
                      refine ⟨4060103345155722469848769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413471126874296626465025 4060103345155722469848769)
                      ·
                        rfl

theorem cell23_7907023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4, 2].length) (baseStart_7907023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907023 prefixEnd_7907023 := by exact prefixLift 7907023
  have htrace : WordTrace (prefixWord ++ tailWord_7907023) baseStart_7907023 baseEnd_7907023 := by
    simpa [prefixWord, tailWord_7907023, baseEnd_7907023] using wordTrace_append hprefix tailTrace_7907023
  have hstable : (prefixWord ++ tailWord_7907023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907023).length < 2 ^ (prefixWord ++ tailWord_7907023).sum := by decide
  have hdescent : baseEnd_7907023 < baseStart_7907023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7907066 : Nat := 118140960795 + 7907066 * 2 ^ 59
def prefixEnd_7907066 : Nat := 4983230072969 + 3 ^ 40 * 7907066 * 2
def baseEnd_7907066 : Nat := 4060125424823865801611071

theorem tailTrace_7907066 : CollatzResearch.WordTrace tailWord_7907066 prefixEnd_7907066 4060125424823865801611071 := by
  unfold tailWord_7907066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72098597393014444051383263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192262926381371850803688701 72098597393014444051383263)
  ·
    refine ⟨108147896089521666077074895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72098597393014444051383263 108147896089521666077074895)
    ·
      refine ⟨162221844134282499115612343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108147896089521666077074895 162221844134282499115612343)
      ·
        refine ⟨243332766201423748673418515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162221844134282499115612343 243332766201423748673418515)
        ·
          refine ⟨364999149302135623010127773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243332766201423748673418515 364999149302135623010127773)
          ·
            refine ⟨136874680988300858628797915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364999149302135623010127773 136874680988300858628797915)
            ·
              refine ⟨205312021482451287943196873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136874680988300858628797915 205312021482451287943196873)
              ·
                refine ⟨153984016111838465957397655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205312021482451287943196873 153984016111838465957397655)
                ·
                  refine ⟨230976024167757698936096483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153984016111838465957397655 230976024167757698936096483)
                  ·
                    refine ⟨346464036251636548404144725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230976024167757698936096483 346464036251636548404144725)
                    ·
                      refine ⟨4060125424823865801611071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346464036251636548404144725 4060125424823865801611071)
                      ·
                        rfl

theorem cell23_7907066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7907066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907066 prefixEnd_7907066 := by exact prefixLift 7907066
  have htrace : WordTrace (prefixWord ++ tailWord_7907066) baseStart_7907066 baseEnd_7907066 := by
    simpa [prefixWord, tailWord_7907066, baseEnd_7907066] using wordTrace_append hprefix tailTrace_7907066
  have hstable : (prefixWord ++ tailWord_7907066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907066).length < 2 ^ (prefixWord ++ tailWord_7907066).sum := by decide
  have hdescent : baseEnd_7907066 < baseStart_7907066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907093 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7907093 : Nat := 118140960795 + 7907093 * 2 ^ 59
def prefixEnd_7907093 : Nat := 4983230072969 + 3 ^ 40 * 7907093 * 2
def baseEnd_7907093 : Nat := 1353379762933845731991149

theorem tailTrace_7907093 : CollatzResearch.WordTrace tailWord_7907093 prefixEnd_7907093 1353379762933845731991149 := by
  unfold tailWord_7907093
  simp only [CollatzResearch.WordTrace]
  refine ⟨288395374342959959816765933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192263582895306639877843955 288395374342959959816765933)
  ·
    refine ⟨108148265378609984931287225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288395374342959959816765933 108148265378609984931287225)
    ·
      refine ⟨81111199033957488698465419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108148265378609984931287225 81111199033957488698465419)
      ·
        refine ⟨121666798550936233047698129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81111199033957488698465419 121666798550936233047698129)
        ·
          refine ⟨91250098913202174785773597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121666798550936233047698129 91250098913202174785773597)
          ·
            refine ⟨34218787092450815544665099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91250098913202174785773597 34218787092450815544665099)
            ·
              refine ⟨51328180638676223316997649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34218787092450815544665099 51328180638676223316997649)
              ·
                refine ⟨38496135479007167487748237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51328180638676223316997649 38496135479007167487748237)
                ·
                  refine ⟨14436050804627687807905589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38496135479007167487748237 14436050804627687807905589)
                  ·
                    refine ⟨1353379762933845731991149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14436050804627687807905589 1353379762933845731991149)
                    ·
                      rfl

theorem cell23_7907093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7907093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907093 prefixEnd_7907093 := by exact prefixLift 7907093
  have htrace : WordTrace (prefixWord ++ tailWord_7907093) baseStart_7907093 baseEnd_7907093 := by
    simpa [prefixWord, tailWord_7907093, baseEnd_7907093] using wordTrace_append hprefix tailTrace_7907093
  have hstable : (prefixWord ++ tailWord_7907093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907093).length < 2 ^ (prefixWord ++ tailWord_7907093).sum := by decide
  have hdescent : baseEnd_7907093 < baseStart_7907093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907100 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7907100 : Nat := 118140960795 + 7907100 * 2 ^ 59
def prefixEnd_7907100 : Nat := 4983230072969 + 3 ^ 40 * 7907100 * 2
def baseEnd_7907100 : Nat := 4060142883166118668585915

theorem tailTrace_7907100 : CollatzResearch.WordTrace tailWord_7907100 prefixEnd_7907100 4060142883166118668585915 := by
  unfold tailWord_7907100
  simp only [CollatzResearch.WordTrace]
  refine ⟨144197814826967300006135377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192263753102623066674847169 144197814826967300006135377)
  ·
    refine ⟨108148361120225475004601533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144197814826967300006135377 108148361120225475004601533)
    ·
      refine ⟨40555635420084553126725575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108148361120225475004601533 40555635420084553126725575)
      ·
        refine ⟨60833453130126829690088363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40555635420084553126725575 60833453130126829690088363)
        ·
          refine ⟨91250179695190244535132545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60833453130126829690088363 91250179695190244535132545)
          ·
            refine ⟨68437634771392683401349409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91250179695190244535132545 68437634771392683401349409)
            ·
              refine ⟨51328226078544512551012057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68437634771392683401349409 51328226078544512551012057)
              ·
                refine ⟨38496169558908384413259043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51328226078544512551012057 38496169558908384413259043)
                ·
                  refine ⟨57744254338362576619888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38496169558908384413259043 57744254338362576619888565)
                  ·
                    refine ⟨5413523844221491558114553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57744254338362576619888565 5413523844221491558114553)
                    ·
                      refine ⟨4060142883166118668585915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413523844221491558114553 4060142883166118668585915)
                      ·
                        rfl

theorem cell23_7907100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7907100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907100 prefixEnd_7907100 := by exact prefixLift 7907100
  have htrace : WordTrace (prefixWord ++ tailWord_7907100) baseStart_7907100 baseEnd_7907100 := by
    simpa [prefixWord, tailWord_7907100, baseEnd_7907100] using wordTrace_append hprefix tailTrace_7907100
  have hstable : (prefixWord ++ tailWord_7907100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907100).length < 2 ^ (prefixWord ++ tailWord_7907100).sum := by decide
  have hdescent : baseEnd_7907100 < baseStart_7907100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907143 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_7907143 : Nat := 118140960795 + 7907143 * 2 ^ 59
def prefixEnd_7907143 : Nat := 4983230072969 + 3 ^ 40 * 7907143 * 2
def baseEnd_7907143 : Nat := 4060164962834262000348217

theorem tailTrace_7907143 : CollatzResearch.WordTrace tailWord_7907143 prefixEnd_7907143 4060164962834262000348217 := by
  unfold tailWord_7907143
  simp only [CollatzResearch.WordTrace]
  refine ⟨288397197992778818356086083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192264798661852545570724055 288397197992778818356086083)
  ·
    refine ⟨432595796989168227534129125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288397197992778818356086083 432595796989168227534129125)
    ·
      refine ⟨81111711935469042662649211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432595796989168227534129125 81111711935469042662649211)
      ·
        refine ⟨121667567903203563993973817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81111711935469042662649211 121667567903203563993973817)
        ·
          refine ⟨91250675927402672995480363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121667567903203563993973817 91250675927402672995480363)
          ·
            refine ⟨136876013891104009493220545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91250675927402672995480363 136876013891104009493220545)
            ·
              refine ⟨102657010418328007119915409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136876013891104009493220545 102657010418328007119915409)
              ·
                refine ⟨76992757813746005339936557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102657010418328007119915409 76992757813746005339936557)
                ·
                  refine ⟨28872284180154752002476209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76992757813746005339936557 28872284180154752002476209)
                  ·
                    refine ⟨21654213135116064001857157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28872284180154752002476209 21654213135116064001857157)
                    ·
                      refine ⟨4060164962834262000348217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21654213135116064001857157 4060164962834262000348217)
                      ·
                        rfl

theorem cell23_7907143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_7907143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907143 prefixEnd_7907143 := by exact prefixLift 7907143
  have htrace : WordTrace (prefixWord ++ tailWord_7907143) baseStart_7907143 baseEnd_7907143 := by
    simpa [prefixWord, tailWord_7907143, baseEnd_7907143] using wordTrace_append hprefix tailTrace_7907143
  have hstable : (prefixWord ++ tailWord_7907143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907143).length < 2 ^ (prefixWord ++ tailWord_7907143).sum := by decide
  have hdescent : baseEnd_7907143 < baseStart_7907143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907164 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7907164 : Nat := 118140960795 + 7907164 * 2 ^ 59
def prefixEnd_7907164 : Nat := 4983230072969 + 3 ^ 40 * 7907164 * 2
def baseEnd_7907164 : Nat := 4060175745928006418185621

theorem tailTrace_7907164 : CollatzResearch.WordTrace tailWord_7907164 prefixEnd_7907164 4060175745928006418185621 := by
  unfold tailWord_7907164
  simp only [CollatzResearch.WordTrace]
  refine ⟨144198981962851369471300273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192265309283801825961733697 144198981962851369471300273)
  ·
    refine ⟨108149236472138527103475205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144198981962851369471300273 108149236472138527103475205)
    ·
      refine ⟨20277981838525973831901601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108149236472138527103475205 20277981838525973831901601)
      ·
        refine ⟨15208486378894480373926201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20277981838525973831901601 15208486378894480373926201)
        ·
          refine ⟨11406364784170860280444651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15208486378894480373926201 11406364784170860280444651)
          ·
            refine ⟨17109547176256290420666977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11406364784170860280444651 17109547176256290420666977)
            ·
              refine ⟨12832160382192217815500233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17109547176256290420666977 12832160382192217815500233)
              ·
                refine ⟨9624120286644163361625175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12832160382192217815500233 9624120286644163361625175)
                ·
                  refine ⟨14436180429966245042437763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624120286644163361625175 14436180429966245042437763)
                  ·
                    refine ⟨21654270644949367563656645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14436180429966245042437763 21654270644949367563656645)
                    ·
                      refine ⟨4060175745928006418185621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21654270644949367563656645 4060175745928006418185621)
                      ·
                        rfl

theorem cell23_7907164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7907164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907164 prefixEnd_7907164 := by exact prefixLift 7907164
  have htrace : WordTrace (prefixWord ++ tailWord_7907164) baseStart_7907164 baseEnd_7907164 := by
    simpa [prefixWord, tailWord_7907164, baseEnd_7907164] using wordTrace_append hprefix tailTrace_7907164
  have hstable : (prefixWord ++ tailWord_7907164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907164).length < 2 ^ (prefixWord ++ tailWord_7907164).sum := by decide
  have hdescent : baseEnd_7907164 < baseStart_7907164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907167 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_7907167 : Nat := 118140960795 + 7907167 * 2 ^ 59
def prefixEnd_7907167 : Nat := 4983230072969 + 3 ^ 40 * 7907167 * 2
def baseEnd_7907167 : Nat := 4060177286369969906448107

theorem tailTrace_7907167 : CollatzResearch.WordTrace tailWord_7907167 prefixEnd_7907167 4060177286369969906448107 := by
  unfold tailWord_7907167
  simp only [CollatzResearch.WordTrace]
  refine ⟨288398073344691870454959755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192265382229794580303306503 288398073344691870454959755)
  ·
    refine ⟨432597110017037805682439633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288398073344691870454959755 432597110017037805682439633)
    ·
      refine ⟨324447832512778354261829725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432597110017037805682439633 324447832512778354261829725)
      ·
        refine ⟨121667937192291882848186147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324447832512778354261829725 121667937192291882848186147)
        ·
          refine ⟨182501905788437824272279221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121667937192291882848186147 182501905788437824272279221)
          ·
            refine ⟨17109553667666046025526177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182501905788437824272279221 17109553667666046025526177)
            ·
              refine ⟨12832165250749534519144633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17109553667666046025526177 12832165250749534519144633)
              ·
                refine ⟨9624123938062150889358475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12832165250749534519144633 9624123938062150889358475)
                ·
                  refine ⟨14436185907093226334037713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624123938062150889358475 14436185907093226334037713)
                  ·
                    refine ⟨10827139430319919750528285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14436185907093226334037713 10827139430319919750528285)
                    ·
                      refine ⟨4060177286369969906448107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827139430319919750528285 4060177286369969906448107)
                      ·
                        rfl

theorem cell23_7907167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_7907167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907167 prefixEnd_7907167 := by exact prefixLift 7907167
  have htrace : WordTrace (prefixWord ++ tailWord_7907167) baseStart_7907167 baseEnd_7907167 := by
    simpa [prefixWord, tailWord_7907167, baseEnd_7907167] using wordTrace_append hprefix tailTrace_7907167
  have hstable : (prefixWord ++ tailWord_7907167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907167).length < 2 ^ (prefixWord ++ tailWord_7907167).sum := by decide
  have hdescent : baseEnd_7907167 < baseStart_7907167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907170 : List Nat := [3, 3, 2, 1, 2, 2, 1, 9]
def baseStart_7907170 : Nat := 118140960795 + 7907170 * 2 ^ 59
def prefixEnd_7907170 : Nat := 4983230072969 + 3 ^ 40 * 7907170 * 2
def baseEnd_7907170 : Nat := 150376993585627162767059

theorem tailTrace_7907170 : CollatzResearch.WordTrace tailWord_7907170 prefixEnd_7907170 150376993585627162767059 := by
  unfold tailWord_7907170
  simp only [CollatzResearch.WordTrace]
  refine ⟨72099545690920250491829741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192265455175787334644879309 72099545690920250491829741)
  ·
    refine ⟨27037329634095093934436153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72099545690920250491829741 27037329634095093934436153)
    ·
      refine ⟨20277997225571320450827115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27037329634095093934436153 20277997225571320450827115)
      ·
        refine ⟨30416995838356980676240673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20277997225571320450827115 30416995838356980676240673)
        ·
          refine ⟨22812746878767735507180505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30416995838356980676240673 22812746878767735507180505)
          ·
            refine ⟨17109560159075801630385379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22812746878767735507180505 17109560159075801630385379)
            ·
              refine ⟨25664340238613702445578069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17109560159075801630385379 25664340238613702445578069)
              ·
                refine ⟨150376993585627162767059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25664340238613702445578069 150376993585627162767059)
                ·
                  rfl

theorem cell23_7907170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_7907170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907170 prefixEnd_7907170 := by exact prefixLift 7907170
  have htrace : WordTrace (prefixWord ++ tailWord_7907170) baseStart_7907170 baseEnd_7907170 := by
    simpa [prefixWord, tailWord_7907170, baseEnd_7907170] using wordTrace_append hprefix tailTrace_7907170
  have hstable : (prefixWord ++ tailWord_7907170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907170).length < 2 ^ (prefixWord ++ tailWord_7907170).sum := by decide
  have hdescent : baseEnd_7907170 < baseStart_7907170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907181 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7907181 : Nat := 118140960795 + 7907181 * 2 ^ 59
def prefixEnd_7907181 : Nat := 4983230072969 + 3 ^ 40 * 7907181 * 2
def baseEnd_7907181 : Nat := 4060184475099132851673043

theorem tailTrace_7907181 : CollatzResearch.WordTrace tailWord_7907181 prefixEnd_7907181 4060184475099132851673043 := by
  unfold tailWord_7907181
  simp only [CollatzResearch.WordTrace]
  refine ⟨288398583966641150845969397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192265722644427433897312931 288398583966641150845969397)
  ·
    refine ⟨27037367246872607891809631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288398583966641150845969397 27037367246872607891809631)
    ·
      refine ⟨40556050870308911837714447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27037367246872607891809631 40556050870308911837714447)
      ·
        refine ⟨60834076305463367756571671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40556050870308911837714447 60834076305463367756571671)
        ·
          refine ⟨91251114458195051634857507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60834076305463367756571671 91251114458195051634857507)
          ·
            refine ⟨136876671687292577452286261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91251114458195051634857507 136876671687292577452286261)
            ·
              refine ⟨12832187970683679136151837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136876671687292577452286261 12832187970683679136151837)
              ·
                refine ⟨4812070489006379676056939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12832187970683679136151837 4812070489006379676056939)
                ·
                  refine ⟨7218105733509569514085409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812070489006379676056939 7218105733509569514085409)
                  ·
                    refine ⟨5413579300132177135564057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218105733509569514085409 5413579300132177135564057)
                    ·
                      refine ⟨4060184475099132851673043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413579300132177135564057 4060184475099132851673043)
                      ·
                        rfl

theorem cell23_7907181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7907181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907181 prefixEnd_7907181 := by exact prefixLift 7907181
  have htrace : WordTrace (prefixWord ++ tailWord_7907181) baseStart_7907181 baseEnd_7907181 := by
    simpa [prefixWord, tailWord_7907181, baseEnd_7907181] using wordTrace_append hprefix tailTrace_7907181
  have hstable : (prefixWord ++ tailWord_7907181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907181).length < 2 ^ (prefixWord ++ tailWord_7907181).sum := by decide
  have hdescent : baseEnd_7907181 < baseStart_7907181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907193 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7907193 : Nat := 118140960795 + 7907193 * 2 ^ 59
def prefixEnd_7907193 : Nat := 4983230072969 + 3 ^ 40 * 7907193 * 2
def baseEnd_7907193 : Nat := 4060190636866986804722987

theorem tailTrace_7907193 : CollatzResearch.WordTrace tailWord_7907193 prefixEnd_7907193 4060190636866986804722987 := by
  unfold tailWord_7907193
  simp only [CollatzResearch.WordTrace]
  refine ⟨288399021642597676895406233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192266014428398451263604155 288399021642597676895406233)
  ·
    refine ⟨216299266231948257671554675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288399021642597676895406233 216299266231948257671554675)
    ·
      refine ⟨324448899347922386507332013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216299266231948257671554675 324448899347922386507332013)
      ·
        refine ⟨121668337255470894940249505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324448899347922386507332013 121668337255470894940249505)
        ·
          refine ⟨91251252941603171205187129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121668337255470894940249505 91251252941603171205187129)
          ·
            refine ⟨68438439706202378403890347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91251252941603171205187129 68438439706202378403890347)
            ·
              refine ⟨102657659559303567605835521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68438439706202378403890347 102657659559303567605835521)
              ·
                refine ⟨76993244669477675704376641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102657659559303567605835521 76993244669477675704376641)
                ·
                  refine ⟨57744933502108256778282481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76993244669477675704376641 57744933502108256778282481)
                  ·
                    refine ⟨43308700126581192583711861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57744933502108256778282481 43308700126581192583711861)
                    ·
                      refine ⟨4060190636866986804722987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43308700126581192583711861 4060190636866986804722987)
                      ·
                        rfl

theorem cell23_7907193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7907193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907193 prefixEnd_7907193 := by exact prefixLift 7907193
  have htrace : WordTrace (prefixWord ++ tailWord_7907193) baseStart_7907193 baseEnd_7907193 := by
    simpa [prefixWord, tailWord_7907193, baseEnd_7907193] using wordTrace_append hprefix tailTrace_7907193
  have hstable : (prefixWord ++ tailWord_7907193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907193).length < 2 ^ (prefixWord ++ tailWord_7907193).sum := by decide
  have hdescent : baseEnd_7907193 < baseStart_7907193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907197 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_7907197 : Nat := 118140960795 + 7907197 * 2 ^ 59
def prefixEnd_7907197 : Nat := 4983230072969 + 3 ^ 40 * 7907197 * 2
def baseEnd_7907197 : Nat := 4060192690789604789072969

theorem tailTrace_7907197 : CollatzResearch.WordTrace tailWord_7907197 prefixEnd_7907197 4060192690789604789072969 := by
  unfold tailWord_7907197
  simp only [CollatzResearch.WordTrace]
  refine ⟨288399167534583185578551845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192266111689722123719034563 288399167534583185578551845)
  ·
    refine ⟨54074843912734347295978471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288399167534583185578551845 54074843912734347295978471)
    ·
      refine ⟨81112265869101520943967707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54074843912734347295978471 81112265869101520943967707)
      ·
        refine ⟨121668398803652281415951561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81112265869101520943967707 121668398803652281415951561)
        ·
          refine ⟨91251299102739211061963671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121668398803652281415951561 91251299102739211061963671)
          ·
            refine ⟨136876948654108816592945507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91251299102739211061963671 136876948654108816592945507)
            ·
              refine ⟨205315422981163224889418261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136876948654108816592945507 205315422981163224889418261)
              ·
                refine ⟨9624160452242026166691481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205315422981163224889418261 9624160452242026166691481)
                ·
                  refine ⟨7218120339181519625018611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624160452242026166691481 7218120339181519625018611)
                  ·
                    refine ⟨10827180508772279437527917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218120339181519625018611 10827180508772279437527917)
                    ·
                      refine ⟨4060192690789604789072969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827180508772279437527917 4060192690789604789072969)
                      ·
                        rfl

theorem cell23_7907197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_7907197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907197 prefixEnd_7907197 := by exact prefixLift 7907197
  have htrace : WordTrace (prefixWord ++ tailWord_7907197) baseStart_7907197 baseEnd_7907197 := by
    simpa [prefixWord, tailWord_7907197, baseEnd_7907197] using wordTrace_append hprefix tailTrace_7907197
  have hstable : (prefixWord ++ tailWord_7907197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907197).length < 2 ^ (prefixWord ++ tailWord_7907197).sum := by decide
  have hdescent : baseEnd_7907197 < baseStart_7907197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907198 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7907198 : Nat := 118140960795 + 7907198 * 2 ^ 59
def prefixEnd_7907198 : Nat := 4983230072969 + 3 ^ 40 * 7907198 * 2
def baseEnd_7907198 : Nat := 4060193204270259285160465

theorem tailTrace_7907198 : CollatzResearch.WordTrace tailWord_7907198 prefixEnd_7907198 4060193204270259285160465 := by
  unfold tailWord_7907198
  simp only [CollatzResearch.WordTrace]
  refine ⟨36049900500947445343667281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192266136005053041832892165 36049900500947445343667281)
  ·
    refine ⟨27037425375710584007750461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36049900500947445343667281 27037425375710584007750461)
    ·
      refine ⟨10139034515891469002906423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27037425375710584007750461 10139034515891469002906423)
      ·
        refine ⟨15208551773837203504359635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139034515891469002906423 15208551773837203504359635)
        ·
          refine ⟨22812827660755805256539453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208551773837203504359635 22812827660755805256539453)
          ·
            refine ⟨8554810372783426971202295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22812827660755805256539453 8554810372783426971202295)
            ·
              refine ⟨12832215559175140456803443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554810372783426971202295 12832215559175140456803443)
              ·
                refine ⟨19248323338762710685205165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12832215559175140456803443 19248323338762710685205165)
                ·
                  refine ⟨7218121252036016506951937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19248323338762710685205165 7218121252036016506951937)
                  ·
                    refine ⟨5413590939027012380213953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218121252036016506951937 5413590939027012380213953)
                    ·
                      refine ⟨4060193204270259285160465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413590939027012380213953 4060193204270259285160465)
                      ·
                        rfl

theorem cell23_7907198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7907198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907198 prefixEnd_7907198 := by exact prefixLift 7907198
  have htrace : WordTrace (prefixWord ++ tailWord_7907198) baseStart_7907198 baseEnd_7907198 := by
    simpa [prefixWord, tailWord_7907198, baseEnd_7907198] using wordTrace_append hprefix tailTrace_7907198
  have hstable : (prefixWord ++ tailWord_7907198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907198).length < 2 ^ (prefixWord ++ tailWord_7907198).sum := by decide
  have hdescent : baseEnd_7907198 < baseStart_7907198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907237 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_7907237 : Nat := 118140960795 + 7907237 * 2 ^ 59
def prefixEnd_7907237 : Nat := 4983230072969 + 3 ^ 40 * 7907237 * 2
def baseEnd_7907237 : Nat := 4060213230015784632572785

theorem tailTrace_7907237 : CollatzResearch.WordTrace tailWord_7907237 prefixEnd_7907237 4060213230015784632572785 := by
  unfold tailWord_7907237
  simp only [CollatzResearch.WordTrace]
  refine ⟨288400626454438272410007965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192267084302958848273338643 288400626454438272410007965)
  ·
    refine ⟨108150234920414352153752987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288400626454438272410007965 108150234920414352153752987)
    ·
      refine ⟨162225352380621528230629481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108150234920414352153752987 162225352380621528230629481)
      ·
        refine ⟨121669014285466146172972111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162225352380621528230629481 121669014285466146172972111)
        ·
          refine ⟨182503521428199219259458167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121669014285466146172972111 182503521428199219259458167)
          ·
            refine ⟨273755282142298828889187251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182503521428199219259458167 273755282142298828889187251)
            ·
              refine ⟨410632923213448243333780877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273755282142298828889187251 410632923213448243333780877)
              ·
                refine ⟨153987346205043091250167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410632923213448243333780877 153987346205043091250167829)
                ·
                  refine ⟨7218156853361394902351617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153987346205043091250167829 7218156853361394902351617)
                  ·
                    refine ⟨5413617640021046176763713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218156853361394902351617 5413617640021046176763713)
                    ·
                      refine ⟨4060213230015784632572785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413617640021046176763713 4060213230015784632572785)
                      ·
                        rfl

theorem cell23_7907237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_7907237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907237 prefixEnd_7907237 := by exact prefixLift 7907237
  have htrace : WordTrace (prefixWord ++ tailWord_7907237) baseStart_7907237 baseEnd_7907237 := by
    simpa [prefixWord, tailWord_7907237, baseEnd_7907237] using wordTrace_append hprefix tailTrace_7907237
  have hstable : (prefixWord ++ tailWord_7907237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907237).length < 2 ^ (prefixWord ++ tailWord_7907237).sum := by decide
  have hdescent : baseEnd_7907237 < baseStart_7907237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907273 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_7907273 : Nat := 118140960795 + 7907273 * 2 ^ 59
def prefixEnd_7907273 : Nat := 4983230072969 + 3 ^ 40 * 7907273 * 2
def baseEnd_7907273 : Nat := 1353410571773115497240873

theorem tailTrace_7907273 : CollatzResearch.WordTrace tailWord_7907273 prefixEnd_7907273 1353410571773115497240873 := by
  unfold tailWord_7907273
  simp only [CollatzResearch.WordTrace]
  refine ⟨288401939482307850558318473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192267959654871900372212315 288401939482307850558318473)
  ·
    refine ⟨216301454611730887918738855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288401939482307850558318473 216301454611730887918738855)
    ·
      refine ⟨324452181917596331878108283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216301454611730887918738855 324452181917596331878108283)
      ·
        refine ⟨486678272876394497817162425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324452181917596331878108283 486678272876394497817162425)
        ·
          refine ⟨365008704657295873362871819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486678272876394497817162425 365008704657295873362871819)
          ·
            refine ⟨547513056985943810044307729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365008704657295873362871819 547513056985943810044307729)
            ·
              refine ⟨410634792739457857533230797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547513056985943810044307729 410634792739457857533230797)
              ·
                refine ⟨153988047277296696574961549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410634792739457857533230797 153988047277296696574961549)
                ·
                  refine ⟨57745517728986261215610581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153988047277296696574961549 57745517728986261215610581)
                  ·
                    refine ⟨1353410571773115497240873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57745517728986261215610581 1353410571773115497240873)
                    ·
                      rfl

theorem cell23_7907273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_7907273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907273 prefixEnd_7907273 := by exact prefixLift 7907273
  have htrace : WordTrace (prefixWord ++ tailWord_7907273) baseStart_7907273 baseEnd_7907273 := by
    simpa [prefixWord, tailWord_7907273, baseEnd_7907273] using wordTrace_append hprefix tailTrace_7907273
  have hstable : (prefixWord ++ tailWord_7907273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907273).length < 2 ^ (prefixWord ++ tailWord_7907273).sum := by decide
  have hdescent : baseEnd_7907273 < baseStart_7907273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907283 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_7907283 : Nat := 118140960795 + 7907283 * 2 ^ 59
def prefixEnd_7907283 : Nat := 4983230072969 + 3 ^ 40 * 7907283 * 2
def baseEnd_7907283 : Nat := 4060236850125891452597573

theorem tailTrace_7907283 : CollatzResearch.WordTrace tailWord_7907283 prefixEnd_7907283 4060236850125891452597573 := by
  unfold tailWord_7907283
  simp only [CollatzResearch.WordTrace]
  refine ⟨288402304212271622266182503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192268202808181081510788335 288402304212271622266182503)
  ·
    refine ⟨432603456318407433399273755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288402304212271622266182503 432603456318407433399273755)
    ·
      refine ⟨648905184477611150098910633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432603456318407433399273755 648905184477611150098910633)
      ·
        refine ⟨486678888358208362574182975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648905184477611150098910633 486678888358208362574182975)
        ·
          refine ⟨730018332537312543861274463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486678888358208362574182975 730018332537312543861274463)
          ·
            refine ⟨1095027498805968815791911695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730018332537312543861274463 1095027498805968815791911695)
            ·
              refine ⟨1642541248208953223687867543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095027498805968815791911695 1642541248208953223687867543)
              ·
                refine ⟨2463811872313429835531801315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642541248208953223687867543 2463811872313429835531801315)
                ·
                  refine ⟨3695717808470144753297701973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463811872313429835531801315 3695717808470144753297701973)
                  ·
                    refine ⟨43309193068009508827707445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3695717808470144753297701973 43309193068009508827707445)
                    ·
                      refine ⟨4060236850125891452597573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43309193068009508827707445 4060236850125891452597573)
                      ·
                        rfl

theorem cell23_7907283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_7907283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907283 prefixEnd_7907283 := by exact prefixLift 7907283
  have htrace : WordTrace (prefixWord ++ tailWord_7907283) baseStart_7907283 baseEnd_7907283 := by
    simpa [prefixWord, tailWord_7907283, baseEnd_7907283] using wordTrace_append hprefix tailTrace_7907283
  have hstable : (prefixWord ++ tailWord_7907283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907283).length < 2 ^ (prefixWord ++ tailWord_7907283).sum := by decide
  have hdescent : baseEnd_7907283 < baseStart_7907283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907292 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7907292 : Nat := 118140960795 + 7907292 * 2 ^ 59
def prefixEnd_7907292 : Nat := 4983230072969 + 3 ^ 40 * 7907292 * 2
def baseEnd_7907292 : Nat := 4060241471451781917385033

theorem tailTrace_7907292 : CollatzResearch.WordTrace tailWord_7907292 prefixEnd_7907292 4060241471451781917385033 := by
  unfold tailWord_7907292
  simp only [CollatzResearch.WordTrace]
  refine ⟨144201316234619508401630065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192268421646159344535506753 144201316234619508401630065)
  ·
    refine ⟨108150987175964631301222549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144201316234619508401630065 108150987175964631301222549)
    ·
      refine ⟨5069577523873342092244807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108150987175964631301222549 5069577523873342092244807)
      ·
        refine ⟨7604366285810013138367211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069577523873342092244807 7604366285810013138367211)
        ·
          refine ⟨11406549428715019707550817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604366285810013138367211 11406549428715019707550817)
          ·
            refine ⟨8554912071536264780663113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11406549428715019707550817 8554912071536264780663113)
            ·
              refine ⟨6416184053652198585497335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554912071536264780663113 6416184053652198585497335)
              ·
                refine ⟨9624276080478297878246003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416184053652198585497335 9624276080478297878246003)
                ·
                  refine ⟨14436414120717446817369005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624276080478297878246003 14436414120717446817369005)
                  ·
                    refine ⟨5413655295269042556513377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14436414120717446817369005 5413655295269042556513377)
                    ·
                      refine ⟨4060241471451781917385033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413655295269042556513377 4060241471451781917385033)
                      ·
                        rfl

theorem cell23_7907292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7907292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907292 prefixEnd_7907292 := by exact prefixLift 7907292
  have htrace : WordTrace (prefixWord ++ tailWord_7907292) baseStart_7907292 baseEnd_7907292 := by
    simpa [prefixWord, tailWord_7907292, baseEnd_7907292] using wordTrace_append hprefix tailTrace_7907292
  have hstable : (prefixWord ++ tailWord_7907292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907292).length < 2 ^ (prefixWord ++ tailWord_7907292).sum := by decide
  have hdescent : baseEnd_7907292 < baseStart_7907292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907340 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_7907340 : Nat := 118140960795 + 7907340 * 2 ^ 59
def prefixEnd_7907340 : Nat := 4983230072969 + 3 ^ 40 * 7907340 * 2
def baseEnd_7907340 : Nat := 4060266118523197729584811

theorem tailTrace_7907340 : CollatzResearch.WordTrace tailWord_7907340 prefixEnd_7907340 4060266118523197729584811 := by
  unfold tailWord_7907340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144202191586532560500503737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192269588782043414000671649 144202191586532560500503737)
  ·
    refine ⟨108151643689899420375377803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144202191586532560500503737 108151643689899420375377803)
    ·
      refine ⟨162227465534849130563066705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108151643689899420375377803 162227465534849130563066705)
      ·
        refine ⟨121670599151136847922300029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162227465534849130563066705 121670599151136847922300029)
        ·
          refine ⟨45626474681676317970862511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121670599151136847922300029 45626474681676317970862511)
          ·
            refine ⟨68439712022514476956293767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45626474681676317970862511 68439712022514476956293767)
            ·
              refine ⟨102659568033771715434440651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68439712022514476956293767 102659568033771715434440651)
              ·
                refine ⟨153989352050657573151660977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102659568033771715434440651 153989352050657573151660977)
                ·
                  refine ⟨115492014037993179863745733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153989352050657573151660977 115492014037993179863745733)
                  ·
                    refine ⟨21654752632123721224452325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115492014037993179863745733 21654752632123721224452325)
                    ·
                      refine ⟨4060266118523197729584811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21654752632123721224452325 4060266118523197729584811)
                      ·
                        rfl

theorem cell23_7907340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_7907340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907340 prefixEnd_7907340 := by exact prefixLift 7907340
  have htrace : WordTrace (prefixWord ++ tailWord_7907340) baseStart_7907340 baseEnd_7907340 := by
    simpa [prefixWord, tailWord_7907340, baseEnd_7907340] using wordTrace_append hprefix tailTrace_7907340
  have hstable : (prefixWord ++ tailWord_7907340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907340).length < 2 ^ (prefixWord ++ tailWord_7907340).sum := by decide
  have hdescent : baseEnd_7907340 < baseStart_7907340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907404 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_7907404 : Nat := 118140960795 + 7907404 * 2 ^ 59
def prefixEnd_7907404 : Nat := 4983230072969 + 3 ^ 40 * 7907404 * 2
def baseEnd_7907404 : Nat := 4060298981285085479184517

theorem tailTrace_7907404 : CollatzResearch.WordTrace tailWord_7907404 prefixEnd_7907404 4060298981285085479184517 := by
  unfold tailWord_7907404
  simp only [CollatzResearch.WordTrace]
  refine ⟨144203358722416629965668633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192271144963222173287558177 144203358722416629965668633)
  ·
    refine ⟨108152519041812472474251475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144203358722416629965668633 108152519041812472474251475)
    ·
      refine ⟨162228778562718708711377213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108152519041812472474251475 162228778562718708711377213)
      ·
        refine ⟨60835791961019515766766455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162228778562718708711377213 60835791961019515766766455)
        ·
          refine ⟨91253687941529273650149683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60835791961019515766766455 91253687941529273650149683)
          ·
            refine ⟨136880531912293910475224525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91253687941529273650149683 136880531912293910475224525)
            ·
              refine ⟨51330199467110216428209197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136880531912293910475224525 51330199467110216428209197)
              ·
                refine ⟨19248824800166331160578449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51330199467110216428209197 19248824800166331160578449)
                ·
                  refine ⟨14436618600124748370433837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19248824800166331160578449 14436618600124748370433837)
                  ·
                    refine ⟨5413731975046780638912689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14436618600124748370433837 5413731975046780638912689)
                    ·
                      refine ⟨4060298981285085479184517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413731975046780638912689 4060298981285085479184517)
                      ·
                        rfl

theorem cell23_7907404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_7907404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907404 prefixEnd_7907404 := by exact prefixLift 7907404
  have htrace : WordTrace (prefixWord ++ tailWord_7907404) baseStart_7907404 baseEnd_7907404 := by
    simpa [prefixWord, tailWord_7907404, baseEnd_7907404] using wordTrace_append hprefix tailTrace_7907404
  have hstable : (prefixWord ++ tailWord_7907404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907404).length < 2 ^ (prefixWord ++ tailWord_7907404).sum := by decide
  have hdescent : baseEnd_7907404 < baseStart_7907404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907427 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 4, 4]
def baseStart_7907427 : Nat := 118140960795 + 7907427 * 2 ^ 59
def prefixEnd_7907427 : Nat := 4983230072969 + 3 ^ 40 * 7907427 * 2
def baseEnd_7907427 : Nat := 1353436930446712963065637

theorem tailTrace_7907427 : CollatzResearch.WordTrace tailWord_7907427 prefixEnd_7907427 1353436930446712963065637 := by
  unfold tailWord_7907427
  simp only [CollatzResearch.WordTrace]
  refine ⟨288407556323749934859424535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192271704215833289906283023 288407556323749934859424535)
  ·
    refine ⟨432611334485624902289136803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288407556323749934859424535 432611334485624902289136803)
    ·
      refine ⟨648917001728437353433705205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432611334485624902289136803 648917001728437353433705205)
      ·
        refine ⟨60835968912041001884409863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 648917001728437353433705205 60835968912041001884409863)
        ·
          refine ⟨91253953368061502826614795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60835968912041001884409863 91253953368061502826614795)
          ·
            refine ⟨136880930052092254239922193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91253953368061502826614795 136880930052092254239922193)
            ·
              refine ⟨102660697539069190679941645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136880930052092254239922193 102660697539069190679941645)
              ·
                refine ⟨38497761577150946504978117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102660697539069190679941645 38497761577150946504978117)
                ·
                  refine ⟨7218330295715802469683397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38497761577150946504978117 7218330295715802469683397)
                  ·
                    refine ⟨1353436930446712963065637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218330295715802469683397 1353436930446712963065637)
                    ·
                      rfl

theorem cell23_7907427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 4].length) (baseStart_7907427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907427 prefixEnd_7907427 := by exact prefixLift 7907427
  have htrace : WordTrace (prefixWord ++ tailWord_7907427) baseStart_7907427 baseEnd_7907427 := by
    simpa [prefixWord, tailWord_7907427, baseEnd_7907427] using wordTrace_append hprefix tailTrace_7907427
  have hstable : (prefixWord ++ tailWord_7907427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907427).length < 2 ^ (prefixWord ++ tailWord_7907427).sum := by decide
  have hdescent : baseEnd_7907427 < baseStart_7907427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907428 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_7907428 : Nat := 118140960795 + 7907428 * 2 ^ 59
def prefixEnd_7907428 : Nat := 4983230072969 + 3 ^ 40 * 7907428 * 2
def baseEnd_7907428 : Nat := 4060311304820793385284407

theorem tailTrace_7907428 : CollatzResearch.WordTrace tailWord_7907428 prefixEnd_7907428 4060311304820793385284407 := by
  unfold tailWord_7907428
  simp only [CollatzResearch.WordTrace]
  refine ⟨144203796398373156015105469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192271728531164208020140625 144203796398373156015105469)
  ·
    refine ⟨54076423649389933505664551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144203796398373156015105469 54076423649389933505664551)
    ·
      refine ⟨81114635474084900258496827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54076423649389933505664551 81114635474084900258496827)
      ·
        refine ⟨121671953211127350387745241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81114635474084900258496827 121671953211127350387745241)
        ·
          refine ⟨91253964908345512790808931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121671953211127350387745241 91253964908345512790808931)
          ·
            refine ⟨136880947362518269186213397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91253964908345512790808931 136880947362518269186213397)
            ·
              refine ⟨6416294407618043868103753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136880947362518269186213397 6416294407618043868103753)
              ·
                refine ⟨4812220805713532901077815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416294407618043868103753 4812220805713532901077815)
                ·
                  refine ⟨7218331208570299351616723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812220805713532901077815 7218331208570299351616723)
                  ·
                    refine ⟨10827496812855449027425085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218331208570299351616723 10827496812855449027425085)
                    ·
                      refine ⟨4060311304820793385284407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827496812855449027425085 4060311304820793385284407)
                      ·
                        rfl

theorem cell23_7907428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_7907428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907428 prefixEnd_7907428 := by exact prefixLift 7907428
  have htrace : WordTrace (prefixWord ++ tailWord_7907428) baseStart_7907428 baseEnd_7907428 := by
    simpa [prefixWord, tailWord_7907428, baseEnd_7907428] using wordTrace_append hprefix tailTrace_7907428
  have hstable : (prefixWord ++ tailWord_7907428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907428).length < 2 ^ (prefixWord ++ tailWord_7907428).sum := by decide
  have hdescent : baseEnd_7907428 < baseStart_7907428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907437 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7907437 : Nat := 118140960795 + 7907437 * 2 ^ 59
def prefixEnd_7907437 : Nat := 4983230072969 + 3 ^ 40 * 7907437 * 2
def baseEnd_7907437 : Nat := 4060315926146683850071865

theorem tailTrace_7907437 : CollatzResearch.WordTrace tailWord_7907437 prefixEnd_7907437 4060315926146683850071865 := by
  unfold tailWord_7907437
  simp only [CollatzResearch.WordTrace]
  refine ⟨288407921053713706567288565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192271947369142471044859043 288407921053713706567288565)
  ·
    refine ⟨27038242598785659990683303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288407921053713706567288565 27038242598785659990683303)
    ·
      refine ⟨40557363898178489986024955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27038242598785659990683303 40557363898178489986024955)
      ·
        refine ⟨60836045847267734979037433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40557363898178489986024955 60836045847267734979037433)
        ·
          refine ⟨45627034385450801234278075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60836045847267734979037433 45627034385450801234278075)
          ·
            refine ⟨68440551578176201851417113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45627034385450801234278075 68440551578176201851417113)
            ·
              refine ⟨51330413683632151388562835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68440551578176201851417113 51330413683632151388562835)
              ·
                refine ⟨76995620525448227082844253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51330413683632151388562835 76995620525448227082844253)
                ·
                  refine ⟨28873357697043085156066595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76995620525448227082844253 28873357697043085156066595)
                  ·
                    refine ⟨43310036545564627734099893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28873357697043085156066595 43310036545564627734099893)
                    ·
                      refine ⟨4060315926146683850071865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43310036545564627734099893 4060315926146683850071865)
                      ·
                        rfl

theorem cell23_7907437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7907437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907437 prefixEnd_7907437 := by exact prefixLift 7907437
  have htrace : WordTrace (prefixWord ++ tailWord_7907437) baseStart_7907437 baseEnd_7907437 := by
    simpa [prefixWord, tailWord_7907437, baseEnd_7907437] using wordTrace_append hprefix tailTrace_7907437
  have hstable : (prefixWord ++ tailWord_7907437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907437).length < 2 ^ (prefixWord ++ tailWord_7907437).sum := by decide
  have hdescent : baseEnd_7907437 < baseStart_7907437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907447 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_7907447 : Nat := 118140960795 + 7907447 * 2 ^ 59
def prefixEnd_7907447 : Nat := 4983230072969 + 3 ^ 40 * 7907447 * 2
def baseEnd_7907447 : Nat := 4060321060953228810946819

theorem tailTrace_7907447 : CollatzResearch.WordTrace tailWord_7907447 prefixEnd_7907447 4060321060953228810946819 := by
  unfold tailWord_7907447
  simp only [CollatzResearch.WordTrace]
  refine ⟨288408285783677478275152595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192272190522451652183435063 288408285783677478275152595)
  ·
    refine ⟨432612428675516217412728893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288408285783677478275152595 432612428675516217412728893)
    ·
      refine ⟨162229660753318581529773335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432612428675516217412728893 162229660753318581529773335)
      ·
        refine ⟨243344491129977872294660003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162229660753318581529773335 243344491129977872294660003)
        ·
          refine ⟨365016736694966808441990005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243344491129977872294660003 365016736694966808441990005)
          ·
            refine ⟨34220319065153138291436563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365016736694966808441990005 34220319065153138291436563)
            ·
              refine ⟨51330478597729707437154845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220319065153138291436563 51330478597729707437154845)
              ·
                refine ⟨19248929474148640288933067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51330478597729707437154845 19248929474148640288933067)
                ·
                  refine ⟨28873394211222960433399601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19248929474148640288933067 28873394211222960433399601)
                  ·
                    refine ⟨21655045658417220325049701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28873394211222960433399601 21655045658417220325049701)
                    ·
                      refine ⟨4060321060953228810946819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655045658417220325049701 4060321060953228810946819)
                      ·
                        rfl

theorem cell23_7907447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_7907447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907447 prefixEnd_7907447 := by exact prefixLift 7907447
  have htrace : WordTrace (prefixWord ++ tailWord_7907447) baseStart_7907447 baseEnd_7907447 := by
    simpa [prefixWord, tailWord_7907447, baseEnd_7907447] using wordTrace_append hprefix tailTrace_7907447
  have hstable : (prefixWord ++ tailWord_7907447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907447).length < 2 ^ (prefixWord ++ tailWord_7907447).sum := by decide
  have hdescent : baseEnd_7907447 < baseStart_7907447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907450 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7907450 : Nat := 118140960795 + 7907450 * 2 ^ 59
def prefixEnd_7907450 : Nat := 4983230072969 + 3 ^ 40 * 7907450 * 2
def baseEnd_7907450 : Nat := 4060322601395192299209305

theorem tailTrace_7907450 : CollatzResearch.WordTrace tailWord_7907450 prefixEnd_7907450 4060322601395192299209305 := by
  unfold tailWord_7907450
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102098800666652446877951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192272263468444406525007869 72102098800666652446877951)
  ·
    refine ⟨108153148200999978670316927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72102098800666652446877951 108153148200999978670316927)
    ·
      refine ⟨162229722301499968005475391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108153148200999978670316927 162229722301499968005475391)
      ·
        refine ⟨243344583452249952008213087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162229722301499968005475391 243344583452249952008213087)
        ·
          refine ⟨365016875178374928012319631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243344583452249952008213087 365016875178374928012319631)
          ·
            refine ⟨547525312767562392018479447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365016875178374928012319631 547525312767562392018479447)
            ·
              refine ⟨821287969151343588027719171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547525312767562392018479447 821287969151343588027719171)
              ·
                refine ⟨1231931953727015382041578757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821287969151343588027719171 1231931953727015382041578757)
                ·
                  refine ⟨230987241323815384132796017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231931953727015382041578757 230987241323815384132796017)
                  ·
                    refine ⟨173240430992861538099597013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230987241323815384132796017 173240430992861538099597013)
                    ·
                      refine ⟨4060322601395192299209305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173240430992861538099597013 4060322601395192299209305)
                      ·
                        rfl

theorem cell23_7907450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7907450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907450 prefixEnd_7907450 := by exact prefixLift 7907450
  have htrace : WordTrace (prefixWord ++ tailWord_7907450) baseStart_7907450 baseEnd_7907450 := by
    simpa [prefixWord, tailWord_7907450, baseEnd_7907450] using wordTrace_append hprefix tailTrace_7907450
  have hstable : (prefixWord ++ tailWord_7907450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907450).length < 2 ^ (prefixWord ++ tailWord_7907450).sum := by decide
  have hdescent : baseEnd_7907450 < baseStart_7907450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907464 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7907464 : Nat := 118140960795 + 7907464 * 2 ^ 59
def prefixEnd_7907464 : Nat := 4983230072969 + 3 ^ 40 * 7907464 * 2
def baseEnd_7907464 : Nat := 4060329790124355244434241

theorem tailTrace_7907464 : CollatzResearch.WordTrace tailWord_7907464 prefixEnd_7907464 4060329790124355244434241 := by
  unfold tailWord_7907464
  simp only [CollatzResearch.WordTrace]
  refine ⟨144204452912307945089260723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192272603883077260119014297 144204452912307945089260723)
  ·
    refine ⟨216306679368461917633891085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144204452912307945089260723 216306679368461917633891085)
    ·
      refine ⟨81115004763173219112709157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216306679368461917633891085 81115004763173219112709157)
      ·
        refine ⟨15209063393094978583632967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81115004763173219112709157 15209063393094978583632967)
        ·
          refine ⟨22813595089642467875449451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209063393094978583632967 22813595089642467875449451)
          ·
            refine ⟨34220392634463701813174177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813595089642467875449451 34220392634463701813174177)
            ·
              refine ⟨25665294475847776359880633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34220392634463701813174177 25665294475847776359880633)
              ·
                refine ⟨19248970856885832269910475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25665294475847776359880633 19248970856885832269910475)
                ·
                  refine ⟨28873456285328748404865713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19248970856885832269910475 28873456285328748404865713)
                  ·
                    refine ⟨21655092213996561303649285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28873456285328748404865713 21655092213996561303649285)
                    ·
                      refine ⟨4060329790124355244434241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655092213996561303649285 4060329790124355244434241)
                      ·
                        rfl

theorem cell23_7907464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7907464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907464 prefixEnd_7907464 := by exact prefixLift 7907464
  have htrace : WordTrace (prefixWord ++ tailWord_7907464) baseStart_7907464 baseEnd_7907464 := by
    simpa [prefixWord, tailWord_7907464, baseEnd_7907464] using wordTrace_append hprefix tailTrace_7907464
  have hstable : (prefixWord ++ tailWord_7907464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907464).length < 2 ^ (prefixWord ++ tailWord_7907464).sum := by decide
  have hdescent : baseEnd_7907464 < baseStart_7907464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907498 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7907498 : Nat := 118140960795 + 7907498 * 2 ^ 59
def prefixEnd_7907498 : Nat := 4983230072969 + 3 ^ 40 * 7907498 * 2
def baseEnd_7907498 : Nat := 4060347248466608111409085

theorem tailTrace_7907498 : CollatzResearch.WordTrace tailWord_7907498 prefixEnd_7907498 4060347248466608111409085 := by
  unfold tailWord_7907498
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102536476623178496314787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192273430604328475990172765 72102536476623178496314787)
  ·
    refine ⟨108153804714934767744472181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72102536476623178496314787 108153804714934767744472181)
    ·
      refine ⟨10139419192025134476044267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108153804714934767744472181 10139419192025134476044267)
      ·
        refine ⟨15209128788037701714066401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139419192025134476044267 15209128788037701714066401)
        ·
          refine ⟨11406846591028276285549801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15209128788037701714066401 11406846591028276285549801)
          ·
            refine ⟨8555134943271207214162351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11406846591028276285549801 8555134943271207214162351)
            ·
              refine ⟨12832702414906810821243527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555134943271207214162351 12832702414906810821243527)
              ·
                refine ⟨19249053622360216231865291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12832702414906810821243527 19249053622360216231865291)
                ·
                  refine ⟨28873580433540324347797937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249053622360216231865291 28873580433540324347797937)
                  ·
                    refine ⟨21655185325155243260848453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28873580433540324347797937 21655185325155243260848453)
                    ·
                      refine ⟨4060347248466608111409085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655185325155243260848453 4060347248466608111409085)
                      ·
                        rfl

theorem cell23_7907498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7907498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907498 prefixEnd_7907498 := by exact prefixLift 7907498
  have htrace : WordTrace (prefixWord ++ tailWord_7907498) baseStart_7907498 baseEnd_7907498 := by
    simpa [prefixWord, tailWord_7907498, baseEnd_7907498] using wordTrace_append hprefix tailTrace_7907498
  have hstable : (prefixWord ++ tailWord_7907498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907498).length < 2 ^ (prefixWord ++ tailWord_7907498).sum := by decide
  have hdescent : baseEnd_7907498 < baseStart_7907498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907501 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_7907501 : Nat := 118140960795 + 7907501 * 2 ^ 59
def prefixEnd_7907501 : Nat := 4983230072969 + 3 ^ 40 * 7907501 * 2
def baseEnd_7907501 : Nat := 4060348788908571599671571

theorem tailTrace_7907501 : CollatzResearch.WordTrace tailWord_7907501 prefixEnd_7907501 4060348788908571599671571 := by
  unfold tailWord_7907501
  simp only [CollatzResearch.WordTrace]
  refine ⟨288410255325481845497618357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192273503550321230331745571 288410255325481845497618357)
  ·
    refine ⟨27038461436763923015401721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288410255325481845497618357 27038461436763923015401721)
    ·
      refine ⟨20278846077572942261551291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27038461436763923015401721 20278846077572942261551291)
      ·
        refine ⟨30418269116359413392326937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278846077572942261551291 30418269116359413392326937)
        ·
          refine ⟨22813701837269560044245203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30418269116359413392326937 22813701837269560044245203)
          ·
            refine ⟨34220552755904340066367805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813701837269560044245203 34220552755904340066367805)
            ·
              refine ⟨12832707283464127524887927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34220552755904340066367805 12832707283464127524887927)
              ·
                refine ⟨19249060925196191287331891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12832707283464127524887927 19249060925196191287331891)
                ·
                  refine ⟨28873591387794286930997837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249060925196191287331891 28873591387794286930997837)
                  ·
                    refine ⟨10827596770422857599124189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28873591387794286930997837 10827596770422857599124189)
                    ·
                      refine ⟨4060348788908571599671571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827596770422857599124189 4060348788908571599671571)
                      ·
                        rfl

theorem cell23_7907501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_7907501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907501 prefixEnd_7907501 := by exact prefixLift 7907501
  have htrace : WordTrace (prefixWord ++ tailWord_7907501) baseStart_7907501 baseEnd_7907501 := by
    simpa [prefixWord, tailWord_7907501, baseEnd_7907501] using wordTrace_append hprefix tailTrace_7907501
  have hstable : (prefixWord ++ tailWord_7907501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907501).length < 2 ^ (prefixWord ++ tailWord_7907501).sum := by decide
  have hdescent : baseEnd_7907501 < baseStart_7907501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907508 : List Nat := [2, 5, 3, 1, 1, 1, 1, 9]
def baseStart_7907508 : Nat := 118140960795 + 7907508 * 2 ^ 59
def prefixEnd_7907508 : Nat := 4983230072969 + 3 ^ 40 * 7907508 * 2
def baseEnd_7907508 : Nat := 150383421602709373047557

theorem tailTrace_7907508 : CollatzResearch.WordTrace tailWord_7907508 prefixEnd_7907508 150383421602709373047557 := by
  unfold tailWord_7907508
  simp only [CollatzResearch.WordTrace]
  refine ⟨144205255318228242846561589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192273673757637657128748785 144205255318228242846561589)
  ·
    refine ⟨13519242686083897766865149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144205255318228242846561589 13519242686083897766865149)
    ·
      refine ⟨5069716007281461662574431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13519242686083897766865149 5069716007281461662574431)
      ·
        refine ⟨7604574010922192493861647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069716007281461662574431 7604574010922192493861647)
        ·
          refine ⟨11406861016383288740792471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604574010922192493861647 11406861016383288740792471)
          ·
            refine ⟨17110291524574933111188707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11406861016383288740792471 17110291524574933111188707)
            ·
              refine ⟨25665437286862399666783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17110291524574933111188707 25665437286862399666783061)
              ·
                refine ⟨150383421602709373047557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25665437286862399666783061 150383421602709373047557)
                ·
                  rfl

theorem cell23_7907508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 9].length) (baseStart_7907508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907508 prefixEnd_7907508 := by exact prefixLift 7907508
  have htrace : WordTrace (prefixWord ++ tailWord_7907508) baseStart_7907508 baseEnd_7907508 := by
    simpa [prefixWord, tailWord_7907508, baseEnd_7907508] using wordTrace_append hprefix tailTrace_7907508
  have hstable : (prefixWord ++ tailWord_7907508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907508).length < 2 ^ (prefixWord ++ tailWord_7907508).sum := by decide
  have hdescent : baseEnd_7907508 < baseStart_7907508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907511 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_7907511 : Nat := 118140960795 + 7907511 * 2 ^ 59
def prefixEnd_7907511 : Nat := 4983230072969 + 3 ^ 40 * 7907511 * 2
def baseEnd_7907511 : Nat := 4060353923715116560546525

theorem tailTrace_7907511 : CollatzResearch.WordTrace tailWord_7907511 prefixEnd_7907511 4060353923715116560546525 := by
  unfold tailWord_7907511
  simp only [CollatzResearch.WordTrace]
  refine ⟨288410620055445617205482387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192273746703630411470321591 288410620055445617205482387)
  ·
    refine ⟨432615930083168425808223581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288410620055445617205482387 432615930083168425808223581)
    ·
      refine ⟨162230973781188159678083843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432615930083168425808223581 162230973781188159678083843)
      ·
        refine ⟨243346460671782239517125765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162230973781188159678083843 243346460671782239517125765)
        ·
          refine ⟨45627461375959169909461081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243346460671782239517125765 45627461375959169909461081)
          ·
            refine ⟨34220596031969377432095811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45627461375959169909461081 34220596031969377432095811)
            ·
              refine ⟨51330894047954066148143717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220596031969377432095811 51330894047954066148143717)
              ·
                refine ⟨9624542633991387402776947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51330894047954066148143717 9624542633991387402776947)
                ·
                  refine ⟨14436813950987081104165421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624542633991387402776947 14436813950987081104165421)
                  ·
                    refine ⟨5413805231620155414062033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14436813950987081104165421 5413805231620155414062033)
                    ·
                      refine ⟨4060353923715116560546525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413805231620155414062033 4060353923715116560546525)
                      ·
                        rfl

theorem cell23_7907511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_7907511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907511 prefixEnd_7907511 := by exact prefixLift 7907511
  have htrace : WordTrace (prefixWord ++ tailWord_7907511) baseStart_7907511 baseEnd_7907511 := by
    simpa [prefixWord, tailWord_7907511, baseEnd_7907511] using wordTrace_append hprefix tailTrace_7907511
  have hstable : (prefixWord ++ tailWord_7907511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907511).length < 2 ^ (prefixWord ++ tailWord_7907511).sum := by decide
  have hdescent : baseEnd_7907511 < baseStart_7907511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907527 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_7907527 : Nat := 118140960795 + 7907527 * 2 ^ 59
def prefixEnd_7907527 : Nat := 4983230072969 + 3 ^ 40 * 7907527 * 2
def baseEnd_7907527 : Nat := 4060362139405588497946451

theorem tailTrace_7907527 : CollatzResearch.WordTrace tailWord_7907527 prefixEnd_7907527 4060362139405588497946451 := by
  unfold tailWord_7907527
  simp only [CollatzResearch.WordTrace]
  refine ⟨288411203623387651938064835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192274135748925101292043223 288411203623387651938064835)
  ·
    refine ⟨432616805435081477907097253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288411203623387651938064835 432616805435081477907097253)
    ·
      refine ⟨81115651019077777107580735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432616805435081477907097253 81115651019077777107580735)
      ·
        refine ⟨121673476528616665661371103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81115651019077777107580735 121673476528616665661371103)
        ·
          refine ⟨182510214792924998492056655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121673476528616665661371103 182510214792924998492056655)
          ·
            refine ⟨273765322189387497738084983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182510214792924998492056655 273765322189387497738084983)
            ·
              refine ⟨410647983284081246607127475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273765322189387497738084983 410647983284081246607127475)
              ·
                refine ⟨615971974926121869910691213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410647983284081246607127475 615971974926121869910691213)
                ·
                  refine ⟨230989490597295701216509205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615971974926121869910691213 230989490597295701216509205)
                  ·
                    refine ⟨10827632371748235994523869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230989490597295701216509205 10827632371748235994523869)
                    ·
                      refine ⟨4060362139405588497946451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827632371748235994523869 4060362139405588497946451)
                      ·
                        rfl

theorem cell23_7907527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_7907527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907527 prefixEnd_7907527 := by exact prefixLift 7907527
  have htrace : WordTrace (prefixWord ++ tailWord_7907527) baseStart_7907527 baseEnd_7907527 := by
    simpa [prefixWord, tailWord_7907527, baseEnd_7907527] using wordTrace_append hprefix tailTrace_7907527
  have hstable : (prefixWord ++ tailWord_7907527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907527).length < 2 ^ (prefixWord ++ tailWord_7907527).sum := by decide
  have hdescent : baseEnd_7907527 < baseStart_7907527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907537 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_7907537 : Nat := 118140960795 + 7907537 * 2 ^ 59
def prefixEnd_7907537 : Nat := 4983230072969 + 3 ^ 40 * 7907537 * 2
def baseEnd_7907537 : Nat := 4060367274212133458821405

theorem tailTrace_7907537 : CollatzResearch.WordTrace tailWord_7907537 prefixEnd_7907537 4060367274212133458821405 := by
  unfold tailWord_7907537
  simp only [CollatzResearch.WordTrace]
  refine ⟨288411568353351423645928865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192274378902234282430619243 288411568353351423645928865)
  ·
    refine ⟨216308676265013567734446649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288411568353351423645928865 216308676265013567734446649)
    ·
      refine ⟨162231507198760175800834987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216308676265013567734446649 162231507198760175800834987)
      ·
        refine ⟨243347260798140263701252481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162231507198760175800834987 243347260798140263701252481)
        ·
          refine ⟨182510445598605197775939361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243347260798140263701252481 182510445598605197775939361)
          ·
            refine ⟨136882834198953898331954521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182510445598605197775939361 136882834198953898331954521)
            ·
              refine ⟨102662125649215423748965891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136882834198953898331954521 102662125649215423748965891)
              ·
                refine ⟨153993188473823135623448837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102662125649215423748965891 153993188473823135623448837)
                ·
                  refine ⟨28873722838841837929396657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153993188473823135623448837 28873722838841837929396657)
                  ·
                    refine ⟨21655292129131378447047493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28873722838841837929396657 21655292129131378447047493)
                    ·
                      refine ⟨4060367274212133458821405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655292129131378447047493 4060367274212133458821405)
                      ·
                        rfl

theorem cell23_7907537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_7907537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907537 prefixEnd_7907537 := by exact prefixLift 7907537
  have htrace : WordTrace (prefixWord ++ tailWord_7907537) baseStart_7907537 baseEnd_7907537 := by
    simpa [prefixWord, tailWord_7907537, baseEnd_7907537] using wordTrace_append hprefix tailTrace_7907537
  have hstable : (prefixWord ++ tailWord_7907537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907537).length < 2 ^ (prefixWord ++ tailWord_7907537).sum := by decide
  have hdescent : baseEnd_7907537 < baseStart_7907537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907587 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_7907587 : Nat := 118140960795 + 7907587 * 2 ^ 59
def prefixEnd_7907587 : Nat := 4983230072969 + 3 ^ 40 * 7907587 * 2
def baseEnd_7907587 : Nat := 4060392948244858263196175

theorem tailTrace_7907587 : CollatzResearch.WordTrace tailWord_7907587 prefixEnd_7907587 4060392948244858263196175 := by
  unfold tailWord_7907587
  simp only [CollatzResearch.WordTrace]
  refine ⟨288413392003170282185249015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192275594668780188123499343 288413392003170282185249015)
  ·
    refine ⟨432620088004755423277873523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288413392003170282185249015 432620088004755423277873523)
    ·
      refine ⟨648930132007133134916810285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432620088004755423277873523 648930132007133134916810285)
      ·
        refine ⟨243348799502674925593803857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648930132007133134916810285 243348799502674925593803857)
        ·
          refine ⟨182511599627006194195352893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243348799502674925593803857 182511599627006194195352893)
          ·
            refine ⟨68441849860127322823257335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182511599627006194195352893 68441849860127322823257335)
            ·
              refine ⟨102662774790190984234886003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68441849860127322823257335 102662774790190984234886003)
              ·
                refine ⟨153994162185286476352329005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102662774790190984234886003 153994162185286476352329005)
                ·
                  refine ⟨57747810819482428632123377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153994162185286476352329005 57747810819482428632123377)
                  ·
                    refine ⟨43310858114611821474092533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57747810819482428632123377 43310858114611821474092533)
                    ·
                      refine ⟨4060392948244858263196175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43310858114611821474092533 4060392948244858263196175)
                      ·
                        rfl

theorem cell23_7907587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_7907587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907587 prefixEnd_7907587 := by exact prefixLift 7907587
  have htrace : WordTrace (prefixWord ++ tailWord_7907587) baseStart_7907587 baseEnd_7907587 := by
    simpa [prefixWord, tailWord_7907587, baseEnd_7907587] using wordTrace_append hprefix tailTrace_7907587
  have hstable : (prefixWord ++ tailWord_7907587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907587).length < 2 ^ (prefixWord ++ tailWord_7907587).sum := by decide
  have hdescent : baseEnd_7907587 < baseStart_7907587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907594 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_7907594 : Nat := 118140960795 + 7907594 * 2 ^ 59
def prefixEnd_7907594 : Nat := 4983230072969 + 3 ^ 40 * 7907594 * 2
def baseEnd_7907594 : Nat := 1353465514203146578602881

theorem tailTrace_7907594 : CollatzResearch.WordTrace tailWord_7907594 prefixEnd_7907594 1353465514203146578602881 := by
  unfold tailWord_7907594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72103411828536230595188459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192275764876096614920502557 72103411828536230595188459)
  ·
    refine ⟨108155117742804345892782689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72103411828536230595188459 108155117742804345892782689)
    ·
      refine ⟨81116338307103259419587017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108155117742804345892782689 81116338307103259419587017)
      ·
        refine ⟨60837253730327444564690263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81116338307103259419587017 60837253730327444564690263)
        ·
          refine ⟨91255880595491166847035395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60837253730327444564690263 91255880595491166847035395)
          ·
            refine ⟨136883820893236750270553093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91255880595491166847035395 136883820893236750270553093)
            ·
              refine ⟨25665716417481890675728705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136883820893236750270553093 25665716417481890675728705)
              ·
                refine ⟨19249287313111418006796529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25665716417481890675728705 19249287313111418006796529)
                ·
                  refine ⟨14436965484833563505097397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19249287313111418006796529 14436965484833563505097397)
                  ·
                    refine ⟨1353465514203146578602881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14436965484833563505097397 1353465514203146578602881)
                    ·
                      rfl

theorem cell23_7907594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_7907594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907594 prefixEnd_7907594 := by exact prefixLift 7907594
  have htrace : WordTrace (prefixWord ++ tailWord_7907594) baseStart_7907594 baseEnd_7907594 := by
    simpa [prefixWord, tailWord_7907594, baseEnd_7907594] using wordTrace_append hprefix tailTrace_7907594
  have hstable : (prefixWord ++ tailWord_7907594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907594).length < 2 ^ (prefixWord ++ tailWord_7907594).sum := by decide
  have hdescent : baseEnd_7907594 < baseStart_7907594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907667 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 9]
def baseStart_7907667 : Nat := 118140960795 + 7907667 * 2 ^ 59
def prefixEnd_7907667 : Nat := 4983230072969 + 3 ^ 40 * 7907667 * 2
def baseEnd_7907667 : Nat := 1353478008899072650065269

theorem tailTrace_7907667 : CollatzResearch.WordTrace tailWord_7907667 prefixEnd_7907667 1353478008899072650065269 := by
  unfold tailWord_7907667
  simp only [CollatzResearch.WordTrace]
  refine ⟨288416309842880455848161255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192277539895253637232107503 288416309842880455848161255)
  ·
    refine ⟨432624464764320683772241883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288416309842880455848161255 432624464764320683772241883)
    ·
      refine ⟨648936697146481025658362825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432624464764320683772241883 648936697146481025658362825)
      ·
        refine ⟨486702522859860769243772119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648936697146481025658362825 486702522859860769243772119)
        ·
          refine ⟨730053784289791153865658179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486702522859860769243772119 730053784289791153865658179)
          ·
            refine ⟨1095080676434686730798487269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730053784289791153865658179 1095080676434686730798487269)
            ·
              refine ⟨205327626831503762024716363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1095080676434686730798487269 205327626831503762024716363)
              ·
                refine ⟨307991440247255643037074545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205327626831503762024716363 307991440247255643037074545)
                ·
                  refine ⟨230993580185441732277805909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307991440247255643037074545 230993580185441732277805909)
                  ·
                    refine ⟨1353478008899072650065269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230993580185441732277805909 1353478008899072650065269)
                    ·
                      rfl

theorem cell23_7907667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_7907667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907667 prefixEnd_7907667 := by exact prefixLift 7907667
  have htrace : WordTrace (prefixWord ++ tailWord_7907667) baseStart_7907667 baseEnd_7907667 := by
    simpa [prefixWord, tailWord_7907667, baseEnd_7907667] using wordTrace_append hprefix tailTrace_7907667
  have hstable : (prefixWord ++ tailWord_7907667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907667).length < 2 ^ (prefixWord ++ tailWord_7907667).sum := by decide
  have hdescent : baseEnd_7907667 < baseStart_7907667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907671 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 6]
def baseStart_7907671 : Nat := 118140960795 + 7907671 * 2 ^ 59
def prefixEnd_7907671 : Nat := 4983230072969 + 3 ^ 40 * 7907671 * 2
def baseEnd_7907671 : Nat := 451159564513315103838421

theorem tailTrace_7907671 : CollatzResearch.WordTrace tailWord_7907671 prefixEnd_7907671 451159564513315103838421 := by
  unfold tailWord_7907671
  simp only [CollatzResearch.WordTrace]
  refine ⟨288416455734865964531306867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192277637156577309687537911 288416455734865964531306867)
  ·
    refine ⟨432624683602298946796960301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288416455734865964531306867 432624683602298946796960301)
    ·
      refine ⟨162234256350862105048860113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432624683602298946796960301 162234256350862105048860113)
      ·
        refine ⟨121675692263146578786645085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162234256350862105048860113 121675692263146578786645085)
        ·
          refine ⟨45628384598679967044991907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121675692263146578786645085 45628384598679967044991907)
          ·
            refine ⟨68442576898019950567487861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45628384598679967044991907 68442576898019950567487861)
            ·
              refine ⟨6416491584189370365701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68442576898019950567487861 6416491584189370365701987)
              ·
                refine ⟨9624737376284055548552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416491584189370365701987 9624737376284055548552981)
                ·
                  refine ⟨451159564513315103838421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9624737376284055548552981 451159564513315103838421)
                  ·
                    rfl

theorem cell23_7907671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 6].length) (baseStart_7907671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907671 prefixEnd_7907671 := by exact prefixLift 7907671
  have htrace : WordTrace (prefixWord ++ tailWord_7907671) baseStart_7907671 baseEnd_7907671 := by
    simpa [prefixWord, tailWord_7907671, baseEnd_7907671] using wordTrace_append hprefix tailTrace_7907671
  have hstable : (prefixWord ++ tailWord_7907671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907671).length < 2 ^ (prefixWord ++ tailWord_7907671).sum := by decide
  have hdescent : baseEnd_7907671 < baseStart_7907671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907692 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_7907692 : Nat := 118140960795 + 7907692 * 2 ^ 59
def prefixEnd_7907692 : Nat := 4983230072969 + 3 ^ 40 * 7907692 * 2
def baseEnd_7907692 : Nat := 1353482287904526784127731

theorem tailTrace_7907692 : CollatzResearch.WordTrace tailWord_7907692 prefixEnd_7907692 1353482287904526784127731 := by
  unfold tailWord_7907692
  simp only [CollatzResearch.WordTrace]
  refine ⟨144208610833894942558910665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192278147778526590078547553 144208610833894942558910665)
  ·
    refine ⟨108156458125421206919182999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144208610833894942558910665 108156458125421206919182999)
    ·
      refine ⟨162234687188131810378774499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108156458125421206919182999 162234687188131810378774499)
      ·
        refine ⟨243352030782197715568161749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162234687188131810378774499 243352030782197715568161749)
        ·
          refine ⟨5703563221457758958628791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243352030782197715568161749 5703563221457758958628791)
          ·
            refine ⟨8555344832186638437943187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703563221457758958628791 8555344832186638437943187)
            ·
              refine ⟨12833017248279957656914781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555344832186638437943187 12833017248279957656914781)
              ·
                refine ⟨4812381468104984121343043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12833017248279957656914781 4812381468104984121343043)
                ·
                  refine ⟨7218572202157476182014565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812381468104984121343043 7218572202157476182014565)
                  ·
                    refine ⟨1353482287904526784127731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218572202157476182014565 1353482287904526784127731)
                    ·
                      rfl

theorem cell23_7907692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_7907692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907692 prefixEnd_7907692 := by exact prefixLift 7907692
  have htrace : WordTrace (prefixWord ++ tailWord_7907692) baseStart_7907692 baseEnd_7907692 := by
    simpa [prefixWord, tailWord_7907692, baseEnd_7907692] using wordTrace_append hprefix tailTrace_7907692
  have hstable : (prefixWord ++ tailWord_7907692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907692).length < 2 ^ (prefixWord ++ tailWord_7907692).sum := by decide
  have hdescent : baseEnd_7907692 < baseStart_7907692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907715 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 3]
def baseStart_7907715 : Nat := 118140960795 + 7907715 * 2 ^ 59
def prefixEnd_7907715 : Nat := 4983230072969 + 3 ^ 40 * 7907715 * 2
def baseEnd_7907715 : Nat := 4060458673768633762395587

theorem tailTrace_7907715 : CollatzResearch.WordTrace tailWord_7907715 prefixEnd_7907715 4060458673768633762395587 := by
  unfold tailWord_7907715
  simp only [CollatzResearch.WordTrace]
  refine ⟨288418060546706560045908599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192278707031137706697272399 288418060546706560045908599)
  ·
    refine ⟨432627090820059840068862899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288418060546706560045908599 432627090820059840068862899)
    ·
      refine ⟨648940636230089760103294349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432627090820059840068862899 648940636230089760103294349)
      ·
        refine ⟨243352738586283660038735381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648940636230089760103294349 243352738586283660038735381)
        ·
          refine ⟨11407159621232046564315721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243352738586283660038735381 11407159621232046564315721)
          ·
            refine ⟨8555369715924034923236791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11407159621232046564315721 8555369715924034923236791)
            ·
              refine ⟨12833054573886052384855187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555369715924034923236791 12833054573886052384855187)
              ·
                refine ⟨19249581860829078577282781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833054573886052384855187 19249581860829078577282781)
                ·
                  refine ⟨7218593197810904466481043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19249581860829078577282781 7218593197810904466481043)
                  ·
                    refine ⟨10827889796716356699721565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218593197810904466481043 10827889796716356699721565)
                    ·
                      refine ⟨4060458673768633762395587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10827889796716356699721565 4060458673768633762395587)
                      ·
                        rfl

theorem cell23_7907715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_7907715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907715 prefixEnd_7907715 := by exact prefixLift 7907715
  have htrace : WordTrace (prefixWord ++ tailWord_7907715) baseStart_7907715 baseEnd_7907715 := by
    simpa [prefixWord, tailWord_7907715, baseEnd_7907715] using wordTrace_append hprefix tailTrace_7907715
  have hstable : (prefixWord ++ tailWord_7907715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907715).length < 2 ^ (prefixWord ++ tailWord_7907715).sum := by decide
  have hdescent : baseEnd_7907715 < baseStart_7907715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907722 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_7907722 : Nat := 118140960795 + 7907722 * 2 ^ 59
def prefixEnd_7907722 : Nat := 4983230072969 + 3 ^ 40 * 7907722 * 2
def baseEnd_7907722 : Nat := 451162474237023915000895

theorem tailTrace_7907722 : CollatzResearch.WordTrace tailWord_7907722 prefixEnd_7907722 451162474237023915000895 := by
  unfold tailWord_7907722
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104578964420300060353355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192278877238454133494275613 72104578964420300060353355)
  ·
    refine ⟨108156868446630450090530033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72104578964420300060353355 108156868446630450090530033)
    ·
      refine ⟨81117651334972837567897525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108156868446630450090530033 81117651334972837567897525)
      ·
        refine ⟨7604779812653703521990393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81117651334972837567897525 7604779812653703521990393)
        ·
          refine ⟨5703584859490277641492795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7604779812653703521990393 5703584859490277641492795)
          ·
            refine ⟨8555377289235416462239193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703584859490277641492795 8555377289235416462239193)
            ·
              refine ⟨6416532966926562346679395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555377289235416462239193 6416532966926562346679395)
              ·
                refine ⟨9624799450389843520019093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416532966926562346679395 9624799450389843520019093)
                ·
                  refine ⟨451162474237023915000895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9624799450389843520019093 451162474237023915000895)
                  ·
                    rfl

theorem cell23_7907722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_7907722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907722 prefixEnd_7907722 := by exact prefixLift 7907722
  have htrace : WordTrace (prefixWord ++ tailWord_7907722) baseStart_7907722 baseEnd_7907722 := by
    simpa [prefixWord, tailWord_7907722, baseEnd_7907722] using wordTrace_append hprefix tailTrace_7907722
  have hstable : (prefixWord ++ tailWord_7907722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907722).length < 2 ^ (prefixWord ++ tailWord_7907722).sum := by decide
  have hdescent : baseEnd_7907722 < baseStart_7907722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907738 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7907738 : Nat := 118140960795 + 7907738 * 2 ^ 59
def prefixEnd_7907738 : Nat := 4983230072969 + 3 ^ 40 * 7907738 * 2
def baseEnd_7907738 : Nat := 4060470483823687172407981

theorem tailTrace_7907738 : CollatzResearch.WordTrace tailWord_7907738 prefixEnd_7907738 4060470483823687172407981 := by
  unfold tailWord_7907738
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104724856405808743498967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192279266283748823315997245 72104724856405808743498967)
  ·
    refine ⟨108157087284608713115248451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72104724856405808743498967 108157087284608713115248451)
    ·
      refine ⟨162235630926913069672872677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108157087284608713115248451 162235630926913069672872677)
      ·
        refine ⟨30419180798796200563663627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162235630926913069672872677 30419180798796200563663627)
        ·
          refine ⟨45628771198194300845495441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30419180798796200563663627 45628771198194300845495441)
          ·
            refine ⟨34221578398645725634121581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45628771198194300845495441 34221578398645725634121581)
            ·
              refine ⟨12833091899492147112795593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34221578398645725634121581 12833091899492147112795593)
              ·
                refine ⟨9624818924619110334596695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833091899492147112795593 9624818924619110334596695)
                ·
                  refine ⟨14437228386928665501895043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624818924619110334596695 14437228386928665501895043)
                  ·
                    refine ⟨21655842580392998252842565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14437228386928665501895043 21655842580392998252842565)
                    ·
                      refine ⟨4060470483823687172407981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655842580392998252842565 4060470483823687172407981)
                      ·
                        rfl

theorem cell23_7907738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7907738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907738 prefixEnd_7907738 := by exact prefixLift 7907738
  have htrace : WordTrace (prefixWord ++ tailWord_7907738) baseStart_7907738 baseEnd_7907738 := by
    simpa [prefixWord, tailWord_7907738, baseEnd_7907738] using wordTrace_append hprefix tailTrace_7907738
  have hstable : (prefixWord ++ tailWord_7907738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907738).length < 2 ^ (prefixWord ++ tailWord_7907738).sum := by decide
  have hdescent : baseEnd_7907738 < baseStart_7907738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907742 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7907742 : Nat := 118140960795 + 7907742 * 2 ^ 59
def prefixEnd_7907742 : Nat := 4983230072969 + 3 ^ 40 * 7907742 * 2
def baseEnd_7907742 : Nat := 4060472537746305156757963

theorem tailTrace_7907742 : CollatzResearch.WordTrace tailWord_7907742 prefixEnd_7907742 4060472537746305156757963 := by
  unfold tailWord_7907742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052380664701092957142685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192279363545072495771427653 36052380664701092957142685)
  ·
    refine ⟨13519642749262909858928507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36052380664701092957142685 13519642749262909858928507)
    ·
      refine ⟨20279464123894364788392761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13519642749262909858928507 20279464123894364788392761)
      ·
        refine ⟨15209598092920773591294571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20279464123894364788392761 15209598092920773591294571)
        ·
          refine ⟨22814397139381160386941857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209598092920773591294571 22814397139381160386941857)
          ·
            refine ⟨17110797854535870290206393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22814397139381160386941857 17110797854535870290206393)
            ·
              refine ⟨12833098390901902717654795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110797854535870290206393 12833098390901902717654795)
              ·
                refine ⟨19249647586352854076482193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833098390901902717654795 19249647586352854076482193)
                ·
                  refine ⟨14437235689764640557361645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19249647586352854076482193 14437235689764640557361645)
                  ·
                    refine ⟨5413963383661740209010617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14437235689764640557361645 5413963383661740209010617)
                    ·
                      refine ⟨4060472537746305156757963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413963383661740209010617 4060472537746305156757963)
                      ·
                        rfl

theorem cell23_7907742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7907742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907742 prefixEnd_7907742 := by exact prefixLift 7907742
  have htrace : WordTrace (prefixWord ++ tailWord_7907742) baseStart_7907742 baseEnd_7907742 := by
    simpa [prefixWord, tailWord_7907742, baseEnd_7907742] using wordTrace_append hprefix tailTrace_7907742
  have hstable : (prefixWord ++ tailWord_7907742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907742).length < 2 ^ (prefixWord ++ tailWord_7907742).sum := by decide
  have hdescent : baseEnd_7907742 < baseStart_7907742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907744 : List Nat := [2, 1, 1, 4, 1, 3, 2, 9]
def baseStart_7907744 : Nat := 118140960795 + 7907744 * 2 ^ 59
def prefixEnd_7907744 : Nat := 4983230072969 + 3 ^ 40 * 7907744 * 2
def baseEnd_7907744 : Nat := 150387909803985709219739

theorem tailTrace_7907744 : CollatzResearch.WordTrace tailWord_7907744 prefixEnd_7907744 150387909803985709219739 := by
  unfold tailWord_7907744
  simp only [CollatzResearch.WordTrace]
  refine ⟨144209559131800748999357143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192279412175734331999142857 144209559131800748999357143)
  ·
    refine ⟨216314338697701123499035715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144209559131800748999357143 216314338697701123499035715)
    ·
      refine ⟨324471508046551685248553573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216314338697701123499035715 324471508046551685248553573)
      ·
        refine ⟨60838407758728440984103795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324471508046551685248553573 60838407758728440984103795)
        ·
          refine ⟨91257611638092661476155693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60838407758728440984103795 91257611638092661476155693)
          ·
            refine ⟨34221604364284748053558385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91257611638092661476155693 34221604364284748053558385)
            ·
              refine ⟨25666203273213561040168789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34221604364284748053558385 25666203273213561040168789)
              ·
                refine ⟨150387909803985709219739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25666203273213561040168789 150387909803985709219739)
                ·
                  rfl

theorem cell23_7907744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_7907744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907744 prefixEnd_7907744 := by exact prefixLift 7907744
  have htrace : WordTrace (prefixWord ++ tailWord_7907744) baseStart_7907744 baseEnd_7907744 := by
    simpa [prefixWord, tailWord_7907744, baseEnd_7907744] using wordTrace_append hprefix tailTrace_7907744
  have hstable : (prefixWord ++ tailWord_7907744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907744).length < 2 ^ (prefixWord ++ tailWord_7907744).sum := by decide
  have hdescent : baseEnd_7907744 < baseStart_7907744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907751 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7907751 : Nat := 118140960795 + 7907751 * 2 ^ 59
def prefixEnd_7907751 : Nat := 4983230072969 + 3 ^ 40 * 7907751 * 2
def baseEnd_7907751 : Nat := 4060477159072195621545421

theorem tailTrace_7907751 : CollatzResearch.WordTrace tailWord_7907751 prefixEnd_7907751 4060477159072195621545421 := by
  unfold tailWord_7907751
  simp only [CollatzResearch.WordTrace]
  refine ⟨288419373574576138194219107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192279582383050758796146071 288419373574576138194219107)
  ·
    refine ⟨432629060361864207291328661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288419373574576138194219107 432629060361864207291328661)
    ·
      refine ⟨20279487204462384716781031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432629060361864207291328661 20279487204462384716781031)
      ·
        refine ⟨30419230806693577075171547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20279487204462384716781031 30419230806693577075171547)
        ·
          refine ⟨45628846210040365612757321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30419230806693577075171547 45628846210040365612757321)
          ·
            refine ⟨34221634657530274209567991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45628846210040365612757321 34221634657530274209567991)
            ·
              refine ⟨51332451986295411314351987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34221634657530274209567991 51332451986295411314351987)
              ·
                refine ⟨76998677979443116971527981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51332451986295411314351987 76998677979443116971527981)
                ·
                  refine ⟨28874504242291168864322993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76998677979443116971527981 28874504242291168864322993)
                  ·
                    refine ⟨21655878181718376648242245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28874504242291168864322993 21655878181718376648242245)
                    ·
                      refine ⟨4060477159072195621545421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21655878181718376648242245 4060477159072195621545421)
                      ·
                        rfl

theorem cell23_7907751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7907751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907751 prefixEnd_7907751 := by exact prefixLift 7907751
  have htrace : WordTrace (prefixWord ++ tailWord_7907751) baseStart_7907751 baseEnd_7907751 := by
    simpa [prefixWord, tailWord_7907751, baseEnd_7907751] using wordTrace_append hprefix tailTrace_7907751
  have hstable : (prefixWord ++ tailWord_7907751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907751).length < 2 ^ (prefixWord ++ tailWord_7907751).sum := by decide
  have hdescent : baseEnd_7907751 < baseStart_7907751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907765 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7907765 : Nat := 118140960795 + 7907765 * 2 ^ 59
def prefixEnd_7907765 : Nat := 4983230072969 + 3 ^ 40 * 7907765 * 2
def baseEnd_7907765 : Nat := 1353494782600452855590119

theorem tailTrace_7907765 : CollatzResearch.WordTrace tailWord_7907765 prefixEnd_7907765 1353494782600452855590119 := by
  unfold tailWord_7907765
  simp only [CollatzResearch.WordTrace]
  refine ⟨288419884196525418585228749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192279922797683612390152499 288419884196525418585228749)
  ·
    refine ⟨108157456573697031969460781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288419884196525418585228749 108157456573697031969460781)
    ·
      refine ⟨40559046215136386988547793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108157456573697031969460781 40559046215136386988547793)
      ·
        refine ⟨30419284661352290241410845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40559046215136386988547793 30419284661352290241410845)
        ·
          refine ⟨11407231748007108840529067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30419284661352290241410845 11407231748007108840529067)
          ·
            refine ⟨17110847622010663260793601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407231748007108840529067 17110847622010663260793601)
            ·
              refine ⟨12833135716507997445595201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110847622010663260793601 12833135716507997445595201)
              ·
                refine ⟨9624851787380998084196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833135716507997445595201 9624851787380998084196401)
                ·
                  refine ⟨7218638840535748563147301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624851787380998084196401 7218638840535748563147301)
                  ·
                    refine ⟨1353494782600452855590119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218638840535748563147301 1353494782600452855590119)
                    ·
                      rfl

theorem cell23_7907765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7907765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907765 prefixEnd_7907765 := by exact prefixLift 7907765
  have htrace : WordTrace (prefixWord ++ tailWord_7907765) baseStart_7907765 baseEnd_7907765 := by
    simpa [prefixWord, tailWord_7907765, baseEnd_7907765] using wordTrace_append hprefix tailTrace_7907765
  have hstable : (prefixWord ++ tailWord_7907765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907765).length < 2 ^ (prefixWord ++ tailWord_7907765).sum := by decide
  have hdescent : baseEnd_7907765 < baseStart_7907765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907815 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7907815 : Nat := 118140960795 + 7907815 * 2 ^ 59
def prefixEnd_7907815 : Nat := 4983230072969 + 3 ^ 40 * 7907815 * 2
def baseEnd_7907815 : Nat := 4060510021834083371145127

theorem tailTrace_7907815 : CollatzResearch.WordTrace tailWord_7907815 prefixEnd_7907815 4060510021834083371145127 := by
  unfold tailWord_7907815
  simp only [CollatzResearch.WordTrace]
  refine ⟨288421707846344277124548899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192281138564229518083032599 288421707846344277124548899)
  ·
    refine ⟨432632561769516415686823349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288421707846344277124548899 432632561769516415686823349)
    ·
      refine ⟨40559302665892163970639689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432632561769516415686823349 40559302665892163970639689)
      ·
        refine ⟨30419476999419122977979767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40559302665892163970639689 30419476999419122977979767)
        ·
          refine ⟨45629215499128684466969651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30419476999419122977979767 45629215499128684466969651)
          ·
            refine ⟨68443823248693026700454477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45629215499128684466969651 68443823248693026700454477)
            ·
              refine ⟨25666433718259885012670429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68443823248693026700454477 25666433718259885012670429)
              ·
                refine ⟨9624912644347456879751411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25666433718259885012670429 9624912644347456879751411)
                ·
                  refine ⟨14437368966521185319627117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624912644347456879751411 14437368966521185319627117)
                  ·
                    refine ⟨5414013362445444494860169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14437368966521185319627117 5414013362445444494860169)
                    ·
                      refine ⟨4060510021834083371145127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414013362445444494860169 4060510021834083371145127)
                      ·
                        rfl

theorem cell23_7907815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7907815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907815 prefixEnd_7907815 := by exact prefixLift 7907815
  have htrace : WordTrace (prefixWord ++ tailWord_7907815) baseStart_7907815 baseEnd_7907815 := by
    simpa [prefixWord, tailWord_7907815, baseEnd_7907815] using wordTrace_append hprefix tailTrace_7907815
  have hstable : (prefixWord ++ tailWord_7907815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907815).length < 2 ^ (prefixWord ++ tailWord_7907815).sum := by decide
  have hdescent : baseEnd_7907815 < baseStart_7907815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907822 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_7907822 : Nat := 118140960795 + 7907822 * 2 ^ 59
def prefixEnd_7907822 : Nat := 4983230072969 + 3 ^ 40 * 7907822 * 2
def baseEnd_7907822 : Nat := 4060513616198664843757595

theorem tailTrace_7907822 : CollatzResearch.WordTrace tailWord_7907822 prefixEnd_7907822 4060513616198664843757595 := by
  unfold tailWord_7907822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052745394664864665006715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192281308771545944880035813 36052745394664864665006715)
  ·
    refine ⟨54079118091997296997510073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36052745394664864665006715 54079118091997296997510073)
    ·
      refine ⟨40559338568997972748132555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54079118091997296997510073 40559338568997972748132555)
      ·
        refine ⟨60839007853496959122198833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40559338568997972748132555 60839007853496959122198833)
        ·
          refine ⟨45629255890122719341649125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60839007853496959122198833 45629255890122719341649125)
          ·
            refine ⟨8555485479398009876559211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45629255890122719341649125 8555485479398009876559211)
            ·
              refine ⟨12833228219097014814838817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555485479398009876559211 12833228219097014814838817)
              ·
                refine ⟨9624921164322761111129113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833228219097014814838817 9624921164322761111129113)
                ·
                  refine ⟨7218690873242070833346835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624921164322761111129113 7218690873242070833346835)
                  ·
                    refine ⟨10828036309863106250020253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218690873242070833346835 10828036309863106250020253)
                    ·
                      refine ⟨4060513616198664843757595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828036309863106250020253 4060513616198664843757595)
                      ·
                        rfl

theorem cell23_7907822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_7907822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907822 prefixEnd_7907822 := by exact prefixLift 7907822
  have htrace : WordTrace (prefixWord ++ tailWord_7907822) baseStart_7907822 baseEnd_7907822 := by
    simpa [prefixWord, tailWord_7907822, baseEnd_7907822] using wordTrace_append hprefix tailTrace_7907822
  have hstable : (prefixWord ++ tailWord_7907822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907822).length < 2 ^ (prefixWord ++ tailWord_7907822).sum := by decide
  have hdescent : baseEnd_7907822 < baseStart_7907822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907845 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_7907845 : Nat := 118140960795 + 7907845 * 2 ^ 59
def prefixEnd_7907845 : Nat := 4983230072969 + 3 ^ 40 * 7907845 * 2
def baseEnd_7907845 : Nat := 4060525426253718253769989

theorem tailTrace_7907845 : CollatzResearch.WordTrace tailWord_7907845 prefixEnd_7907845 4060525426253718253769989 := by
  unfold tailWord_7907845
  simp only [CollatzResearch.WordTrace]
  refine ⟨288422802036235592248140989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192281868024157061498760659 288422802036235592248140989)
  ·
    refine ⟨108158550763588347093052871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288422802036235592248140989 108158550763588347093052871)
    ·
      refine ⟨162237826145382520639579307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108158550763588347093052871 162237826145382520639579307)
      ·
        refine ⟨243356739218073780959368961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162237826145382520639579307 243356739218073780959368961)
        ·
          refine ⟨182517554413555335719526721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243356739218073780959368961 182517554413555335719526721)
          ·
            refine ⟨136888165810166501789645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182517554413555335719526721 136888165810166501789645041)
            ·
              refine ⟨102666124357624876342233781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136888165810166501789645041 102666124357624876342233781)
              ·
                refine ⟨9624949158527332157084417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102666124357624876342233781 9624949158527332157084417)
                ·
                  refine ⟨7218711868895499117813313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624949158527332157084417 7218711868895499117813313)
                  ·
                    refine ⟨5414033901671624338359985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218711868895499117813313 5414033901671624338359985)
                    ·
                      refine ⟨4060525426253718253769989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414033901671624338359985 4060525426253718253769989)
                      ·
                        rfl

theorem cell23_7907845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_7907845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907845 prefixEnd_7907845 := by exact prefixLift 7907845
  have htrace : WordTrace (prefixWord ++ tailWord_7907845) baseStart_7907845 baseEnd_7907845 := by
    simpa [prefixWord, tailWord_7907845, baseEnd_7907845] using wordTrace_append hprefix tailTrace_7907845
  have hstable : (prefixWord ++ tailWord_7907845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907845).length < 2 ^ (prefixWord ++ tailWord_7907845).sum := by decide
  have hdescent : baseEnd_7907845 < baseStart_7907845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907851 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 7]
def baseStart_7907851 : Nat := 118140960795 + 7907851 * 2 ^ 59
def prefixEnd_7907851 : Nat := 4983230072969 + 3 ^ 40 * 7907851 * 2
def baseEnd_7907851 : Nat := 451169834126405025588329

theorem tailTrace_7907851 : CollatzResearch.WordTrace tailWord_7907851 prefixEnd_7907851 451169834126405025588329 := by
  unfold tailWord_7907851
  simp only [CollatzResearch.WordTrace]
  refine ⟨288423020874213855272859407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192282013916142570181906271 288423020874213855272859407)
  ·
    refine ⟨432634531311320782909289111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288423020874213855272859407 432634531311320782909289111)
    ·
      refine ⟨648951796966981174363933667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432634531311320782909289111 648951796966981174363933667)
      ·
        refine ⟨973427695450471761545900501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648951796966981174363933667 973427695450471761545900501)
        ·
          refine ⟨22814711612120431911232043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 973427695450471761545900501 22814711612120431911232043)
          ·
            refine ⟨34222067418180647866848065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22814711612120431911232043 34222067418180647866848065)
            ·
              refine ⟨25666550563635485900136049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34222067418180647866848065 25666550563635485900136049)
              ·
                refine ⟨19249912922726614425102037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25666550563635485900136049 19249912922726614425102037)
                ·
                  refine ⟨451169834126405025588329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19249912922726614425102037 451169834126405025588329)
                  ·
                    rfl

theorem cell23_7907851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 7].length) (baseStart_7907851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907851 prefixEnd_7907851 := by exact prefixLift 7907851
  have htrace : WordTrace (prefixWord ++ tailWord_7907851) baseStart_7907851 baseEnd_7907851 := by
    simpa [prefixWord, tailWord_7907851, baseEnd_7907851] using wordTrace_append hprefix tailTrace_7907851
  have hstable : (prefixWord ++ tailWord_7907851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907851).length < 2 ^ (prefixWord ++ tailWord_7907851).sum := by decide
  have hdescent : baseEnd_7907851 < baseStart_7907851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907891 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_7907891 : Nat := 118140960795 + 7907891 * 2 ^ 59
def prefixEnd_7907891 : Nat := 4983230072969 + 3 ^ 40 * 7907891 * 2
def baseEnd_7907891 : Nat := 4060549046363825073794777

theorem tailTrace_7907891 : CollatzResearch.WordTrace tailWord_7907891 prefixEnd_7907891 4060549046363825073794777 := by
  unfold tailWord_7907891
  simp only [CollatzResearch.WordTrace]
  refine ⟨288424479794068942104315527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192282986529379294736210351 288424479794068942104315527)
  ·
    refine ⟨432636719691103413156473291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288424479794068942104315527 432636719691103413156473291)
    ·
      refine ⟨648955079536655119734709937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432636719691103413156473291 648955079536655119734709937)
      ·
        refine ⟨486716309652491339801032453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648955079536655119734709937 486716309652491339801032453)
        ·
          refine ⟨91259308059842126212693585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486716309652491339801032453 91259308059842126212693585)
          ·
            refine ⟨68444481044881594659520189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91259308059842126212693585 68444481044881594659520189)
            ·
              refine ⟨25666680391830597997320071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68444481044881594659520189 25666680391830597997320071)
              ·
                refine ⟨38500020587745896995980107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25666680391830597997320071 38500020587745896995980107)
                ·
                  refine ⟨57750030881618845493970161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38500020587745896995980107 57750030881618845493970161)
                  ·
                    refine ⟨43312523161214134120477621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57750030881618845493970161 43312523161214134120477621)
                    ·
                      refine ⟨4060549046363825073794777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43312523161214134120477621 4060549046363825073794777)
                      ·
                        rfl

theorem cell23_7907891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_7907891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907891 prefixEnd_7907891 := by exact prefixLift 7907891
  have htrace : WordTrace (prefixWord ++ tailWord_7907891) baseStart_7907891 baseEnd_7907891 := by
    simpa [prefixWord, tailWord_7907891, baseEnd_7907891] using wordTrace_append hprefix tailTrace_7907891
  have hstable : (prefixWord ++ tailWord_7907891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907891).length < 2 ^ (prefixWord ++ tailWord_7907891).sum := by decide
  have hdescent : baseEnd_7907891 < baseStart_7907891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907918 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7907918 : Nat := 118140960795 + 7907918 * 2 ^ 59
def prefixEnd_7907918 : Nat := 4983230072969 + 3 ^ 40 * 7907918 * 2
def baseEnd_7907918 : Nat := 4060562910341496468157153

theorem tailTrace_7907918 : CollatzResearch.WordTrace tailWord_7907918 prefixEnd_7907918 4060562910341496468157153 := by
  unfold tailWord_7907918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36053183070621390714443551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192283643043314083810365605 36053183070621390714443551)
  ·
    refine ⟨54079774605932086071665327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36053183070621390714443551 54079774605932086071665327)
    ·
      refine ⟨81119661908898129107497991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54079774605932086071665327 81119661908898129107497991)
      ·
        refine ⟨121679492863347193661246987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81119661908898129107497991 121679492863347193661246987)
        ·
          refine ⟨182519239295020790491870481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121679492863347193661246987 182519239295020790491870481)
          ·
            refine ⟨136889429471265592868902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182519239295020790491870481 136889429471265592868902861)
            ·
              refine ⟨51333536051724597325838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136889429471265592868902861 51333536051724597325838573)
              ·
                refine ⟨19250076019396723997189465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51333536051724597325838573 19250076019396723997189465)
                ·
                  refine ⟨14437557014547542997892099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250076019396723997189465 14437557014547542997892099)
                  ·
                    refine ⟨21656335521821314496838149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14437557014547542997892099 21656335521821314496838149)
                    ·
                      refine ⟨4060562910341496468157153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21656335521821314496838149 4060562910341496468157153)
                      ·
                        rfl

theorem cell23_7907918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7907918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907918 prefixEnd_7907918 := by exact prefixLift 7907918
  have htrace : WordTrace (prefixWord ++ tailWord_7907918) baseStart_7907918 baseEnd_7907918 := by
    simpa [prefixWord, tailWord_7907918, baseEnd_7907918] using wordTrace_append hprefix tailTrace_7907918
  have hstable : (prefixWord ++ tailWord_7907918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907918).length < 2 ^ (prefixWord ++ tailWord_7907918).sum := by decide
  have hdescent : baseEnd_7907918 < baseStart_7907918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7907972 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7907972 : Nat := 118140960795 + 7907972 * 2 ^ 59
def prefixEnd_7907972 : Nat := 4983230072969 + 3 ^ 40 * 7907972 * 2
def baseEnd_7907972 : Nat := 4060590638296839256881905

theorem tailTrace_7907972 : CollatzResearch.WordTrace tailWord_7907972 prefixEnd_7907972 4060590638296839256881905 := by
  unfold tailWord_7907972
  simp only [CollatzResearch.WordTrace]
  refine ⟨144213717053387746469007085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192284956071183661958676113 144213717053387746469007085)
  ·
    refine ⟨54080143895020404925877657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144213717053387746469007085 54080143895020404925877657)
    ·
      refine ⟨40560107921265303694408243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54080143895020404925877657 40560107921265303694408243)
      ·
        refine ⟨60840161881897955541612365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40560107921265303694408243 60840161881897955541612365)
        ·
          refine ⟨22815060705711733328104637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60840161881897955541612365 22815060705711733328104637)
          ·
            refine ⟨8555647764641899998039239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22815060705711733328104637 8555647764641899998039239)
            ·
              refine ⟨12833471646962849997058859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555647764641899998039239 12833471646962849997058859)
              ·
                refine ⟨19250207470444274995588289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12833471646962849997058859 19250207470444274995588289)
                ·
                  refine ⟨14437655602833206246691217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250207470444274995588289 14437655602833206246691217)
                  ·
                    refine ⟨10828241702124904685018413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14437655602833206246691217 10828241702124904685018413)
                    ·
                      refine ⟨4060590638296839256881905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828241702124904685018413 4060590638296839256881905)
                      ·
                        rfl

theorem cell23_7907972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7907972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7907972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7907972 prefixEnd_7907972 := by exact prefixLift 7907972
  have htrace : WordTrace (prefixWord ++ tailWord_7907972) baseStart_7907972 baseEnd_7907972 := by
    simpa [prefixWord, tailWord_7907972, baseEnd_7907972] using wordTrace_append hprefix tailTrace_7907972
  have hstable : (prefixWord ++ tailWord_7907972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7907972).length < 2 ^ (prefixWord ++ tailWord_7907972).sum := by decide
  have hdescent : baseEnd_7907972 < baseStart_7907972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7907972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908028 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7908028 : Nat := 118140960795 + 7908028 * 2 ^ 59
def prefixEnd_7908028 : Nat := 4983230072969 + 3 ^ 40 * 7908028 * 2
def baseEnd_7908028 : Nat := 4060619393213491037781647

theorem tailTrace_7908028 : CollatzResearch.WordTrace tailWord_7908028 prefixEnd_7908028 4060619393213491037781647 := by
  unfold tailWord_7908028
  simp only [CollatzResearch.WordTrace]
  refine ⟨144214738297286307251026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192286317729715076334701825 144214738297286307251026369)
  ·
    refine ⟨108161053722964730438269777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144214738297286307251026369 108161053722964730438269777)
    ·
      refine ⟨81120790292223547828702333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108161053722964730438269777 81120790292223547828702333)
      ·
        refine ⟨30420296359583830435763375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81120790292223547828702333 30420296359583830435763375)
        ·
          refine ⟨45630444539375745653645063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30420296359583830435763375 45630444539375745653645063)
          ·
            refine ⟨68445666809063618480467595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45630444539375745653645063 68445666809063618480467595)
            ·
              refine ⟨102668500213595427720701393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68445666809063618480467595 102668500213595427720701393)
              ·
                refine ⟨77001375160196570790526045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102668500213595427720701393 77001375160196570790526045)
                ·
                  refine ⟨28875515685073714046447267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77001375160196570790526045 28875515685073714046447267)
                  ·
                    refine ⟨43313273527610571069670901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28875515685073714046447267 43313273527610571069670901)
                    ·
                      refine ⟨4060619393213491037781647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43313273527610571069670901 4060619393213491037781647)
                      ·
                        rfl

theorem cell23_7908028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7908028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908028 prefixEnd_7908028 := by exact prefixLift 7908028
  have htrace : WordTrace (prefixWord ++ tailWord_7908028) baseStart_7908028 baseEnd_7908028 := by
    simpa [prefixWord, tailWord_7908028, baseEnd_7908028] using wordTrace_append hprefix tailTrace_7908028
  have hstable : (prefixWord ++ tailWord_7908028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908028).length < 2 ^ (prefixWord ++ tailWord_7908028).sum := by decide
  have hdescent : baseEnd_7908028 < baseStart_7908028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908036 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_7908036 : Nat := 118140960795 + 7908036 * 2 ^ 59
def prefixEnd_7908036 : Nat := 4983230072969 + 3 ^ 40 * 7908036 * 2
def baseEnd_7908036 : Nat := 4060623501058727006481611

theorem tailTrace_7908036 : CollatzResearch.WordTrace tailWord_7908036 prefixEnd_7908036 4060623501058727006481611 := by
  unfold tailWord_7908036
  simp only [CollatzResearch.WordTrace]
  refine ⟨144214884189271815934171981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192286512252362421245562641 144214884189271815934171981)
  ·
    refine ⟨54080581570976930975314493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144214884189271815934171981 54080581570976930975314493)
    ·
      refine ⟨20280218089116349115742935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54080581570976930975314493 20280218089116349115742935)
      ·
        refine ⟨30420327133674523673614403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20280218089116349115742935 30420327133674523673614403)
        ·
          refine ⟨45630490700511785510421605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30420327133674523673614403 45630490700511785510421605)
          ·
            refine ⟨8555717006345959783204051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45630490700511785510421605 8555717006345959783204051)
            ·
              refine ⟨12833575509518939674806077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555717006345959783204051 12833575509518939674806077)
              ·
                refine ⟨4812590816069602378052279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12833575509518939674806077 4812590816069602378052279)
                ·
                  refine ⟨7218886224104403567078419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812590816069602378052279 7218886224104403567078419)
                  ·
                    refine ⟨10828329336156605350617629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218886224104403567078419 10828329336156605350617629)
                    ·
                      refine ⟨4060623501058727006481611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828329336156605350617629 4060623501058727006481611)
                      ·
                        rfl

theorem cell23_7908036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_7908036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908036 prefixEnd_7908036 := by exact prefixLift 7908036
  have htrace : WordTrace (prefixWord ++ tailWord_7908036) baseStart_7908036 baseEnd_7908036 := by
    simpa [prefixWord, tailWord_7908036, baseEnd_7908036] using wordTrace_append hprefix tailTrace_7908036
  have hstable : (prefixWord ++ tailWord_7908036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908036).length < 2 ^ (prefixWord ++ tailWord_7908036).sum := by decide
  have hdescent : baseEnd_7908036 < baseStart_7908036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908053 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7908053 : Nat := 118140960795 + 7908053 * 2 ^ 59
def prefixEnd_7908053 : Nat := 4983230072969 + 3 ^ 40 * 7908053 * 2
def baseEnd_7908053 : Nat := 4060632230229853439969033

theorem tailTrace_7908053 : CollatzResearch.WordTrace tailWord_7908053 prefixEnd_7908053 4060632230229853439969033 := by
  unfold tailWord_7908053
  simp only [CollatzResearch.WordTrace]
  refine ⟨288430388419482043771712813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192286925612988029181141875 288430388419482043771712813)
  ·
    refine ⟨108161395657305766414392305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288430388419482043771712813 108161395657305766414392305)
    ·
      refine ⟨81121046742979324810794229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108161395657305766414392305 81121046742979324810794229)
      ·
        refine ⟨7605098132154311701011959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81121046742979324810794229 7605098132154311701011959)
        ·
          refine ⟨11407647198231467551517939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605098132154311701011959 11407647198231467551517939)
          ·
            refine ⟨17111470797347201327276909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407647198231467551517939 17111470797347201327276909)
            ·
              refine ⟨6416801549005200497728841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17111470797347201327276909 6416801549005200497728841)
              ·
                refine ⟨4812601161753900373296631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416801549005200497728841 4812601161753900373296631)
                ·
                  refine ⟨7218901742630850559944947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812601161753900373296631 7218901742630850559944947)
                  ·
                    refine ⟨10828352613946275839917421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7218901742630850559944947 10828352613946275839917421)
                    ·
                      refine ⟨4060632230229853439969033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828352613946275839917421 4060632230229853439969033)
                      ·
                        rfl

theorem cell23_7908053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7908053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908053 prefixEnd_7908053 := by exact prefixLift 7908053
  have htrace : WordTrace (prefixWord ++ tailWord_7908053) baseStart_7908053 baseEnd_7908053 := by
    simpa [prefixWord, tailWord_7908053, baseEnd_7908053] using wordTrace_append hprefix tailTrace_7908053
  have hstable : (prefixWord ++ tailWord_7908053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908053).length < 2 ^ (prefixWord ++ tailWord_7908053).sum := by decide
  have hdescent : baseEnd_7908053 < baseStart_7908053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908069 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_7908069 : Nat := 118140960795 + 7908069 * 2 ^ 59
def prefixEnd_7908069 : Nat := 4983230072969 + 3 ^ 40 * 7908069 * 2
def baseEnd_7908069 : Nat := 1353546815306775125789653

theorem tailTrace_7908069 : CollatzResearch.WordTrace tailWord_7908069 prefixEnd_7908069 1353546815306775125789653 := by
  unfold tailWord_7908069
  simp only [CollatzResearch.WordTrace]
  refine ⟨288430971987424078504295261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192287314658282719002863507 288430971987424078504295261)
  ·
    refine ⟨108161614495284029439110723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288430971987424078504295261 108161614495284029439110723)
    ·
      refine ⟨162242421742926044158666085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108161614495284029439110723 162242421742926044158666085)
      ·
        refine ⟨30420454076798633279749891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162242421742926044158666085 30420454076798633279749891)
        ·
          refine ⟨45630681115197949919624837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30420454076798633279749891 45630681115197949919624837)
          ·
            refine ⟨8555752709099615609929657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45630681115197949919624837 8555752709099615609929657)
            ·
              refine ⟨6416814531824711707447243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555752709099615609929657 6416814531824711707447243)
              ·
                refine ⟨9625221797737067561170865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416814531824711707447243 9625221797737067561170865)
                ·
                  refine ⟨7218916348302800670878149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9625221797737067561170865 7218916348302800670878149)
                  ·
                    refine ⟨1353546815306775125789653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218916348302800670878149 1353546815306775125789653)
                    ·
                      rfl

theorem cell23_7908069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_7908069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908069 prefixEnd_7908069 := by exact prefixLift 7908069
  have htrace : WordTrace (prefixWord ++ tailWord_7908069) baseStart_7908069 baseEnd_7908069 := by
    simpa [prefixWord, tailWord_7908069, baseEnd_7908069] using wordTrace_append hprefix tailTrace_7908069
  have hstable : (prefixWord ++ tailWord_7908069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908069).length < 2 ^ (prefixWord ++ tailWord_7908069).sum := by decide
  have hdescent : baseEnd_7908069 < baseStart_7908069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908108 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_7908108 : Nat := 118140960795 + 7908108 * 2 ^ 59
def prefixEnd_7908108 : Nat := 4983230072969 + 3 ^ 40 * 7908108 * 2
def baseEnd_7908108 : Nat := 1353553490555283574927093

theorem tailTrace_7908108 : CollatzResearch.WordTrace tailWord_7908108 prefixEnd_7908108 1353553490555283574927093 := by
  unfold tailWord_7908108
  simp only [CollatzResearch.WordTrace]
  refine ⟨144216197217141394082482489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192288262956188525443309985 144216197217141394082482489)
  ·
    refine ⟨108162147912856045561861867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144216197217141394082482489 108162147912856045561861867)
    ·
      refine ⟨162243221869284068342792801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108162147912856045561861867 162243221869284068342792801)
      ·
        refine ⟨121682416401963051257094601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162243221869284068342792801 121682416401963051257094601)
        ·
          refine ⟨91261812301472288442820951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121682416401963051257094601 91261812301472288442820951)
          ·
            refine ⟨136892718452208432664231427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91261812301472288442820951 136892718452208432664231427)
            ·
              refine ⟨205339077678312648996347141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136892718452208432664231427 205339077678312648996347141)
              ·
                refine ⟨38501077064683621686815089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205339077678312648996347141 38501077064683621686815089)
                ·
                  refine ⟨28875807798512716265111317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38501077064683621686815089 28875807798512716265111317)
                  ·
                    refine ⟨1353553490555283574927093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28875807798512716265111317 1353553490555283574927093)
                    ·
                      rfl

theorem cell23_7908108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_7908108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908108 prefixEnd_7908108 := by exact prefixLift 7908108
  have htrace : WordTrace (prefixWord ++ tailWord_7908108) baseStart_7908108 baseEnd_7908108 := by
    simpa [prefixWord, tailWord_7908108, baseEnd_7908108] using wordTrace_append hprefix tailTrace_7908108
  have hstable : (prefixWord ++ tailWord_7908108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908108).length < 2 ^ (prefixWord ++ tailWord_7908108).sum := by decide
  have hdescent : baseEnd_7908108 < baseStart_7908108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908115 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 4, 2]
def baseStart_7908115 : Nat := 118140960795 + 7908115 * 2 ^ 59
def prefixEnd_7908115 : Nat := 4983230072969 + 3 ^ 40 * 7908115 * 2
def baseEnd_7908115 : Nat := 4060664066030432197393747

theorem tailTrace_7908115 : CollatzResearch.WordTrace tailWord_7908115 prefixEnd_7908115 4060664066030432197393747 := by
  unfold tailWord_7908115
  simp only [CollatzResearch.WordTrace]
  refine ⟨288432649745257428360469799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192288433163504952240313199 288432649745257428360469799)
  ·
    refine ⟨432648974617886142540704699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288432649745257428360469799 432648974617886142540704699)
    ·
      refine ⟨648973461926829213811057049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432648974617886142540704699 648973461926829213811057049)
      ·
        refine ⟨486730096445121910358292787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648973461926829213811057049 486730096445121910358292787)
        ·
          refine ⟨730095144667682865537439181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486730096445121910358292787 730095144667682865537439181)
          ·
            refine ⟨273785679250381074576539693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730095144667682865537439181 273785679250381074576539693)
            ·
              refine ⟨102669629718892902966202385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273785679250381074576539693 102669629718892902966202385)
              ·
                refine ⟨77002222289169677224651789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102669629718892902966202385 77002222289169677224651789)
                ·
                  refine ⟨28875833358438628959244421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77002222289169677224651789 28875833358438628959244421)
                  ·
                    refine ⟨5414218754707242929858329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28875833358438628959244421 5414218754707242929858329)
                    ·
                      refine ⟨4060664066030432197393747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414218754707242929858329 4060664066030432197393747)
                      ·
                        rfl

theorem cell23_7908115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4, 2].length) (baseStart_7908115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908115 prefixEnd_7908115 := by exact prefixLift 7908115
  have htrace : WordTrace (prefixWord ++ tailWord_7908115) baseStart_7908115 baseEnd_7908115 := by
    simpa [prefixWord, tailWord_7908115, baseEnd_7908115] using wordTrace_append hprefix tailTrace_7908115
  have hstable : (prefixWord ++ tailWord_7908115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908115).length < 2 ^ (prefixWord ++ tailWord_7908115).sum := by decide
  have hdescent : baseEnd_7908115 < baseStart_7908115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908172 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 5]
def baseStart_7908172 : Nat := 118140960795 + 7908172 * 2 ^ 59
def prefixEnd_7908172 : Nat := 4983230072969 + 3 ^ 40 * 7908172 * 2
def baseEnd_7908172 : Nat := 451188148269748719375665

theorem tailTrace_7908172 : CollatzResearch.WordTrace tailWord_7908172 prefixEnd_7908172 451188148269748719375665 := by
  unfold tailWord_7908172
  simp only [CollatzResearch.WordTrace]
  refine ⟨144217364353025463547647385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192289819137367284730196513 144217364353025463547647385)
  ·
    refine ⟨108163023264769097660735539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144217364353025463547647385 108163023264769097660735539)
    ·
      refine ⟨162244534897153646491103309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108163023264769097660735539 162244534897153646491103309)
      ·
        refine ⟨60841700586432617434163741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162244534897153646491103309 60841700586432617434163741)
        ·
          refine ⟨22815637719912231537811403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60841700586432617434163741 22815637719912231537811403)
          ·
            refine ⟨34223456579868347306717105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22815637719912231537811403 34223456579868347306717105)
            ·
              refine ⟨25667592434901260480037829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34223456579868347306717105 25667592434901260480037829)
              ·
                refine ⟨4812673581543986340007093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25667592434901260480037829 4812673581543986340007093)
                ·
                  refine ⟨451188148269748719375665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812673581543986340007093 451188148269748719375665)
                  ·
                    rfl

theorem cell23_7908172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_7908172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908172 prefixEnd_7908172 := by exact prefixLift 7908172
  have htrace : WordTrace (prefixWord ++ tailWord_7908172) baseStart_7908172 baseEnd_7908172 := by
    simpa [prefixWord, tailWord_7908172, baseEnd_7908172] using wordTrace_append hprefix tailTrace_7908172
  have hstable : (prefixWord ++ tailWord_7908172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908172).length < 2 ^ (prefixWord ++ tailWord_7908172).sum := by decide
  have hdescent : baseEnd_7908172 < baseStart_7908172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908206 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_7908206 : Nat := 118140960795 + 7908206 * 2 ^ 59
def prefixEnd_7908206 : Nat := 4983230072969 + 3 ^ 40 * 7908206 * 2
def baseEnd_7908206 : Nat := 451190088085554593483981

theorem tailTrace_7908206 : CollatzResearch.WordTrace tailWord_7908206 prefixEnd_7908206 451190088085554593483981 := by
  unfold tailWord_7908206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36054496098490968862754059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192290645858618500601354981 36054496098490968862754059)
  ·
    refine ⟨54081744147736453294131089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36054496098490968862754059 54081744147736453294131089)
    ·
      refine ⟨40561308110802339970598317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54081744147736453294131089 40561308110802339970598317)
      ·
        refine ⟨15210490541550877488974369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40561308110802339970598317 15210490541550877488974369)
        ·
          refine ⟨11407867906163158116730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210490541550877488974369 11407867906163158116730777)
          ·
            refine ⟨8555900929622368587548083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11407867906163158116730777 8555900929622368587548083)
            ·
              refine ⟨12833851394433552881322125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555900929622368587548083 12833851394433552881322125)
              ·
                refine ⟨4812694272912582330495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12833851394433552881322125 4812694272912582330495797)
                ·
                  refine ⟨451190088085554593483981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812694272912582330495797 451190088085554593483981)
                  ·
                    rfl

theorem cell23_7908206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_7908206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908206 prefixEnd_7908206 := by exact prefixLift 7908206
  have htrace : WordTrace (prefixWord ++ tailWord_7908206) baseStart_7908206 baseEnd_7908206 := by
    simpa [prefixWord, tailWord_7908206, baseEnd_7908206] using wordTrace_append hprefix tailTrace_7908206
  have hstable : (prefixWord ++ tailWord_7908206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908206).length < 2 ^ (prefixWord ++ tailWord_7908206).sum := by decide
  have hdescent : baseEnd_7908206 < baseStart_7908206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908215 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 5, 4]
def baseStart_7908215 : Nat := 118140960795 + 7908215 * 2 ^ 59
def prefixEnd_7908215 : Nat := 4983230072969 + 3 ^ 40 * 7908215 * 2
def baseEnd_7908215 : Nat := 1353571804698627268714429

theorem tailTrace_7908215 : CollatzResearch.WordTrace tailWord_7908215 prefixEnd_7908215 1353571804698627268714429 := by
  unfold tailWord_7908215
  simp only [CollatzResearch.WordTrace]
  refine ⟨288436297044895145439110099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192290864696596763626073399 288436297044895145439110099)
  ·
    refine ⟨432654445567342718158665149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288436297044895145439110099 432654445567342718158665149)
    ·
      refine ⟨162245417087753519309499431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432654445567342718158665149 162245417087753519309499431)
      ·
        refine ⟨243368125631630278964249147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162245417087753519309499431 243368125631630278964249147)
        ·
          refine ⟨365052188447445418446373721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243368125631630278964249147 365052188447445418446373721)
          ·
            refine ⟨273789141335584063834780291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365052188447445418446373721 273789141335584063834780291)
            ·
              refine ⟨410683712003376095752170437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273789141335584063834780291 410683712003376095752170437)
              ·
                refine ⟨77003196000633017953531957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410683712003376095752170437 77003196000633017953531957)
                ·
                  refine ⟨7219049625059345433143621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77003196000633017953531957 7219049625059345433143621)
                  ·
                    refine ⟨1353571804698627268714429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7219049625059345433143621 1353571804698627268714429)
                    ·
                      rfl

theorem cell23_7908215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_7908215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908215 prefixEnd_7908215 := by exact prefixLift 7908215
  have htrace : WordTrace (prefixWord ++ tailWord_7908215) baseStart_7908215 baseEnd_7908215 := by
    simpa [prefixWord, tailWord_7908215, baseEnd_7908215] using wordTrace_append hprefix tailTrace_7908215
  have hstable : (prefixWord ++ tailWord_7908215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908215).length < 2 ^ (prefixWord ++ tailWord_7908215).sum := by decide
  have hdescent : baseEnd_7908215 < baseStart_7908215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908276 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7908276 : Nat := 118140960795 + 7908276 * 2 ^ 59
def prefixEnd_7908276 : Nat := 4983230072969 + 3 ^ 40 * 7908276 * 2
def baseEnd_7908276 : Nat := 4060746736415806067480507

theorem tailTrace_7908276 : CollatzResearch.WordTrace tailWord_7908276 prefixEnd_7908276 4060746736415806067480507 := by
  unfold tailWord_7908276
  simp only [CollatzResearch.WordTrace]
  refine ⟨144219260948837076428540341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192292347931782768571387121 144219260948837076428540341)
  ·
    refine ⟨13520555713953475915175657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144219260948837076428540341 13520555713953475915175657)
    ·
      refine ⟨10140416785465106936381743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13520555713953475915175657 10140416785465106936381743)
      ·
        refine ⟨15210625178197660404572615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140416785465106936381743 15210625178197660404572615)
        ·
          refine ⟨22815937767296490606858923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210625178197660404572615 22815937767296490606858923)
          ·
            refine ⟨34223906650944735910288385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22815937767296490606858923 34223906650944735910288385)
            ·
              refine ⟨25667929988208551932716289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34223906650944735910288385 25667929988208551932716289)
              ·
                refine ⟨19250947491156413949537217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25667929988208551932716289 19250947491156413949537217)
                ·
                  refine ⟨14438210618367310462152913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19250947491156413949537217 14438210618367310462152913)
                  ·
                    refine ⟨10828657963775482846614685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14438210618367310462152913 10828657963775482846614685)
                    ·
                      refine ⟨4060746736415806067480507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828657963775482846614685 4060746736415806067480507)
                      ·
                        rfl

theorem cell23_7908276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7908276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908276 prefixEnd_7908276 := by exact prefixLift 7908276
  have htrace : WordTrace (prefixWord ++ tailWord_7908276) baseStart_7908276 baseEnd_7908276 := by
    simpa [prefixWord, tailWord_7908276, baseEnd_7908276] using wordTrace_append hprefix tailTrace_7908276
  have hstable : (prefixWord ++ tailWord_7908276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908276).length < 2 ^ (prefixWord ++ tailWord_7908276).sum := by decide
  have hdescent : baseEnd_7908276 < baseStart_7908276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908306 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7908306 : Nat := 118140960795 + 7908306 * 2 ^ 59
def prefixEnd_7908306 : Nat := 4983230072969 + 3 ^ 40 * 7908306 * 2
def baseEnd_7908306 : Nat := 4060762140835440950105369

theorem tailTrace_7908306 : CollatzResearch.WordTrace tailWord_7908306 prefixEnd_7908306 4060762140835440950105369 := by
  unfold tailWord_7908306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72109904021891366995168193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192293077391710311987115181 72109904021891366995168193)
  ·
    refine ⟨54082428016418525246376145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72109904021891366995168193 54082428016418525246376145)
    ·
      refine ⟨40561821012313893934782109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54082428016418525246376145 40561821012313893934782109)
      ·
        refine ⟨15210682879617710225543291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40561821012313893934782109 15210682879617710225543291)
        ·
          refine ⟨22816024319426565338314937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210682879617710225543291 22816024319426565338314937)
          ·
            refine ⟨17112018239569924003736203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22816024319426565338314937 17112018239569924003736203)
            ·
              refine ⟨25668027359354886005604305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112018239569924003736203 25668027359354886005604305)
              ·
                refine ⟨19251020519516164504203229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25668027359354886005604305 19251020519516164504203229)
                ·
                  refine ⟨7219132694818561689076211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19251020519516164504203229 7219132694818561689076211)
                  ·
                    refine ⟨10828699042227842533614317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219132694818561689076211 10828699042227842533614317)
                    ·
                      refine ⟨4060762140835440950105369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828699042227842533614317 4060762140835440950105369)
                      ·
                        rfl

theorem cell23_7908306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7908306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908306 prefixEnd_7908306 := by exact prefixLift 7908306
  have htrace : WordTrace (prefixWord ++ tailWord_7908306) baseStart_7908306 baseEnd_7908306 := by
    simpa [prefixWord, tailWord_7908306, baseEnd_7908306] using wordTrace_append hprefix tailTrace_7908306
  have hstable : (prefixWord ++ tailWord_7908306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908306).length < 2 ^ (prefixWord ++ tailWord_7908306).sum := by decide
  have hdescent : baseEnd_7908306 < baseStart_7908306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908312 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_7908312 : Nat := 118140960795 + 7908312 * 2 ^ 59
def prefixEnd_7908312 : Nat := 4983230072969 + 3 ^ 40 * 7908312 * 2
def baseEnd_7908312 : Nat := 4060765221719367926630341

theorem tailTrace_7908312 : CollatzResearch.WordTrace tailWord_7908312 prefixEnd_7908312 4060765221719367926630341 := by
  unfold tailWord_7908312
  simp only [CollatzResearch.WordTrace]
  refine ⟨144219917462771865502695595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192293223283695820670260793 144219917462771865502695595)
  ·
    refine ⟨216329876194157798254043393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144219917462771865502695595 216329876194157798254043393)
    ·
      refine ⟨162247407145618348690532545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216329876194157798254043393 162247407145618348690532545)
      ·
        refine ⟨121685555359213761517899409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162247407145618348690532545 121685555359213761517899409)
        ·
          refine ⟨91264166519410321138424557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121685555359213761517899409 91264166519410321138424557)
          ·
            refine ⟨34224062444778870426909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91264166519410321138424557 34224062444778870426909209)
            ·
              refine ⟨25668046833584152820181907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34224062444778870426909209 25668046833584152820181907)
              ·
                refine ⟨38502070250376229230272861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25668046833584152820181907 38502070250376229230272861)
                ·
                  refine ⟨14438276343891085961352323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38502070250376229230272861 14438276343891085961352323)
                  ·
                    refine ⟨21657414515836628942028485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14438276343891085961352323 21657414515836628942028485)
                    ·
                      refine ⟨4060765221719367926630341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21657414515836628942028485 4060765221719367926630341)
                      ·
                        rfl

theorem cell23_7908312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_7908312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908312 prefixEnd_7908312 := by exact prefixLift 7908312
  have htrace : WordTrace (prefixWord ++ tailWord_7908312) baseStart_7908312 baseEnd_7908312 := by
    simpa [prefixWord, tailWord_7908312, baseEnd_7908312] using wordTrace_append hprefix tailTrace_7908312
  have hstable : (prefixWord ++ tailWord_7908312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908312).length < 2 ^ (prefixWord ++ tailWord_7908312).sum := by decide
  have hdescent : baseEnd_7908312 < baseStart_7908312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908335 : List Nat := [1, 1, 2, 1, 4, 4, 10]
def baseStart_7908335 : Nat := 118140960795 + 7908335 * 2 ^ 59
def prefixEnd_7908335 : Nat := 4983230072969 + 3 ^ 40 * 7908335 * 2
def baseEnd_7908335 : Nat := 50133049774992856007935

theorem tailTrace_7908335 : CollatzResearch.WordTrace tailWord_7908335 prefixEnd_7908335 50133049774992856007935 := by
  unfold tailWord_7908335
  simp only [CollatzResearch.WordTrace]
  refine ⟨288440673804460405933478459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192293782536306937288985639 288440673804460405933478459)
  ·
    refine ⟨432661010706690608900217689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288440673804460405933478459 432661010706690608900217689)
    ·
      refine ⟨324495758030017956675163267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432661010706690608900217689 324495758030017956675163267)
      ·
        refine ⟨486743637045026935012744901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324495758030017956675163267 486743637045026935012744901)
        ·
          refine ⟨91264431945942550314889669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486743637045026935012744901 91264431945942550314889669)
          ·
            refine ⟨17112080989864228184041813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91264431945942550314889669 17112080989864228184041813)
            ·
              refine ⟨50133049774992856007935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17112080989864228184041813 50133049774992856007935)
              ·
                rfl

theorem cell23_7908335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 10].length) (baseStart_7908335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908335 prefixEnd_7908335 := by exact prefixLift 7908335
  have htrace : WordTrace (prefixWord ++ tailWord_7908335) baseStart_7908335 baseEnd_7908335 := by
    simpa [prefixWord, tailWord_7908335, baseEnd_7908335] using wordTrace_append hprefix tailTrace_7908335
  have hstable : (prefixWord ++ tailWord_7908335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908335).length < 2 ^ (prefixWord ++ tailWord_7908335).sum := by decide
  have hdescent : baseEnd_7908335 < baseStart_7908335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908366 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7908366 : Nat := 118140960795 + 7908366 * 2 ^ 59
def prefixEnd_7908366 : Nat := 4983230072969 + 3 ^ 40 * 7908366 * 2
def baseEnd_7908366 : Nat := 4060792949674710715355093

theorem tailTrace_7908366 : CollatzResearch.WordTrace tailWord_7908366 prefixEnd_7908366 4060792949674710715355093 := by
  unfold tailWord_7908366
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055225558418512278482119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192294536311565398818571301 36055225558418512278482119)
  ·
    refine ⟨54082838337627768417723179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36055225558418512278482119 54082838337627768417723179)
    ·
      refine ⟨81124257506441652626584769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54082838337627768417723179 81124257506441652626584769)
      ·
        refine ⟨60843193129831239469938577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81124257506441652626584769 60843193129831239469938577)
        ·
          refine ⟨45632394847373429602453933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60843193129831239469938577 45632394847373429602453933)
          ·
            refine ⟨17112148067765036100920225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45632394847373429602453933 17112148067765036100920225)
            ·
              refine ⟨12834111050823777075690169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17112148067765036100920225 12834111050823777075690169)
              ·
                refine ⟨9625583288117832806767627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12834111050823777075690169 9625583288117832806767627)
                ·
                  refine ⟨14438374932176749210151441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9625583288117832806767627 14438374932176749210151441)
                  ·
                    refine ⟨10828781199132561907613581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14438374932176749210151441 10828781199132561907613581)
                    ·
                      refine ⟨4060792949674710715355093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828781199132561907613581 4060792949674710715355093)
                      ·
                        rfl

theorem cell23_7908366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7908366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908366 prefixEnd_7908366 := by exact prefixLift 7908366
  have htrace : WordTrace (prefixWord ++ tailWord_7908366) baseStart_7908366 baseEnd_7908366 := by
    simpa [prefixWord, tailWord_7908366, baseEnd_7908366] using wordTrace_append hprefix tailTrace_7908366
  have hstable : (prefixWord ++ tailWord_7908366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908366).length < 2 ^ (prefixWord ++ tailWord_7908366).sum := by decide
  have hdescent : baseEnd_7908366 < baseStart_7908366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908402 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_7908402 : Nat := 118140960795 + 7908402 * 2 ^ 59
def prefixEnd_7908402 : Nat := 4983230072969 + 3 ^ 40 * 7908402 * 2
def baseEnd_7908402 : Nat := 4060811434978272574504927

theorem tailTrace_7908402 : CollatzResearch.WordTrace tailWord_7908402 prefixEnd_7908402 4060811434978272574504927 := by
  unfold tailWord_7908402
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110779373804419094041865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192295411663478450917444973 72110779373804419094041865)
  ·
    refine ⟨54083084530353314320531399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72110779373804419094041865 54083084530353314320531399)
    ·
      refine ⟨81124626795529971480797099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54083084530353314320531399 81124626795529971480797099)
      ·
        refine ⟨121686940193294957221195649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81124626795529971480797099 121686940193294957221195649)
        ·
          refine ⟨91265205144971217915896737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121686940193294957221195649 91265205144971217915896737)
          ·
            refine ⟨68448903858728413436922553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91265205144971217915896737 68448903858728413436922553)
            ·
              refine ⟨51336677894046310077691915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68448903858728413436922553 51336677894046310077691915)
              ·
                refine ⟨77005016841069465116537873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51336677894046310077691915 77005016841069465116537873)
                ·
                  refine ⟨57753762630802098837403405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77005016841069465116537873 57753762630802098837403405)
                  ·
                    refine ⟨21657660986550787064026277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57753762630802098837403405 21657660986550787064026277)
                    ·
                      refine ⟨4060811434978272574504927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21657660986550787064026277 4060811434978272574504927)
                      ·
                        rfl

theorem cell23_7908402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_7908402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908402 prefixEnd_7908402 := by exact prefixLift 7908402
  have htrace : WordTrace (prefixWord ++ tailWord_7908402) baseStart_7908402 baseEnd_7908402 := by
    simpa [prefixWord, tailWord_7908402, baseEnd_7908402] using wordTrace_append hprefix tailTrace_7908402
  have hstable : (prefixWord ++ tailWord_7908402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908402).length < 2 ^ (prefixWord ++ tailWord_7908402).sum := by decide
  have hdescent : baseEnd_7908402 < baseStart_7908402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908413 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7908413 : Nat := 118140960795 + 7908413 * 2 ^ 59
def prefixEnd_7908413 : Nat := 4983230072969 + 3 ^ 40 * 7908413 * 2
def baseEnd_7908413 : Nat := 4060817083265472031467377

theorem tailTrace_7908413 : CollatzResearch.WordTrace tailWord_7908413 prefixEnd_7908413 4060817083265472031467377 := by
  unfold tailWord_7908413
  simp only [CollatzResearch.WordTrace]
  refine ⟨288443518698177825254817893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192295679132118550169878595 288443518698177825254817893)
  ·
    refine ⟨54083159755908342235278355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288443518698177825254817893 54083159755908342235278355)
    ·
      refine ⟨81124739633862513352917533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54083159755908342235278355 81124739633862513352917533)
      ·
        refine ⟨30421777362698442507344075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81124739633862513352917533 30421777362698442507344075)
        ·
          refine ⟨45632666044047663761016113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30421777362698442507344075 45632666044047663761016113)
          ·
            refine ⟨34224499533035747820762085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45632666044047663761016113 34224499533035747820762085)
            ·
              refine ⟨6417093662444202716392891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34224499533035747820762085 6417093662444202716392891)
              ·
                refine ⟨9625640493666304074589337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417093662444202716392891 9625640493666304074589337)
                ·
                  refine ⟨7219230370249728055942003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9625640493666304074589337 7219230370249728055942003)
                  ·
                    refine ⟨10828845555374592083913005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219230370249728055942003 10828845555374592083913005)
                    ·
                      refine ⟨4060817083265472031467377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10828845555374592083913005 4060817083265472031467377)
                      ·
                        rfl

theorem cell23_7908413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7908413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908413 prefixEnd_7908413 := by exact prefixLift 7908413
  have htrace : WordTrace (prefixWord ++ tailWord_7908413) baseStart_7908413 baseEnd_7908413 := by
    simpa [prefixWord, tailWord_7908413, baseEnd_7908413] using wordTrace_append hprefix tailTrace_7908413
  have hstable : (prefixWord ++ tailWord_7908413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908413).length < 2 ^ (prefixWord ++ tailWord_7908413).sum := by decide
  have hdescent : baseEnd_7908413 < baseStart_7908413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908419 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 4, 2]
def baseStart_7908419 : Nat := 118140960795 + 7908419 * 2 ^ 59
def prefixEnd_7908419 : Nat := 4983230072969 + 3 ^ 40 * 7908419 * 2
def baseEnd_7908419 : Nat := 4060820164149399007992349

theorem tailTrace_7908419 : CollatzResearch.WordTrace tailWord_7908419 prefixEnd_7908419 4060820164149399007992349 := by
  unfold tailWord_7908419
  simp only [CollatzResearch.WordTrace]
  refine ⟨288443737536156088279536311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192295825024104058853024207 288443737536156088279536311)
  ·
    refine ⟨432665606304234132419304467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288443737536156088279536311 432665606304234132419304467)
    ·
      refine ⟨648998409456351198628956701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432665606304234132419304467 648998409456351198628956701)
      ·
        refine ⟨243374403546131699485858763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648998409456351198628956701 243374403546131699485858763)
        ·
          refine ⟨365061605319197549228788145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243374403546131699485858763 365061605319197549228788145)
          ·
            refine ⟨273796203989398161921591109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365061605319197549228788145 273796203989398161921591109)
            ·
              refine ⟨51336788248012155360298333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273796203989398161921591109 51336788248012155360298333)
              ·
                refine ⟨19251295593004558260111875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51336788248012155360298333 19251295593004558260111875)
                ·
                  refine ⟨28876943389506837390167813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19251295593004558260111875 28876943389506837390167813)
                  ·
                    refine ⟨5414426885532532010656465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28876943389506837390167813 5414426885532532010656465)
                    ·
                      refine ⟨4060820164149399007992349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414426885532532010656465 4060820164149399007992349)
                      ·
                        rfl

theorem cell23_7908419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_7908419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908419 prefixEnd_7908419 := by exact prefixLift 7908419
  have htrace : WordTrace (prefixWord ++ tailWord_7908419) baseStart_7908419 baseEnd_7908419 := by
    simpa [prefixWord, tailWord_7908419, baseEnd_7908419] using wordTrace_append hprefix tailTrace_7908419
  have hstable : (prefixWord ++ tailWord_7908419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908419).length < 2 ^ (prefixWord ++ tailWord_7908419).sum := by decide
  have hdescent : baseEnd_7908419 < baseStart_7908419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908423 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_7908423 : Nat := 118140960795 + 7908423 * 2 ^ 59
def prefixEnd_7908423 : Nat := 4983230072969 + 3 ^ 40 * 7908423 * 2
def baseEnd_7908423 : Nat := 4060822218072016992342331

theorem tailTrace_7908423 : CollatzResearch.WordTrace tailWord_7908423 prefixEnd_7908423 4060822218072016992342331 := by
  unfold tailWord_7908423
  simp only [CollatzResearch.WordTrace]
  refine ⟨288443883428141596962681923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192295922285427731308454615 288443883428141596962681923)
  ·
    refine ⟨432665825142212395444022885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288443883428141596962681923 432665825142212395444022885)
    ·
      refine ⟨81124842214164824145754291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432665825142212395444022885 81124842214164824145754291)
      ·
        refine ⟨121687263321247236218631437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81124842214164824145754291 121687263321247236218631437)
        ·
          refine ⟨45632723745467713581986789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121687263321247236218631437 45632723745467713581986789)
          ·
            refine ⟨8556135702275196296622523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45632723745467713581986789 8556135702275196296622523)
            ·
              refine ⟨12834203553412794444933785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556135702275196296622523 12834203553412794444933785)
              ·
                refine ⟨9625652665059595833700339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12834203553412794444933785 9625652665059595833700339)
                ·
                  refine ⟨14438478997589393750550509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9625652665059595833700339 14438478997589393750550509)
                  ·
                    refine ⟨5414429624096022656456441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14438478997589393750550509 5414429624096022656456441)
                    ·
                      refine ⟨4060822218072016992342331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414429624096022656456441 4060822218072016992342331)
                      ·
                        rfl

theorem cell23_7908423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_7908423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908423 prefixEnd_7908423 := by exact prefixLift 7908423
  have htrace : WordTrace (prefixWord ++ tailWord_7908423) baseStart_7908423 baseEnd_7908423 := by
    simpa [prefixWord, tailWord_7908423, baseEnd_7908423] using wordTrace_append hprefix tailTrace_7908423
  have hstable : (prefixWord ++ tailWord_7908423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908423).length < 2 ^ (prefixWord ++ tailWord_7908423).sum := by decide
  have hdescent : baseEnd_7908423 < baseStart_7908423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908436 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_7908436 : Nat := 118140960795 + 7908436 * 2 ^ 59
def prefixEnd_7908436 : Nat := 4983230072969 + 3 ^ 40 * 7908436 * 2
def baseEnd_7908436 : Nat := 4060828893320525441479771

theorem tailTrace_7908436 : CollatzResearch.WordTrace tailWord_7908436 prefixEnd_7908436 4060828893320525441479771 := by
  unfold tailWord_7908436
  simp only [CollatzResearch.WordTrace]
  refine ⟨144222178788547250091452581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192296238384729666788603441 144222178788547250091452581)
  ·
    refine ⟨27041658522852609392147359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144222178788547250091452581 27041658522852609392147359)
    ·
      refine ⟨40562487784278914088221039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27041658522852609392147359 40562487784278914088221039)
      ·
        refine ⟨60843731676418371132331559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40562487784278914088221039 60843731676418371132331559)
        ·
          refine ⟨91265597514627556698497339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60843731676418371132331559 91265597514627556698497339)
          ·
            refine ⟨136898396271941335047746009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91265597514627556698497339 136898396271941335047746009)
            ·
              refine ⟨102673797203956001285809507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136898396271941335047746009 102673797203956001285809507)
              ·
                refine ⟨154010695805934001928714261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102673797203956001285809507 154010695805934001928714261)
                ·
                  refine ⟨7219251365903156340408481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154010695805934001928714261 7219251365903156340408481)
                  ·
                    refine ⟨5414438524427367255306361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219251365903156340408481 5414438524427367255306361)
                    ·
                      refine ⟨4060828893320525441479771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414438524427367255306361 4060828893320525441479771)
                      ·
                        rfl

theorem cell23_7908436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_7908436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908436 prefixEnd_7908436 := by exact prefixLift 7908436
  have htrace : WordTrace (prefixWord ++ tailWord_7908436) baseStart_7908436 baseEnd_7908436 := by
    simpa [prefixWord, tailWord_7908436, baseEnd_7908436] using wordTrace_append hprefix tailTrace_7908436
  have hstable : (prefixWord ++ tailWord_7908436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908436).length < 2 ^ (prefixWord ++ tailWord_7908436).sum := by decide
  have hdescent : baseEnd_7908436 < baseStart_7908436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908453 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_7908453 : Nat := 118140960795 + 7908453 * 2 ^ 59
def prefixEnd_7908453 : Nat := 4983230072969 + 3 ^ 40 * 7908453 * 2
def baseEnd_7908453 : Nat := 4060837622491651874967193

theorem tailTrace_7908453 : CollatzResearch.WordTrace tailWord_7908453 prefixEnd_7908453 4060837622491651874967193 := by
  unfold tailWord_7908453
  simp only [CollatzResearch.WordTrace]
  refine ⟨288444977618032912086274013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192296651745355274724182675 288444977618032912086274013)
  ·
    refine ⟨108166866606762342032352755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288444977618032912086274013 108166866606762342032352755)
    ·
      refine ⟨162250299910143513048529133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108166866606762342032352755 162250299910143513048529133)
      ·
        refine ⟨60843862466303817393198425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162250299910143513048529133 60843862466303817393198425)
        ·
          refine ⟨45632896849727863044898819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60843862466303817393198425 45632896849727863044898819)
          ·
            refine ⟨68449345274591794567348229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45632896849727863044898819 68449345274591794567348229)
            ·
              refine ⟨12834252238985961481377793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68449345274591794567348229 12834252238985961481377793)
              ·
                refine ⟨9625689179239471111033345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12834252238985961481377793 9625689179239471111033345)
                ·
                  refine ⟨7219266884429603333275009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9625689179239471111033345 7219266884429603333275009)
                  ·
                    refine ⟨5414450163322202499956257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219266884429603333275009 5414450163322202499956257)
                    ·
                      refine ⟨4060837622491651874967193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414450163322202499956257 4060837622491651874967193)
                      ·
                        rfl

theorem cell23_7908453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_7908453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908453 prefixEnd_7908453 := by exact prefixLift 7908453
  have htrace : WordTrace (prefixWord ++ tailWord_7908453) baseStart_7908453 baseEnd_7908453 := by
    simpa [prefixWord, tailWord_7908453, baseEnd_7908453] using wordTrace_append hprefix tailTrace_7908453
  have hstable : (prefixWord ++ tailWord_7908453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908453).length < 2 ^ (prefixWord ++ tailWord_7908453).sum := by decide
  have hdescent : baseEnd_7908453 < baseStart_7908453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908472 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_7908472 : Nat := 118140960795 + 7908472 * 2 ^ 59
def prefixEnd_7908472 : Nat := 4983230072969 + 3 ^ 40 * 7908472 * 2
def baseEnd_7908472 : Nat := 1353615792874695766876535

theorem tailTrace_7908472 : CollatzResearch.WordTrace tailWord_7908472 prefixEnd_7908472 1353615792874695766876535 := by
  unfold tailWord_7908472
  simp only [CollatzResearch.WordTrace]
  refine ⟨144222835302482039165607835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192297113736642718887477113 144222835302482039165607835)
  ·
    refine ⟨216334252953723058748411753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144222835302482039165607835 216334252953723058748411753)
    ·
      refine ⟨162250689715292294061308815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216334252953723058748411753 162250689715292294061308815)
      ·
        refine ⟨243376034572938441091963223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162250689715292294061308815 243376034572938441091963223)
        ·
          refine ⟨365064051859407661637944835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243376034572938441091963223 365064051859407661637944835)
          ·
            refine ⟨547596077789111492456917253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365064051859407661637944835 547596077789111492456917253)
            ·
              refine ⟨102674264585458404835671985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547596077789111492456917253 102674264585458404835671985)
              ·
                refine ⟨77005698439093803626753989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102674264585458404835671985 77005698439093803626753989)
                ·
                  refine ⟨14438568457330088180016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77005698439093803626753989 14438568457330088180016373)
                  ·
                    refine ⟨1353615792874695766876535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14438568457330088180016373 1353615792874695766876535)
                    ·
                      rfl

theorem cell23_7908472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_7908472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908472 prefixEnd_7908472 := by exact prefixLift 7908472
  have htrace : WordTrace (prefixWord ++ tailWord_7908472) baseStart_7908472 baseEnd_7908472 := by
    simpa [prefixWord, tailWord_7908472, baseEnd_7908472] using wordTrace_append hprefix tailTrace_7908472
  have hstable : (prefixWord ++ tailWord_7908472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908472).length < 2 ^ (prefixWord ++ tailWord_7908472).sum := by decide
  have hdescent : baseEnd_7908472 < baseStart_7908472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908489 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_7908489 : Nat := 118140960795 + 7908489 * 2 ^ 59
def prefixEnd_7908489 : Nat := 4983230072969 + 3 ^ 40 * 7908489 * 2
def baseEnd_7908489 : Nat := 1353618702598404578039009

theorem tailTrace_7908489 : CollatzResearch.WordTrace tailWord_7908489 prefixEnd_7908489 1353618702598404578039009 := by
  unfold tailWord_7908489
  simp only [CollatzResearch.WordTrace]
  refine ⟨288446290645902490234584521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192297527097268326823056347 288446290645902490234584521)
  ·
    refine ⟨216334717984426867675938391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288446290645902490234584521 216334717984426867675938391)
    ·
      refine ⟨324502076976640301513907587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216334717984426867675938391 324502076976640301513907587)
      ·
        refine ⟨486753115464960452270861381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324502076976640301513907587 486753115464960452270861381)
        ·
          refine ⟨91266209149680084800786509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486753115464960452270861381 91266209149680084800786509)
          ·
            refine ⟨34224828431130031800294941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91266209149680084800786509 34224828431130031800294941)
            ·
              refine ⟨12834310661673761925110603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34224828431130031800294941 12834310661673761925110603)
              ·
                refine ⟨19251465992510642887665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12834310661673761925110603 19251465992510642887665905)
                ·
                  refine ⟨14438599494382982165749429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19251465992510642887665905 14438599494382982165749429)
                  ·
                    refine ⟨1353618702598404578039009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14438599494382982165749429 1353618702598404578039009)
                    ·
                      rfl

theorem cell23_7908489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_7908489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908489 prefixEnd_7908489 := by exact prefixLift 7908489
  have htrace : WordTrace (prefixWord ++ tailWord_7908489) baseStart_7908489 baseEnd_7908489 := by
    simpa [prefixWord, tailWord_7908489, baseEnd_7908489] using wordTrace_append hprefix tailTrace_7908489
  have hstable : (prefixWord ++ tailWord_7908489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908489).length < 2 ^ (prefixWord ++ tailWord_7908489).sum := by decide
  have hdescent : baseEnd_7908489 < baseStart_7908489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908509 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7908509 : Nat := 118140960795 + 7908509 * 2 ^ 59
def prefixEnd_7908509 : Nat := 4983230072969 + 3 ^ 40 * 7908509 * 2
def baseEnd_7908509 : Nat := 4060866377408303655866935

theorem tailTrace_7908509 : CollatzResearch.WordTrace tailWord_7908509 prefixEnd_7908509 4060866377408303655866935 := by
  unfold tailWord_7908509
  simp only [CollatzResearch.WordTrace]
  refine ⟨288447020105830033650312581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192298013403886689100208387 288447020105830033650312581)
  ·
    refine ⟨54083816269843131309433609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288447020105830033650312581 54083816269843131309433609)
    ·
      refine ⟨40562862202382348482075207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54083816269843131309433609 40562862202382348482075207)
      ·
        refine ⟨60844293303573522723112811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40562862202382348482075207 60844293303573522723112811)
        ·
          refine ⟨91266439955360284084669217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60844293303573522723112811 91266439955360284084669217)
          ·
            refine ⟨68449829966520213063501913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91266439955360284084669217 68449829966520213063501913)
            ·
              refine ⟨51337372474890159797626435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68449829966520213063501913 51337372474890159797626435)
              ·
                refine ⟨77006058712335239696439653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51337372474890159797626435 77006058712335239696439653)
                ·
                  refine ⟨14438636008562857443082435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77006058712335239696439653 14438636008562857443082435)
                  ·
                    refine ⟨21657954012844286164623653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14438636008562857443082435 21657954012844286164623653)
                    ·
                      refine ⟨4060866377408303655866935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21657954012844286164623653 4060866377408303655866935)
                      ·
                        rfl

theorem cell23_7908509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7908509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908509 prefixEnd_7908509 := by exact prefixLift 7908509
  have htrace : WordTrace (prefixWord ++ tailWord_7908509) baseStart_7908509 baseEnd_7908509 := by
    simpa [prefixWord, tailWord_7908509, baseEnd_7908509] using wordTrace_append hprefix tailTrace_7908509
  have hstable : (prefixWord ++ tailWord_7908509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908509).length < 2 ^ (prefixWord ++ tailWord_7908509).sum := by decide
  have hdescent : baseEnd_7908509 < baseStart_7908509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908599 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_7908599 : Nat := 118140960795 + 7908599 * 2 ^ 59
def prefixEnd_7908599 : Nat := 4983230072969 + 3 ^ 40 * 7908599 * 2
def baseEnd_7908599 : Nat := 4060912590667208303741521

theorem tailTrace_7908599 : CollatzResearch.WordTrace tailWord_7908599 prefixEnd_7908599 4060912590667208303741521 := by
  unfold tailWord_7908599
  simp only [CollatzResearch.WordTrace]
  refine ⟨288450302675503979021088851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192300201783669319347392567 288450302675503979021088851)
  ·
    refine ⟨432675454013255968531633277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288450302675503979021088851 432675454013255968531633277)
    ·
      refine ⟨162253295254970988199362479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432675454013255968531633277 162253295254970988199362479)
      ·
        refine ⟨243379942882456482299043719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162253295254970988199362479 243379942882456482299043719)
        ·
          refine ⟨365069914323684723448565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243379942882456482299043719 365069914323684723448565579)
          ·
            refine ⟨547604871485527085172848369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365069914323684723448565579 547604871485527085172848369)
            ·
              refine ⟨410703653614145313879636277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547604871485527085172848369 410703653614145313879636277)
              ·
                refine ⟨38503467526326123176215901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410703653614145313879636277 38503467526326123176215901)
                ·
                  refine ⟨14438800322372296191080963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38503467526326123176215901 14438800322372296191080963)
                  ·
                    refine ⟨21658200483558444286621445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14438800322372296191080963 21658200483558444286621445)
                    ·
                      refine ⟨4060912590667208303741521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21658200483558444286621445 4060912590667208303741521)
                      ·
                        rfl

theorem cell23_7908599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_7908599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908599 prefixEnd_7908599 := by exact prefixLift 7908599
  have htrace : WordTrace (prefixWord ++ tailWord_7908599) baseStart_7908599 baseEnd_7908599 := by
    simpa [prefixWord, tailWord_7908599, baseEnd_7908599] using wordTrace_append hprefix tailTrace_7908599
  have hstable : (prefixWord ++ tailWord_7908599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908599).length < 2 ^ (prefixWord ++ tailWord_7908599).sum := by decide
  have hdescent : baseEnd_7908599 < baseStart_7908599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908609 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7908609 : Nat := 118140960795 + 7908609 * 2 ^ 59
def prefixEnd_7908609 : Nat := 4983230072969 + 3 ^ 40 * 7908609 * 2
def baseEnd_7908609 : Nat := 1353639241824584421538825

theorem tailTrace_7908609 : CollatzResearch.WordTrace tailWord_7908609 prefixEnd_7908609 1353639241824584421538825 := by
  unfold tailWord_7908609
  simp only [CollatzResearch.WordTrace]
  refine ⟨288450667405467750728952881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192300444936978500485968587 288450667405467750728952881)
  ·
    refine ⟨216338000554100813046714661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288450667405467750728952881 216338000554100813046714661)
    ·
      refine ⟨40563375103893902446258999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216338000554100813046714661 40563375103893902446258999)
      ·
        refine ⟨60845062655840853669388499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40563375103893902446258999 60845062655840853669388499)
        ·
          refine ⟨91267593983761280504082749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60845062655840853669388499 91267593983761280504082749)
          ·
            refine ⟨34225347743910480189031031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91267593983761280504082749 34225347743910480189031031)
            ·
              refine ⟨51338021615865720283546547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34225347743910480189031031 51338021615865720283546547)
              ·
                refine ⟨77007032423798580425319821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51338021615865720283546547 77007032423798580425319821)
                ·
                  refine ⟨28877637158924467659494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77007032423798580425319821 28877637158924467659494933)
                  ·
                    refine ⟨1353639241824584421538825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28877637158924467659494933 1353639241824584421538825)
                    ·
                      rfl

theorem cell23_7908609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7908609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908609 prefixEnd_7908609 := by exact prefixLift 7908609
  have htrace : WordTrace (prefixWord ++ tailWord_7908609) baseStart_7908609 baseEnd_7908609 := by
    simpa [prefixWord, tailWord_7908609, baseEnd_7908609] using wordTrace_append hprefix tailTrace_7908609
  have hstable : (prefixWord ++ tailWord_7908609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908609).length < 2 ^ (prefixWord ++ tailWord_7908609).sum := by decide
  have hdescent : baseEnd_7908609 < baseStart_7908609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908629 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7908629 : Nat := 118140960795 + 7908629 * 2 ^ 59
def prefixEnd_7908629 : Nat := 4983230072969 + 3 ^ 40 * 7908629 * 2
def baseEnd_7908629 : Nat := 4060927995086843186366383

theorem tailTrace_7908629 : CollatzResearch.WordTrace tailWord_7908629 prefixEnd_7908629 4060927995086843186366383 := by
  unfold tailWord_7908629
  simp only [CollatzResearch.WordTrace]
  refine ⟨288451396865395294144680941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192300931243596862763120627 288451396865395294144680941)
  ·
    refine ⟨108169273824523235304255353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288451396865395294144680941 108169273824523235304255353)
    ·
      refine ⟨81126955368392426478191515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108169273824523235304255353 81126955368392426478191515)
      ·
        refine ⟨121690433052588639717287273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81126955368392426478191515 121690433052588639717287273)
        ·
          refine ⟨91267824789441479787965455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121690433052588639717287273 91267824789441479787965455)
          ·
            refine ⟨136901737184162219681948183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91267824789441479787965455 136901737184162219681948183)
            ·
              refine ⟨205352605776243329522922275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136901737184162219681948183 205352605776243329522922275)
              ·
                refine ⟨308028908664364994284383413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205352605776243329522922275 308028908664364994284383413)
                ·
                  refine ⟨28877710187284218214160945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308028908664364994284383413 28877710187284218214160945)
                  ·
                    refine ⟨21658282640463163660620709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28877710187284218214160945 21658282640463163660620709)
                    ·
                      refine ⟨4060927995086843186366383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21658282640463163660620709 4060927995086843186366383)
                      ·
                        rfl

theorem cell23_7908629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7908629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908629 prefixEnd_7908629 := by exact prefixLift 7908629
  have htrace : WordTrace (prefixWord ++ tailWord_7908629) baseStart_7908629 baseEnd_7908629 := by
    simpa [prefixWord, tailWord_7908629, baseEnd_7908629] using wordTrace_append hprefix tailTrace_7908629
  have hstable : (prefixWord ++ tailWord_7908629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908629).length < 2 ^ (prefixWord ++ tailWord_7908629).sum := by decide
  have hdescent : baseEnd_7908629 < baseStart_7908629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908636 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7908636 : Nat := 118140960795 + 7908636 * 2 ^ 59
def prefixEnd_7908636 : Nat := 4983230072969 + 3 ^ 40 * 7908636 * 2
def baseEnd_7908636 : Nat := 4060931589451424658978851

theorem tailTrace_7908636 : CollatzResearch.WordTrace tailWord_7908636 prefixEnd_7908636 4060931589451424658978851 := by
  unfold tailWord_7908636
  simp only [CollatzResearch.WordTrace]
  refine ⟨144225826088184967170092881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192301101450913289560123841 144225826088184967170092881)
  ·
    refine ⟨108169369566138725377569661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144225826088184967170092881 108169369566138725377569661)
    ·
      refine ⟨40563513587302022016588623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108169369566138725377569661 40563513587302022016588623)
      ·
        refine ⟨60845270380953033024882935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40563513587302022016588623 60845270380953033024882935)
        ·
          refine ⟨91267905571429549537324403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60845270380953033024882935 91267905571429549537324403)
          ·
            refine ⟨136901858357144324305986605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91267905571429549537324403 136901858357144324305986605)
            ·
              refine ⟨51338196883929121614744977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136901858357144324305986605 51338196883929121614744977)
              ·
                refine ⟨38503647662946841211058733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51338196883929121614744977 38503647662946841211058733)
                ·
                  refine ⟨14438867873605065454147025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38503647662946841211058733 14438867873605065454147025)
                  ·
                    refine ⟨10829150905203799090610269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14438867873605065454147025 10829150905203799090610269)
                    ·
                      refine ⟨4060931589451424658978851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829150905203799090610269 4060931589451424658978851)
                      ·
                        rfl

theorem cell23_7908636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7908636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908636 prefixEnd_7908636 := by exact prefixLift 7908636
  have htrace : WordTrace (prefixWord ++ tailWord_7908636) baseStart_7908636 baseEnd_7908636 := by
    simpa [prefixWord, tailWord_7908636, baseEnd_7908636] using wordTrace_append hprefix tailTrace_7908636
  have hstable : (prefixWord ++ tailWord_7908636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908636).length < 2 ^ (prefixWord ++ tailWord_7908636).sum := by decide
  have hdescent : baseEnd_7908636 < baseStart_7908636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908650 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7908650 : Nat := 118140960795 + 7908650 * 2 ^ 59
def prefixEnd_7908650 : Nat := 4983230072969 + 3 ^ 40 * 7908650 * 2
def baseEnd_7908650 : Nat := 4060938778180587604203787

theorem tailTrace_7908650 : CollatzResearch.WordTrace tailWord_7908650 prefixEnd_7908650 4060938778180587604203787 := by
  unfold tailWord_7908650
  simp only [CollatzResearch.WordTrace]
  refine ⟨72113040699579803682798851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192301441865546143154130269 72113040699579803682798851)
  ·
    refine ⟨108169561049369705524198277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72113040699579803682798851 108169561049369705524198277)
    ·
      refine ⟨20281792696756819785787177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108169561049369705524198277 20281792696756819785787177)
      ·
        refine ⟨15211344522567614839340383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20281792696756819785787177 15211344522567614839340383)
        ·
          refine ⟨22817016783851422259010575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15211344522567614839340383 22817016783851422259010575)
          ·
            refine ⟨34225525175777133388515863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22817016783851422259010575 34225525175777133388515863)
            ·
              refine ⟨51338287763665700082773795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34225525175777133388515863 51338287763665700082773795)
              ·
                refine ⟨77007431645498550124160693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51338287763665700082773795 77007431645498550124160693)
                ·
                  refine ⟨7219446716765489074140065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77007431645498550124160693 7219446716765489074140065)
                  ·
                    refine ⟨5414585037574116805605049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219446716765489074140065 5414585037574116805605049)
                    ·
                      refine ⟨4060938778180587604203787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414585037574116805605049 4060938778180587604203787)
                      ·
                        rfl

theorem cell23_7908650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7908650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908650 prefixEnd_7908650 := by exact prefixLift 7908650
  have htrace : WordTrace (prefixWord ++ tailWord_7908650) baseStart_7908650 baseEnd_7908650 := by
    simpa [prefixWord, tailWord_7908650, baseEnd_7908650] using wordTrace_append hprefix tailTrace_7908650
  have hstable : (prefixWord ++ tailWord_7908650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908650).length < 2 ^ (prefixWord ++ tailWord_7908650).sum := by decide
  have hdescent : baseEnd_7908650 < baseStart_7908650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908666 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_7908666 : Nat := 118140960795 + 7908666 * 2 ^ 59
def prefixEnd_7908666 : Nat := 4983230072969 + 3 ^ 40 * 7908666 * 2
def baseEnd_7908666 : Nat := 4060946993871059541603713

theorem tailTrace_7908666 : CollatzResearch.WordTrace tailWord_7908666 prefixEnd_7908666 4060946993871059541603713 := by
  unfold tailWord_7908666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72113186591565312365944463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192301830910840832975851901 72113186591565312365944463)
  ·
    refine ⟨108169779887347968548916695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72113186591565312365944463 108169779887347968548916695)
    ·
      refine ⟨162254669831021952823375043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108169779887347968548916695 162254669831021952823375043)
      ·
        refine ⟨243382004746532929235062565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162254669831021952823375043 243382004746532929235062565)
        ·
          refine ⟨45634125889974924231574231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243382004746532929235062565 45634125889974924231574231)
          ·
            refine ⟨68451188834962386347361347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45634125889974924231574231 68451188834962386347361347)
            ·
              refine ⟨102676783252443579521042021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68451188834962386347361347 102676783252443579521042021)
              ·
                refine ⟨19251896859833171160195379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102676783252443579521042021 19251896859833171160195379)
                ·
                  refine ⟨28877845289749756740293069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19251896859833171160195379 28877845289749756740293069)
                  ·
                    refine ⟨10829191983656158777609901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28877845289749756740293069 10829191983656158777609901)
                    ·
                      refine ⟨4060946993871059541603713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829191983656158777609901 4060946993871059541603713)
                      ·
                        rfl

theorem cell23_7908666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_7908666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908666 prefixEnd_7908666 := by exact prefixLift 7908666
  have htrace : WordTrace (prefixWord ++ tailWord_7908666) baseStart_7908666 baseEnd_7908666 := by
    simpa [prefixWord, tailWord_7908666, baseEnd_7908666] using wordTrace_append hprefix tailTrace_7908666
  have hstable : (prefixWord ++ tailWord_7908666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908666).length < 2 ^ (prefixWord ++ tailWord_7908666).sum := by decide
  have hdescent : baseEnd_7908666 < baseStart_7908666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908694 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7908694 : Nat := 118140960795 + 7908694 * 2 ^ 59
def prefixEnd_7908694 : Nat := 4983230072969 + 3 ^ 40 * 7908694 * 2
def baseEnd_7908694 : Nat := 1353653790443128477351195

theorem tailTrace_7908694 : CollatzResearch.WordTrace tailWord_7908694 prefixEnd_7908694 1353653790443128477351195 := by
  unfold tailWord_7908694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18028360475634988140362321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192302511740106540163864757 18028360475634988140362321)
  ·
    refine ⟨13521270356726241105271741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18028360475634988140362321 13521270356726241105271741)
    ·
      refine ⟨5070476383772340414476903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13521270356726241105271741 5070476383772340414476903)
      ·
        refine ⟨7605714575658510621715355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070476383772340414476903 7605714575658510621715355)
        ·
          refine ⟨11408571863487765932573033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605714575658510621715355 11408571863487765932573033)
          ·
            refine ⟨8556428897615824449429775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11408571863487765932573033 8556428897615824449429775)
            ·
              refine ⟨12834643346423736674144663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556428897615824449429775 12834643346423736674144663)
              ·
                refine ⟨19251965019635605011216995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12834643346423736674144663 19251965019635605011216995)
                ·
                  refine ⟨28877947529453407516825493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19251965019635605011216995 28877947529453407516825493)
                  ·
                    refine ⟨1353653790443128477351195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28877947529453407516825493 1353653790443128477351195)
                    ·
                      rfl

theorem cell23_7908694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7908694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908694 prefixEnd_7908694 := by exact prefixLift 7908694
  have htrace : WordTrace (prefixWord ++ tailWord_7908694) baseStart_7908694 baseEnd_7908694 := by
    simpa [prefixWord, tailWord_7908694, baseEnd_7908694] using wordTrace_append hprefix tailTrace_7908694
  have hstable : (prefixWord ++ tailWord_7908694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908694).length < 2 ^ (prefixWord ++ tailWord_7908694).sum := by decide
  have hdescent : baseEnd_7908694 < baseStart_7908694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908718 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_7908718 : Nat := 118140960795 + 7908718 * 2 ^ 59
def prefixEnd_7908718 : Nat := 4983230072969 + 3 ^ 40 * 7908718 * 2
def baseEnd_7908718 : Nat := 4060973694865093338153475

theorem tailTrace_7908718 : CollatzResearch.WordTrace tailWord_7908718 prefixEnd_7908718 4060973694865093338153475 := by
  unfold tailWord_7908718
  simp only [CollatzResearch.WordTrace]
  refine ⟨36056830370259107793083851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192303095308048574896447205 36056830370259107793083851)
  ·
    refine ⟨54085245555388661689625777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36056830370259107793083851 54085245555388661689625777)
    ·
      refine ⟨40563934166541496267219333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54085245555388661689625777 40563934166541496267219333)
      ·
        refine ⟨7605737656226530550103625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40563934166541496267219333 7605737656226530550103625)
        ·
          refine ⟨5704303242169897912577719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7605737656226530550103625 5704303242169897912577719)
          ·
            refine ⟨8556454863254846868866579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704303242169897912577719 8556454863254846868866579)
            ·
              refine ⟨12834682294882270303299869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556454863254846868866579 12834682294882270303299869)
              ·
                refine ⟨4813005860580851363737451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12834682294882270303299869 4813005860580851363737451)
                ·
                  refine ⟨7219508790871277045606177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813005860580851363737451 7219508790871277045606177)
                  ·
                    refine ⟨5414631593153457784204633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219508790871277045606177 5414631593153457784204633)
                    ·
                      refine ⟨4060973694865093338153475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414631593153457784204633 4060973694865093338153475)
                      ·
                        rfl

theorem cell23_7908718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_7908718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908718 prefixEnd_7908718 := by exact prefixLift 7908718
  have htrace : WordTrace (prefixWord ++ tailWord_7908718) baseStart_7908718 baseEnd_7908718 := by
    simpa [prefixWord, tailWord_7908718, baseEnd_7908718] using wordTrace_append hprefix tailTrace_7908718
  have hstable : (prefixWord ++ tailWord_7908718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908718).length < 2 ^ (prefixWord ++ tailWord_7908718).sum := by decide
  have hdescent : baseEnd_7908718 < baseStart_7908718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908729 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 9]
def baseStart_7908729 : Nat := 118140960795 + 7908729 * 2 ^ 59
def prefixEnd_7908729 : Nat := 4983230072969 + 3 ^ 40 * 7908729 * 2
def baseEnd_7908729 : Nat := 451219927016921421679547

theorem tailTrace_7908729 : CollatzResearch.WordTrace tailWord_7908729 prefixEnd_7908729 451219927016921421679547 := by
  unfold tailWord_7908729
  simp only [CollatzResearch.WordTrace]
  refine ⟨288455044165033011223321241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192303362776688674148880827 288455044165033011223321241)
  ·
    refine ⟨216341283123774758417490931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288455044165033011223321241 216341283123774758417490931)
    ·
      refine ⟨324511924685662137626236397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216341283123774758417490931 324511924685662137626236397)
      ·
        refine ⟨121691971757123301609838649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324511924685662137626236397 121691971757123301609838649)
        ·
          refine ⟨91268978817842476207378987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121691971757123301609838649 91268978817842476207378987)
          ·
            refine ⟨136903468226763714311068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91268978817842476207378987 136903468226763714311068481)
            ·
              refine ⟨102677601170072785733301361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136903468226763714311068481 102677601170072785733301361)
              ·
                refine ⟨77008200877554589299976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102677601170072785733301361 77008200877554589299976021)
                ·
                  refine ⟨451219927016921421679547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77008200877554589299976021 451219927016921421679547)
                  ·
                    rfl

theorem cell23_7908729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_7908729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908729 prefixEnd_7908729 := by exact prefixLift 7908729
  have htrace : WordTrace (prefixWord ++ tailWord_7908729) baseStart_7908729 baseEnd_7908729 := by
    simpa [prefixWord, tailWord_7908729, baseEnd_7908729] using wordTrace_append hprefix tailTrace_7908729
  have hstable : (prefixWord ++ tailWord_7908729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908729).length < 2 ^ (prefixWord ++ tailWord_7908729).sum := by decide
  have hdescent : baseEnd_7908729 < baseStart_7908729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908740 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7908740 : Nat := 118140960795 + 7908740 * 2 ^ 59
def prefixEnd_7908740 : Nat := 4983230072969 + 3 ^ 40 * 7908740 * 2
def baseEnd_7908740 : Nat := 4060984991439492252078373

theorem tailTrace_7908740 : CollatzResearch.WordTrace tailWord_7908740 prefixEnd_7908740 4060984991439492252078373 := by
  unfold tailWord_7908740
  simp only [CollatzResearch.WordTrace]
  refine ⟨144227722683996580050985837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192303630245328773401314449 144227722683996580050985837)
  ·
    refine ⟨54085396006498717519119689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144227722683996580050985837 54085396006498717519119689)
    ·
      refine ⟨40564047004874038139339767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54085396006498717519119689 40564047004874038139339767)
      ·
        refine ⟨60846070507311057209009651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40564047004874038139339767 60846070507311057209009651)
        ·
          refine ⟨91269105760966585813514477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60846070507311057209009651 91269105760966585813514477)
          ·
            refine ⟨34225914660362469680067929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91269105760966585813514477 34225914660362469680067929)
            ·
              refine ⟨25669435995271852260050947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34225914660362469680067929 25669435995271852260050947)
              ·
                refine ⟨38504153992907778390076421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25669435995271852260050947 38504153992907778390076421)
                ·
                  refine ⟨7219528873670208448139329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38504153992907778390076421 7219528873670208448139329)
                  ·
                    refine ⟨5414646655252656336104497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219528873670208448139329 5414646655252656336104497)
                    ·
                      refine ⟨4060984991439492252078373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414646655252656336104497 4060984991439492252078373)
                      ·
                        rfl

theorem cell23_7908740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7908740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908740 prefixEnd_7908740 := by exact prefixLift 7908740
  have htrace : WordTrace (prefixWord ++ tailWord_7908740) baseStart_7908740 baseEnd_7908740 := by
    simpa [prefixWord, tailWord_7908740, baseEnd_7908740] using wordTrace_append hprefix tailTrace_7908740
  have hstable : (prefixWord ++ tailWord_7908740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908740).length < 2 ^ (prefixWord ++ tailWord_7908740).sum := by decide
  have hdescent : baseEnd_7908740 < baseStart_7908740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908757 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_7908757 : Nat := 118140960795 + 7908757 * 2 ^ 59
def prefixEnd_7908757 : Nat := 4983230072969 + 3 ^ 40 * 7908757 * 2
def baseEnd_7908757 : Nat := 4060993720610618685565795

theorem tailTrace_7908757 : CollatzResearch.WordTrace tailWord_7908757 prefixEnd_7908757 4060993720610618685565795 := by
  unfold tailWord_7908757
  simp only [CollatzResearch.WordTrace]
  refine ⟨288456065408931572005340525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192304043605954381336893683 288456065408931572005340525)
  ·
    refine ⟨108171024528349339502002697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288456065408931572005340525 108171024528349339502002697)
    ·
      refine ⟨81128268396262004626502023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108171024528349339502002697 81128268396262004626502023)
      ·
        refine ⟨121692402594393006939753035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81128268396262004626502023 121692402594393006939753035)
        ·
          refine ⟨182538603891589510409629553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121692402594393006939753035 182538603891589510409629553)
          ·
            refine ⟨136903952918692132807222165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182538603891589510409629553 136903952918692132807222165)
            ·
              refine ⟨6417372793063693725338539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136903952918692132807222165 6417372793063693725338539)
              ·
                refine ⟨9626059189595540588007809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417372793063693725338539 9626059189595540588007809)
                ·
                  refine ⟨7219544392196655441005857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9626059189595540588007809 7219544392196655441005857)
                  ·
                    refine ⟨5414658294147491580754393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219544392196655441005857 5414658294147491580754393)
                    ·
                      refine ⟨4060993720610618685565795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414658294147491580754393 4060993720610618685565795)
                      ·
                        rfl

theorem cell23_7908757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_7908757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908757 prefixEnd_7908757 := by exact prefixLift 7908757
  have htrace : WordTrace (prefixWord ++ tailWord_7908757) baseStart_7908757 baseEnd_7908757 := by
    simpa [prefixWord, tailWord_7908757, baseEnd_7908757] using wordTrace_append hprefix tailTrace_7908757
  have hstable : (prefixWord ++ tailWord_7908757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908757).length < 2 ^ (prefixWord ++ tailWord_7908757).sum := by decide
  have hdescent : baseEnd_7908757 < baseStart_7908757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908816 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_7908816 : Nat := 118140960795 + 7908816 * 2 ^ 59
def prefixEnd_7908816 : Nat := 4983230072969 + 3 ^ 40 * 7908816 * 2
def baseEnd_7908816 : Nat := 4061024015969233954728023

theorem tailTrace_7908816 : CollatzResearch.WordTrace tailWord_7908816 prefixEnd_7908816 4061024015969233954728023 := by
  unfold tailWord_7908816
  simp only [CollatzResearch.WordTrace]
  refine ⟨144229108657858912540869151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192305478210478550054492201 144229108657858912540869151)
  ·
    refine ⟨216343662986788368811303727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144229108657858912540869151 216343662986788368811303727)
    ·
      refine ⟨324515494480182553216955591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216343662986788368811303727 324515494480182553216955591)
      ·
        refine ⟨486773241720273829825433387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324515494480182553216955591 486773241720273829825433387)
        ·
          refine ⟨730159862580410744738150081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486773241720273829825433387 730159862580410744738150081)
          ·
            refine ⟨547619896935308058553612561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730159862580410744738150081 547619896935308058553612561)
            ·
              refine ⟨410714922701481043915209421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547619896935308058553612561 410714922701481043915209421)
              ·
                refine ⟨154018096013055391468203533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410714922701481043915209421 154018096013055391468203533)
                ·
                  refine ⟨57756786004895771800576325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154018096013055391468203533 57756786004895771800576325)
                  ·
                    refine ⟨10829397375917957212608061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57756786004895771800576325 10829397375917957212608061)
                    ·
                      refine ⟨4061024015969233954728023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829397375917957212608061 4061024015969233954728023)
                      ·
                        rfl

theorem cell23_7908816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_7908816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908816 prefixEnd_7908816 := by exact prefixLift 7908816
  have htrace : WordTrace (prefixWord ++ tailWord_7908816) baseStart_7908816 baseEnd_7908816 := by
    simpa [prefixWord, tailWord_7908816, baseEnd_7908816] using wordTrace_append hprefix tailTrace_7908816
  have hstable : (prefixWord ++ tailWord_7908816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908816).length < 2 ^ (prefixWord ++ tailWord_7908816).sum := by decide
  have hdescent : baseEnd_7908816 < baseStart_7908816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908833 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_7908833 : Nat := 118140960795 + 7908833 * 2 ^ 59
def prefixEnd_7908833 : Nat := 4983230072969 + 3 ^ 40 * 7908833 * 2
def baseEnd_7908833 : Nat := 4061032745140360388215445

theorem tailTrace_7908833 : CollatzResearch.WordTrace tailWord_7908833 prefixEnd_7908833 4061032745140360388215445 := by
  unfold tailWord_7908833
  simp only [CollatzResearch.WordTrace]
  refine ⟨288458837356656236985107153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192305891571104157990071435 288458837356656236985107153)
  ·
    refine ⟨216344128017492177738830365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288458837356656236985107153 216344128017492177738830365)
    ·
      refine ⟨81129048006559566652061387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216344128017492177738830365 81129048006559566652061387)
      ·
        refine ⟨121693572009839349978092081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81129048006559566652061387 121693572009839349978092081)
        ·
          refine ⟨91270179007379512483569061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121693572009839349978092081 91270179007379512483569061)
          ·
            refine ⟨17113158563883658590669199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91270179007379512483569061 17113158563883658590669199)
            ·
              refine ⟨25669737845825487886003799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17113158563883658590669199 25669737845825487886003799)
              ·
                refine ⟨38504606768738231829005699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25669737845825487886003799 38504606768738231829005699)
                ·
                  refine ⟨57756910153107347743508549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38504606768738231829005699 57756910153107347743508549)
                  ·
                    refine ⟨10829420653707627701907853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57756910153107347743508549 10829420653707627701907853)
                    ·
                      refine ⟨4061032745140360388215445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829420653707627701907853 4061032745140360388215445)
                      ·
                        rfl

theorem cell23_7908833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_7908833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908833 prefixEnd_7908833 := by exact prefixLift 7908833
  have htrace : WordTrace (prefixWord ++ tailWord_7908833) baseStart_7908833 baseEnd_7908833 := by
    simpa [prefixWord, tailWord_7908833, baseEnd_7908833] using wordTrace_append hprefix tailTrace_7908833
  have hstable : (prefixWord ++ tailWord_7908833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908833).length < 2 ^ (prefixWord ++ tailWord_7908833).sum := by decide
  have hdescent : baseEnd_7908833 < baseStart_7908833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908856 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_7908856 : Nat := 118140960795 + 7908856 * 2 ^ 59
def prefixEnd_7908856 : Nat := 4983230072969 + 3 ^ 40 * 7908856 * 2
def baseEnd_7908856 : Nat := 4061044555195413798227839

theorem tailTrace_7908856 : CollatzResearch.WordTrace tailWord_7908856 prefixEnd_7908856 4061044555195413798227839 := by
  unfold tailWord_7908856
  simp only [CollatzResearch.WordTrace]
  refine ⟨144229838117786455956597211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192306450823715274608796281 144229838117786455956597211)
  ·
    refine ⟨216344757176679683934895817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144229838117786455956597211 216344757176679683934895817)
    ·
      refine ⟨162258567882509762951171863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216344757176679683934895817 162258567882509762951171863)
      ·
        refine ⟨243387851823764644426757795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162258567882509762951171863 243387851823764644426757795)
        ·
          refine ⟨365081777735646966640136693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243387851823764644426757795 365081777735646966640136693)
          ·
            refine ⟨34226416662716903122512815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365081777735646966640136693 34226416662716903122512815)
            ·
              refine ⟨51339624994075354683769223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34226416662716903122512815 51339624994075354683769223)
              ·
                refine ⟨77009437491113032025653835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51339624994075354683769223 77009437491113032025653835)
                ·
                  refine ⟨115514156236669548038480753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77009437491113032025653835 115514156236669548038480753)
                  ·
                    refine ⟨86635617177502161028860565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115514156236669548038480753 86635617177502161028860565)
                    ·
                      refine ⟨4061044555195413798227839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86635617177502161028860565 4061044555195413798227839)
                      ·
                        rfl

theorem cell23_7908856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_7908856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908856 prefixEnd_7908856 := by exact prefixLift 7908856
  have htrace : WordTrace (prefixWord ++ tailWord_7908856) baseStart_7908856 baseEnd_7908856 := by
    simpa [prefixWord, tailWord_7908856, baseEnd_7908856] using wordTrace_append hprefix tailTrace_7908856
  have hstable : (prefixWord ++ tailWord_7908856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908856).length < 2 ^ (prefixWord ++ tailWord_7908856).sum := by decide
  have hdescent : baseEnd_7908856 < baseStart_7908856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908873 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 5, 2]
def baseStart_7908873 : Nat := 118140960795 + 7908873 * 2 ^ 59
def prefixEnd_7908873 : Nat := 4983230072969 + 3 ^ 40 * 7908873 * 2
def baseEnd_7908873 : Nat := 4061053284366540231715261

theorem tailTrace_7908873 : CollatzResearch.WordTrace tailWord_7908873 prefixEnd_7908873 4061053284366540231715261 := by
  unfold tailWord_7908873
  simp only [CollatzResearch.WordTrace]
  refine ⟨288460296276511323816563273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192306864184340882544375515 288460296276511323816563273)
  ·
    refine ⟨216345222207383492862422455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288460296276511323816563273 216345222207383492862422455)
    ·
      refine ⟨324517833311075239293633683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216345222207383492862422455 324517833311075239293633683)
      ·
        refine ⟨486776749966612858940450525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324517833311075239293633683 486776749966612858940450525)
        ·
          refine ⟨182541281237479822102668947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486776749966612858940450525 182541281237479822102668947)
          ·
            refine ⟨273811921856219733154003421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182541281237479822102668947 273811921856219733154003421)
            ·
              refine ⟨102679470696082399932751283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273811921856219733154003421 102679470696082399932751283)
              ·
                refine ⟨154019206044123599899126925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102679470696082399932751283 154019206044123599899126925)
                ·
                  refine ⟨57757202266546349962172597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154019206044123599899126925 57757202266546349962172597)
                  ·
                    refine ⟨5414737712488720308953681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57757202266546349962172597 5414737712488720308953681)
                    ·
                      refine ⟨4061053284366540231715261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414737712488720308953681 4061053284366540231715261)
                      ·
                        rfl

theorem cell23_7908873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 5, 2].length) (baseStart_7908873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908873 prefixEnd_7908873 := by exact prefixLift 7908873
  have htrace : WordTrace (prefixWord ++ tailWord_7908873) baseStart_7908873 baseEnd_7908873 := by
    simpa [prefixWord, tailWord_7908873, baseEnd_7908873] using wordTrace_append hprefix tailTrace_7908873
  have hstable : (prefixWord ++ tailWord_7908873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908873).length < 2 ^ (prefixWord ++ tailWord_7908873).sum := by decide
  have hdescent : baseEnd_7908873 < baseStart_7908873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908883 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 1, 5]
def baseStart_7908883 : Nat := 118140960795 + 7908883 * 2 ^ 59
def prefixEnd_7908883 : Nat := 4983230072969 + 3 ^ 40 * 7908883 * 2
def baseEnd_7908883 : Nat := 1353686139724361730863405

theorem tailTrace_7908883 : CollatzResearch.WordTrace tailWord_7908883 prefixEnd_7908883 1353686139724361730863405 := by
  unfold tailWord_7908883
  simp only [CollatzResearch.WordTrace]
  refine ⟨288460661006475095524427303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192307107337650063682951535 288460661006475095524427303)
  ·
    refine ⟨432690991509712643286640955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288460661006475095524427303 432690991509712643286640955)
    ·
      refine ⟨649036487264568964929961433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432690991509712643286640955 649036487264568964929961433)
      ·
        refine ⟨486777365448426723697471075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649036487264568964929961433 486777365448426723697471075)
        ·
          refine ⟨730166048172640085546206613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486777365448426723697471075 730166048172640085546206613)
          ·
            refine ⟨34226533508092504009978435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 730166048172640085546206613 34226533508092504009978435)
            ·
              refine ⟨51339800262138756014967653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34226533508092504009978435 51339800262138756014967653)
              ·
                refine ⟨9626212549151016752806435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51339800262138756014967653 9626212549151016752806435)
                ·
                  refine ⟨14439318823726525129209653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626212549151016752806435 14439318823726525129209653)
                  ·
                    refine ⟨1353686139724361730863405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14439318823726525129209653 1353686139724361730863405)
                    ·
                      rfl

theorem cell23_7908883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 5].length) (baseStart_7908883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908883 prefixEnd_7908883 := by exact prefixLift 7908883
  have htrace : WordTrace (prefixWord ++ tailWord_7908883) baseStart_7908883 baseEnd_7908883 := by
    simpa [prefixWord, tailWord_7908883, baseEnd_7908883] using wordTrace_append hprefix tailTrace_7908883
  have hstable : (prefixWord ++ tailWord_7908883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908883).length < 2 ^ (prefixWord ++ tailWord_7908883).sum := by decide
  have hdescent : baseEnd_7908883 < baseStart_7908883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908890 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_7908890 : Nat := 118140960795 + 7908890 * 2 ^ 59
def prefixEnd_7908890 : Nat := 4983230072969 + 3 ^ 40 * 7908890 * 2
def baseEnd_7908890 : Nat := 4061062013537666665202683

theorem tailTrace_7908890 : CollatzResearch.WordTrace tailWord_7908890 prefixEnd_7908890 4061062013537666665202683 := by
  unfold tailWord_7908890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72115229079362433929983031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192307277544966490479954749 72115229079362433929983031)
  ·
    refine ⟨108172843619043650894974547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72115229079362433929983031 108172843619043650894974547)
    ·
      refine ⟨162259265428565476342461821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108172843619043650894974547 162259265428565476342461821)
      ·
        refine ⟨60847224535712053628423183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162259265428565476342461821 60847224535712053628423183)
        ·
          refine ⟨91270836803568080442634775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60847224535712053628423183 91270836803568080442634775)
          ·
            refine ⟨136906255205352120663952163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91270836803568080442634775 136906255205352120663952163)
            ·
              refine ⟨205359382808028180995928245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136906255205352120663952163 205359382808028180995928245)
              ·
                refine ⟨19252442138252641968368273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205359382808028180995928245 19252442138252641968368273)
                ·
                  refine ⟨14439331603689481476276205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19252442138252641968368273 14439331603689481476276205)
                  ·
                    refine ⟨5414749351383555553603577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14439331603689481476276205 5414749351383555553603577)
                    ·
                      refine ⟨4061062013537666665202683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414749351383555553603577 4061062013537666665202683)
                      ·
                        rfl

theorem cell23_7908890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_7908890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908890 prefixEnd_7908890 := by exact prefixLift 7908890
  have htrace : WordTrace (prefixWord ++ tailWord_7908890) baseStart_7908890 baseEnd_7908890 := by
    simpa [prefixWord, tailWord_7908890, baseEnd_7908890] using wordTrace_append hprefix tailTrace_7908890
  have hstable : (prefixWord ++ tailWord_7908890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908890).length < 2 ^ (prefixWord ++ tailWord_7908890).sum := by decide
  have hdescent : baseEnd_7908890 < baseStart_7908890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908933 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_7908933 : Nat := 118140960795 + 7908933 * 2 ^ 59
def prefixEnd_7908933 : Nat := 4983230072969 + 3 ^ 40 * 7908933 * 2
def baseEnd_7908933 : Nat := 4061084093205809996964985

theorem tailTrace_7908933 : CollatzResearch.WordTrace tailWord_7908933 prefixEnd_7908933 4061084093205809996964985 := by
  unfold tailWord_7908933
  simp only [CollatzResearch.WordTrace]
  refine ⟨288462484656293954063747453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192308323104195969375831635 288462484656293954063747453)
  ·
    refine ⟨108173431746110232773905295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288462484656293954063747453 108173431746110232773905295)
    ·
      refine ⟨162260147619165349160857943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108173431746110232773905295 162260147619165349160857943)
      ·
        refine ⟨243390221428748023741286915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162260147619165349160857943 243390221428748023741286915)
        ·
          refine ⟨365085332143122035611930373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243390221428748023741286915 365085332143122035611930373)
          ·
            refine ⟨68453499776835381677236945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365085332143122035611930373 68453499776835381677236945)
            ·
              refine ⟨51340124832626536257927709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68453499776835381677236945 51340124832626536257927709)
              ·
                refine ⟨19252546812234951096722891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51340124832626536257927709 19252546812234951096722891)
                ·
                  refine ⟨28878820218352426645084337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252546812234951096722891 28878820218352426645084337)
                  ·
                    refine ⟨21659115163764319983813253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28878820218352426645084337 21659115163764319983813253)
                    ·
                      refine ⟨4061084093205809996964985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21659115163764319983813253 4061084093205809996964985)
                      ·
                        rfl

theorem cell23_7908933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_7908933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908933 prefixEnd_7908933 := by exact prefixLift 7908933
  have htrace : WordTrace (prefixWord ++ tailWord_7908933) baseStart_7908933 baseEnd_7908933 := by
    simpa [prefixWord, tailWord_7908933, baseEnd_7908933] using wordTrace_append hprefix tailTrace_7908933
  have hstable : (prefixWord ++ tailWord_7908933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908933).length < 2 ^ (prefixWord ++ tailWord_7908933).sum := by decide
  have hdescent : baseEnd_7908933 < baseStart_7908933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908940 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_7908940 : Nat := 118140960795 + 7908940 * 2 ^ 59
def prefixEnd_7908940 : Nat := 4983230072969 + 3 ^ 40 * 7908940 * 2
def baseEnd_7908940 : Nat := 4061087687570391469577453

theorem tailTrace_7908940 : CollatzResearch.WordTrace tailWord_7908940 prefixEnd_7908940 4061087687570391469577453 := by
  unfold tailWord_7908940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144231369983634297129626137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192308493311512396172834849 144231369983634297129626137)
  ·
    refine ⟨108173527487725722847219603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144231369983634297129626137 108173527487725722847219603)
    ·
      refine ⟨162260291231588584270829405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108173527487725722847219603 162260291231588584270829405)
      ·
        refine ⟨60847609211845719101561027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162260291231588584270829405 60847609211845719101561027)
        ·
          refine ⟨91271413817768578652341541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60847609211845719101561027 91271413817768578652341541)
          ·
            refine ⟨17113390090831608497314039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91271413817768578652341541 17113390090831608497314039)
            ·
              refine ⟨25670085136247412745971059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17113390090831608497314039 25670085136247412745971059)
              ·
                refine ⟨38505127704371119118956589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25670085136247412745971059 38505127704371119118956589)
                ·
                  refine ⟨14439422889139169669608721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38505127704371119118956589 14439422889139169669608721)
                  ·
                    refine ⟨10829567166854377252206541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14439422889139169669608721 10829567166854377252206541)
                    ·
                      refine ⟨4061087687570391469577453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829567166854377252206541 4061087687570391469577453)
                      ·
                        rfl

theorem cell23_7908940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_7908940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908940 prefixEnd_7908940 := by exact prefixLift 7908940
  have htrace : WordTrace (prefixWord ++ tailWord_7908940) baseStart_7908940 baseEnd_7908940 := by
    simpa [prefixWord, tailWord_7908940, baseEnd_7908940] using wordTrace_append hprefix tailTrace_7908940
  have hstable : (prefixWord ++ tailWord_7908940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908940).length < 2 ^ (prefixWord ++ tailWord_7908940).sum := by decide
  have hdescent : baseEnd_7908940 < baseStart_7908940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7908997 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_7908997 : Nat := 118140960795 + 7908997 * 2 ^ 59
def prefixEnd_7908997 : Nat := 4983230072969 + 3 ^ 40 * 7908997 * 2
def baseEnd_7908997 : Nat := 4061116955967697746564691

theorem tailTrace_7908997 : CollatzResearch.WordTrace tailWord_7908997 prefixEnd_7908997 4061116955967697746564691 := by
  unfold tailWord_7908997
  simp only [CollatzResearch.WordTrace]
  refine ⟨288464818928062092994077245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192309879285374728662718163 288464818928062092994077245)
  ·
    refine ⟨108174307098023284872778967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288464818928062092994077245 108174307098023284872778967)
    ·
      refine ⟨162261460647034927309168451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108174307098023284872778967 162261460647034927309168451)
      ·
        refine ⟨243392190970552390963752677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162261460647034927309168451 243392190970552390963752677)
        ·
          refine ⟨45636035806978573305703627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243392190970552390963752677 45636035806978573305703627)
          ·
            refine ⟨68454053710467859958555441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45636035806978573305703627 68454053710467859958555441)
            ·
              refine ⟨51340540282850894968916581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68454053710467859958555441 51340540282850894968916581)
              ·
                refine ⟨9626351303034542806671859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51340540282850894968916581 9626351303034542806671859)
                ·
                  refine ⟨14439526954551814210007789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626351303034542806671859 14439526954551814210007789)
                  ·
                    refine ⟨5414822607956930328752921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14439526954551814210007789 5414822607956930328752921)
                    ·
                      refine ⟨4061116955967697746564691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414822607956930328752921 4061116955967697746564691)
                      ·
                        rfl

theorem cell23_7908997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_7908997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7908997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7908997 prefixEnd_7908997 := by exact prefixLift 7908997
  have htrace : WordTrace (prefixWord ++ tailWord_7908997) baseStart_7908997 baseEnd_7908997 := by
    simpa [prefixWord, tailWord_7908997, baseEnd_7908997] using wordTrace_append hprefix tailTrace_7908997
  have hstable : (prefixWord ++ tailWord_7908997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7908997).length < 2 ^ (prefixWord ++ tailWord_7908997).sum := by decide
  have hdescent : baseEnd_7908997 < baseStart_7908997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7908997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909013 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7909013 : Nat := 118140960795 + 7909013 * 2 ^ 59
def prefixEnd_7909013 : Nat := 4983230072969 + 3 ^ 40 * 7909013 * 2
def baseEnd_7909013 : Nat := 4061125171658169683964617

theorem tailTrace_7909013 : CollatzResearch.WordTrace tailWord_7909013 prefixEnd_7909013 4061125171658169683964617 := by
  unfold tailWord_7909013
  simp only [CollatzResearch.WordTrace]
  refine ⟨288465402496004127726659693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192310268330669418484439795 288465402496004127726659693)
  ·
    refine ⟨108174525936001547897497385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288465402496004127726659693 108174525936001547897497385)
    ·
      refine ⟨81130894452001160923123039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108174525936001547897497385 81130894452001160923123039)
      ·
        refine ⟨121696341678001741384684559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81130894452001160923123039 121696341678001741384684559)
        ·
          refine ⟨182544512517002612077026839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121696341678001741384684559 182544512517002612077026839)
          ·
            refine ⟨273816768775503918115540259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182544512517002612077026839 273816768775503918115540259)
            ·
              refine ⟨410725153163255877173310389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273816768775503918115540259 410725153163255877173310389)
              ·
                refine ⟨38505483109055238484997849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410725153163255877173310389 38505483109055238484997849)
                ·
                  refine ⟨28879112331791428863748387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38505483109055238484997849 28879112331791428863748387)
                  ·
                    refine ⟨43318668497687143295622581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28879112331791428863748387 43318668497687143295622581)
                    ·
                      refine ⟨4061125171658169683964617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43318668497687143295622581 4061125171658169683964617)
                      ·
                        rfl

theorem cell23_7909013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7909013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909013 prefixEnd_7909013 := by exact prefixLift 7909013
  have htrace : WordTrace (prefixWord ++ tailWord_7909013) baseStart_7909013 baseEnd_7909013 := by
    simpa [prefixWord, tailWord_7909013, baseEnd_7909013] using wordTrace_append hprefix tailTrace_7909013
  have hstable : (prefixWord ++ tailWord_7909013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909013).length < 2 ^ (prefixWord ++ tailWord_7909013).sum := by decide
  have hdescent : baseEnd_7909013 < baseStart_7909013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909027 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 4, 2, 2]
def baseStart_7909027 : Nat := 118140960795 + 7909027 * 2 ^ 59
def prefixEnd_7909027 : Nat := 4983230072969 + 3 ^ 40 * 7909027 * 2
def baseEnd_7909027 : Nat := 4061132360387332629189553

theorem tailTrace_7909027 : CollatzResearch.WordTrace tailWord_7909027 prefixEnd_7909027 4061132360387332629189553 := by
  unfold tailWord_7909027
  simp only [CollatzResearch.WordTrace]
  refine ⟨288465913117953408117669335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192310608745302272078446223 288465913117953408117669335)
  ·
    refine ⟨432698869676930112176504003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288465913117953408117669335 432698869676930112176504003)
    ·
      refine ⟨649048304515395168264756005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432698869676930112176504003 649048304515395168264756005)
      ·
        refine ⟨121696557096636594049641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649048304515395168264756005 121696557096636594049641751)
        ·
          refine ⟨182544835644954891074462627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121696557096636594049641751 182544835644954891074462627)
          ·
            refine ⟨273817253467432336611693941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182544835644954891074462627 273817253467432336611693941)
            ·
              refine ⟨25670367512571781557346307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273817253467432336611693941 25670367512571781557346307)
              ·
                refine ⟨38505551268857672336019461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25670367512571781557346307 38505551268857672336019461)
                ·
                  refine ⟨7219790862910813563003649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38505551268857672336019461 7219790862910813563003649)
                  ·
                    refine ⟨5414843147183110172252737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219790862910813563003649 5414843147183110172252737)
                    ·
                      refine ⟨4061132360387332629189553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414843147183110172252737 4061132360387332629189553)
                      ·
                        rfl

theorem cell23_7909027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_7909027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909027 prefixEnd_7909027 := by exact prefixLift 7909027
  have htrace : WordTrace (prefixWord ++ tailWord_7909027) baseStart_7909027 baseEnd_7909027 := by
    simpa [prefixWord, tailWord_7909027, baseEnd_7909027] using wordTrace_append hprefix tailTrace_7909027
  have hstable : (prefixWord ++ tailWord_7909027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909027).length < 2 ^ (prefixWord ++ tailWord_7909027).sum := by decide
  have hdescent : baseEnd_7909027 < baseStart_7909027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909038 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7909038 : Nat := 118140960795 + 7909038 * 2 ^ 59
def prefixEnd_7909038 : Nat := 4983230072969 + 3 ^ 40 * 7909038 * 2
def baseEnd_7909038 : Nat := 4061138008674532086152003

theorem tailTrace_7909038 : CollatzResearch.WordTrace tailWord_7909038 prefixEnd_7909038 4061138008674532086152003 := by
  unfold tailWord_7909038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36058289290114194624539971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192310876213942371330879845 36058289290114194624539971)
  ·
    refine ⟨54087433935171291936809957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36058289290114194624539971 54087433935171291936809957)
    ·
      refine ⟨10141393862844617238151867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54087433935171291936809957 10141393862844617238151867)
      ·
        refine ⟨15212090794266925857227801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141393862844617238151867 15212090794266925857227801)
        ·
          refine ⟨11409068095700194392920851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15212090794266925857227801 11409068095700194392920851)
          ·
            refine ⟨17113602143550291589381277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409068095700194392920851 17113602143550291589381277)
            ·
              refine ⟨6417600803831359346017979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17113602143550291589381277 6417600803831359346017979)
              ·
                refine ⟨9626401205747039019026969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417600803831359346017979 9626401205747039019026969)
                ·
                  refine ⟨7219800904310279264270227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9626401205747039019026969 7219800904310279264270227)
                  ·
                    refine ⟨10829701356465418896405341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219800904310279264270227 10829701356465418896405341)
                    ·
                      refine ⟨4061138008674532086152003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829701356465418896405341 4061138008674532086152003)
                      ·
                        rfl

theorem cell23_7909038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7909038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909038 prefixEnd_7909038 := by exact prefixLift 7909038
  have htrace : WordTrace (prefixWord ++ tailWord_7909038) baseStart_7909038 baseEnd_7909038 := by
    simpa [prefixWord, tailWord_7909038, baseEnd_7909038] using wordTrace_append hprefix tailTrace_7909038
  have hstable : (prefixWord ++ tailWord_7909038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909038).length < 2 ^ (prefixWord ++ tailWord_7909038).sum := by decide
  have hdescent : baseEnd_7909038 < baseStart_7909038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909063 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 7]
def baseStart_7909063 : Nat := 118140960795 + 7909063 * 2 ^ 59
def prefixEnd_7909063 : Nat := 4983230072969 + 3 ^ 40 * 7909063 * 2
def baseEnd_7909063 : Nat := 1353716948563631496113129

theorem tailTrace_7909063 : CollatzResearch.WordTrace tailWord_7909063 prefixEnd_7909063 1353716948563631496113129 := by
  unfold tailWord_7909063
  simp only [CollatzResearch.WordTrace]
  refine ⟨288467226145822986265979843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192311484097215324177319895 288467226145822986265979843)
  ·
    refine ⟨432700839218734479398969765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288467226145822986265979843 432700839218734479398969765)
    ·
      refine ⟨81131407353512714887306831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432700839218734479398969765 81131407353512714887306831)
      ·
        refine ⟨121697111030269072330960247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81131407353512714887306831 121697111030269072330960247)
        ·
          refine ⟨182545666545403608496440371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121697111030269072330960247 182545666545403608496440371)
          ·
            refine ⟨273818499818105412744660557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182545666545403608496440371 273818499818105412744660557)
            ·
              refine ⟨102681937431789529779247709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273818499818105412744660557 102681937431789529779247709)
              ·
                refine ⟨38505726536921073667217891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102681937431789529779247709 38505726536921073667217891)
                ·
                  refine ⟨57758589805381610500826837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38505726536921073667217891 57758589805381610500826837)
                  ·
                    refine ⟨1353716948563631496113129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57758589805381610500826837 1353716948563631496113129)
                    ·
                      rfl

theorem cell23_7909063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_7909063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909063 prefixEnd_7909063 := by exact prefixLift 7909063
  have htrace : WordTrace (prefixWord ++ tailWord_7909063) baseStart_7909063 baseEnd_7909063 := by
    simpa [prefixWord, tailWord_7909063, baseEnd_7909063] using wordTrace_append hprefix tailTrace_7909063
  have hstable : (prefixWord ++ tailWord_7909063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909063).length < 2 ^ (prefixWord ++ tailWord_7909063).sum := by decide
  have hdescent : baseEnd_7909063 < baseStart_7909063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909080 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_7909080 : Nat := 118140960795 + 7909080 * 2 ^ 59
def prefixEnd_7909080 : Nat := 4983230072969 + 3 ^ 40 * 7909080 * 2
def baseEnd_7909080 : Nat := 1353719858287340307275603

theorem tailTrace_7909080 : CollatzResearch.WordTrace tailWord_7909080 prefixEnd_7909080 1353719858287340307275603 := by
  unfold tailWord_7909080
  simp only [CollatzResearch.WordTrace]
  refine ⟨144233923093380699084674347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192311897457840932112899129 144233923093380699084674347)
  ·
    refine ⟨216350884640071048627011521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144233923093380699084674347 216350884640071048627011521)
    ·
      refine ⟨162263163480053286470258641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216350884640071048627011521 162263163480053286470258641)
      ·
        refine ⟨121697372610039964852693981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162263163480053286470258641 121697372610039964852693981)
        ·
          refine ⟨45636514728764986819760243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121697372610039964852693981 45636514728764986819760243)
          ·
            refine ⟨68454772093147480229640365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45636514728764986819760243 68454772093147480229640365)
            ·
              refine ⟨25670539534930305086115137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68454772093147480229640365 25670539534930305086115137)
              ·
                refine ⟨19252904651197728814586353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25670539534930305086115137 19252904651197728814586353)
                ·
                  refine ⟨14439678488398296610939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19252904651197728814586353 14439678488398296610939765)
                  ·
                    refine ⟨1353719858287340307275603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14439678488398296610939765 1353719858287340307275603)
                    ·
                      rfl

theorem cell23_7909080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_7909080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909080 prefixEnd_7909080 := by exact prefixLift 7909080
  have htrace : WordTrace (prefixWord ++ tailWord_7909080) baseStart_7909080 baseEnd_7909080 := by
    simpa [prefixWord, tailWord_7909080, baseEnd_7909080] using wordTrace_append hprefix tailTrace_7909080
  have hstable : (prefixWord ++ tailWord_7909080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909080).length < 2 ^ (prefixWord ++ tailWord_7909080).sum := by decide
  have hdescent : baseEnd_7909080 < baseStart_7909080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909084 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 7]
def baseStart_7909084 : Nat := 118140960795 + 7909084 * 2 ^ 59
def prefixEnd_7909084 : Nat := 4983230072969 + 3 ^ 40 * 7909084 * 2
def baseEnd_7909084 : Nat := 451240180976070989575199

theorem tailTrace_7909084 : CollatzResearch.WordTrace tailWord_7909084 prefixEnd_7909084 451240180976070989575199 := by
  unfold tailWord_7909084
  simp only [CollatzResearch.WordTrace]
  refine ⟨144233996039373453426247153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192311994719164604568329537 144233996039373453426247153)
  ·
    refine ⟨108175497029530090069685365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144233996039373453426247153 108175497029530090069685365)
    ·
      refine ⟨10141452846518445944033003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108175497029530090069685365 10141452846518445944033003)
      ·
        refine ⟨15212179269777668916049505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141452846518445944033003 15212179269777668916049505)
        ·
          refine ⟨11409134452333251687037129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15212179269777668916049505 11409134452333251687037129)
          ·
            refine ⟨8556850839249938765277847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11409134452333251687037129 8556850839249938765277847)
            ·
              refine ⟨12835276258874908147916771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556850839249938765277847 12835276258874908147916771)
              ·
                refine ⟨19252914388312362221875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835276258874908147916771 19252914388312362221875157)
                ·
                  refine ⟨451240180976070989575199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19252914388312362221875157 451240180976070989575199)
                  ·
                    rfl

theorem cell23_7909084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_7909084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909084 prefixEnd_7909084 := by exact prefixLift 7909084
  have htrace : WordTrace (prefixWord ++ tailWord_7909084) baseStart_7909084 baseEnd_7909084 := by
    simpa [prefixWord, tailWord_7909084, baseEnd_7909084] using wordTrace_append hprefix tailTrace_7909084
  have hstable : (prefixWord ++ tailWord_7909084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909084).length < 2 ^ (prefixWord ++ tailWord_7909084).sum := by decide
  have hdescent : baseEnd_7909084 < baseStart_7909084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909095 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7909095 : Nat := 118140960795 + 7909095 * 2 ^ 59
def prefixEnd_7909095 : Nat := 4983230072969 + 3 ^ 40 * 7909095 * 2
def baseEnd_7909095 : Nat := 4061167277071838363139241

theorem tailTrace_7909095 : CollatzResearch.WordTrace tailWord_7909095 prefixEnd_7909095 4061167277071838363139241 := by
  unfold tailWord_7909095
  simp only [CollatzResearch.WordTrace]
  refine ⟨288468393281707055731144739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192312262187804703820763159 288468393281707055731144739)
  ·
    refine ⟨432702589922560583596717109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288468393281707055731144739 432702589922560583596717109)
    ·
      refine ⟨40565867805240054712192229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432702589922560583596717109 40565867805240054712192229)
      ·
        refine ⟨7606100213482510258536043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40565867805240054712192229 7606100213482510258536043)
        ·
          refine ⟨11409150320223765387804065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606100213482510258536043 11409150320223765387804065)
          ·
            refine ⟨8556862740167824040853049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11409150320223765387804065 8556862740167824040853049)
            ·
              refine ⟨6417647055125868030639787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556862740167824040853049 6417647055125868030639787)
              ·
                refine ⟨9626470582688802045959681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417647055125868030639787 9626470582688802045959681)
                ·
                  refine ⟨7219852937016601534469761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9626470582688802045959681 7219852937016601534469761)
                  ·
                    refine ⟨5414889702762451150852321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219852937016601534469761 5414889702762451150852321)
                    ·
                      refine ⟨4061167277071838363139241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5414889702762451150852321 4061167277071838363139241)
                      ·
                        rfl

theorem cell23_7909095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7909095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909095 prefixEnd_7909095 := by exact prefixLift 7909095
  have htrace : WordTrace (prefixWord ++ tailWord_7909095) baseStart_7909095 baseEnd_7909095 := by
    simpa [prefixWord, tailWord_7909095, baseEnd_7909095] using wordTrace_append hprefix tailTrace_7909095
  have hstable : (prefixWord ++ tailWord_7909095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909095).length < 2 ^ (prefixWord ++ tailWord_7909095).sum := by decide
  have hdescent : baseEnd_7909095 < baseStart_7909095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909113 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7909113 : Nat := 118140960795 + 7909113 * 2 ^ 59
def prefixEnd_7909113 : Nat := 4983230072969 + 3 ^ 40 * 7909113 * 2
def baseEnd_7909113 : Nat := 4061176519723619292714157

theorem tailTrace_7909113 : CollatzResearch.WordTrace tailWord_7909113 prefixEnd_7909113 4061176519723619292714157 := by
  unfold tailWord_7909113
  simp only [CollatzResearch.WordTrace]
  refine ⟨288469049795641844805299993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192312699863761229870199995 288469049795641844805299993)
  ·
    refine ⟨216351787346731383603974995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288469049795641844805299993 216351787346731383603974995)
    ·
      refine ⟨324527681020097075405962493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216351787346731383603974995 324527681020097075405962493)
      ·
        refine ⟨121697880382536403277235935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324527681020097075405962493 121697880382536403277235935)
        ·
          refine ⟨182546820573804604915853903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121697880382536403277235935 182546820573804604915853903)
          ·
            refine ⟨273820230860706907373780855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182546820573804604915853903 273820230860706907373780855)
            ·
              refine ⟨410730346291060361060671283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273820230860706907373780855 410730346291060361060671283)
              ·
                refine ⟨616095519436590541591006925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410730346291060361060671283 616095519436590541591006925)
                ·
                  refine ⟨231035819788721453096627597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616095519436590541591006925 231035819788721453096627597)
                  ·
                    refine ⟨86638432420770544911235349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231035819788721453096627597 86638432420770544911235349)
                    ·
                      refine ⟨4061176519723619292714157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86638432420770544911235349 4061176519723619292714157)
                      ·
                        rfl

theorem cell23_7909113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7909113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909113 prefixEnd_7909113 := by exact prefixLift 7909113
  have htrace : WordTrace (prefixWord ++ tailWord_7909113) baseStart_7909113 baseEnd_7909113 := by
    simpa [prefixWord, tailWord_7909113, baseEnd_7909113] using wordTrace_append hprefix tailTrace_7909113
  have hstable : (prefixWord ++ tailWord_7909113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909113).length < 2 ^ (prefixWord ++ tailWord_7909113).sum := by decide
  have hdescent : baseEnd_7909113 < baseStart_7909113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909120 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_7909120 : Nat := 118140960795 + 7909120 * 2 ^ 59
def prefixEnd_7909120 : Nat := 4983230072969 + 3 ^ 40 * 7909120 * 2
def baseEnd_7909120 : Nat := 4061180114088200765326625

theorem tailTrace_7909120 : CollatzResearch.WordTrace tailWord_7909120 prefixEnd_7909120 4061180114088200765326625 := by
  unfold tailWord_7909120
  simp only [CollatzResearch.WordTrace]
  refine ⟨144234652553308242500402407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192312870071077656667203209 144234652553308242500402407)
  ·
    refine ⟨216351978829962363750603611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144234652553308242500402407 216351978829962363750603611)
    ·
      refine ⟨324527968244943545625905417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216351978829962363750603611 324527968244943545625905417)
      ·
        refine ⟨243395976183707659219429063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324527968244943545625905417 243395976183707659219429063)
        ·
          refine ⟨365093964275561488829143595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243395976183707659219429063 365093964275561488829143595)
          ·
            refine ⟨547640946413342233243715393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365093964275561488829143595 547640946413342233243715393)
            ·
              refine ⟨410730709810006674932786545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547640946413342233243715393 410730709810006674932786545)
              ·
                refine ⟨308048032357505006199589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410730709810006674932786545 308048032357505006199589909)
                ·
                  refine ⟨14439751516758047165605777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 308048032357505006199589909 14439751516758047165605777)
                  ·
                    refine ⟨10829813637568535374204333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14439751516758047165605777 10829813637568535374204333)
                    ·
                      refine ⟨4061180114088200765326625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829813637568535374204333 4061180114088200765326625)
                      ·
                        rfl

theorem cell23_7909120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_7909120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909120 prefixEnd_7909120 := by exact prefixLift 7909120
  have htrace : WordTrace (prefixWord ++ tailWord_7909120) baseStart_7909120 baseEnd_7909120 := by
    simpa [prefixWord, tailWord_7909120, baseEnd_7909120] using wordTrace_append hprefix tailTrace_7909120
  have hstable : (prefixWord ++ tailWord_7909120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909120).length < 2 ^ (prefixWord ++ tailWord_7909120).sum := by decide
  have hdescent : baseEnd_7909120 < baseStart_7909120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909123 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 10]
def baseStart_7909123 : Nat := 118140960795 + 7909123 * 2 ^ 59
def prefixEnd_7909123 : Nat := 4983230072969 + 3 ^ 40 * 7909123 * 2
def baseEnd_7909123 : Nat := 451242406058907139287679

theorem tailTrace_7909123 : CollatzResearch.WordTrace tailWord_7909123 prefixEnd_7909123 451242406058907139287679 := by
  unfold tailWord_7909123
  simp only [CollatzResearch.WordTrace]
  refine ⟨288469414525605616513164023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192312943017070411008776015 288469414525605616513164023)
  ·
    refine ⟨432704121788408424769746035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288469414525605616513164023 432704121788408424769746035)
    ·
      refine ⟨649056182682612637154619053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432704121788408424769746035 649056182682612637154619053)
      ·
        refine ⟨243396068505979738932982145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649056182682612637154619053 243396068505979738932982145)
        ·
          refine ⟨182547051379484804199736609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243396068505979738932982145 182547051379484804199736609)
          ·
            refine ⟨136910288534613603149802457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182547051379484804199736609 136910288534613603149802457)
            ·
              refine ⟨102682716400960202362351843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136910288534613603149802457 102682716400960202362351843)
              ·
                refine ⟨154024074601440303543527765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102682716400960202362351843 154024074601440303543527765)
                ·
                  refine ⟨451242406058907139287679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154024074601440303543527765 451242406058907139287679)
                  ·
                    rfl

theorem cell23_7909123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 10].length) (baseStart_7909123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909123 prefixEnd_7909123 := by exact prefixLift 7909123
  have htrace : WordTrace (prefixWord ++ tailWord_7909123) baseStart_7909123 baseEnd_7909123 := by
    simpa [prefixWord, tailWord_7909123, baseEnd_7909123] using wordTrace_append hprefix tailTrace_7909123
  have hstable : (prefixWord ++ tailWord_7909123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909123).length < 2 ^ (prefixWord ++ tailWord_7909123).sum := by decide
  have hdescent : baseEnd_7909123 < baseStart_7909123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909167 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_7909167 : Nat := 118140960795 + 7909167 * 2 ^ 59
def prefixEnd_7909167 : Nat := 4983230072969 + 3 ^ 40 * 7909167 * 2
def baseEnd_7909167 : Nat := 4061204247678962081438909

theorem tailTrace_7909167 : CollatzResearch.WordTrace tailWord_7909167 prefixEnd_7909167 4061204247678962081438909 := by
  unfold tailWord_7909167
  simp only [CollatzResearch.WordTrace]
  refine ⟨288471019337446212027765755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192314012891630808018510503 288471019337446212027765755)
  ·
    refine ⟨432706529006169318041648633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288471019337446212027765755 432706529006169318041648633)
    ·
      refine ⟨324529896754626988531236475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432706529006169318041648633 324529896754626988531236475)
      ·
        refine ⟨486794845131940482796854713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324529896754626988531236475 486794845131940482796854713)
        ·
          refine ⟨365096133848955362097641035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486794845131940482796854713 365096133848955362097641035)
          ·
            refine ⟨547644200773433043146461553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365096133848955362097641035 547644200773433043146461553)
            ·
              refine ⟨410733150580074782359846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547644200773433043146461553 410733150580074782359846165)
              ·
                refine ⟨19253116433441005423117789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 410733150580074782359846165 19253116433441005423117789)
                ·
                  refine ⟨7219918662540377033669171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19253116433441005423117789 7219918662540377033669171)
                  ·
                    refine ⟨10829877993810565550503757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219918662540377033669171 10829877993810565550503757)
                    ·
                      refine ⟨4061204247678962081438909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829877993810565550503757 4061204247678962081438909)
                      ·
                        rfl

theorem cell23_7909167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_7909167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909167 prefixEnd_7909167 := by exact prefixLift 7909167
  have htrace : WordTrace (prefixWord ++ tailWord_7909167) baseStart_7909167 baseEnd_7909167 := by
    simpa [prefixWord, tailWord_7909167, baseEnd_7909167] using wordTrace_append hprefix tailTrace_7909167
  have hstable : (prefixWord ++ tailWord_7909167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909167).length < 2 ^ (prefixWord ++ tailWord_7909167).sum := by decide
  have hdescent : baseEnd_7909167 < baseStart_7909167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909171 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 2, 2, 3]
def baseStart_7909171 : Nat := 118140960795 + 7909171 * 2 ^ 59
def prefixEnd_7909171 : Nat := 4983230072969 + 3 ^ 40 * 7909171 * 2
def baseEnd_7909171 : Nat := 4061206301601580065788891

theorem tailTrace_7909171 : CollatzResearch.WordTrace tailWord_7909171 prefixEnd_7909171 4061206301601580065788891 := by
  unfold tailWord_7909171
  simp only [CollatzResearch.WordTrace]
  refine ⟨288471165229431720710911367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192314110152954480473940911 288471165229431720710911367)
  ·
    refine ⟨432706747844147581066367051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288471165229431720710911367 432706747844147581066367051)
    ·
      refine ⟨649060121766221371599550577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432706747844147581066367051 649060121766221371599550577)
      ·
        refine ⟨486795091324666028699662933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649060121766221371599550577 486795091324666028699662933)
        ·
          refine ⟨5704629976460930023824175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 486795091324666028699662933 5704629976460930023824175)
          ·
            refine ⟨8556944964691395035736263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704629976460930023824175 8556944964691395035736263)
            ·
              refine ⟨12835417447037092553604395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556944964691395035736263 12835417447037092553604395)
              ·
                refine ⟨19253126170555638830406593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835417447037092553604395 19253126170555638830406593)
                ·
                  refine ⟨14439844627916729122804945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19253126170555638830406593 14439844627916729122804945)
                  ·
                    refine ⟨10829883470937546842103709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14439844627916729122804945 10829883470937546842103709)
                    ·
                      refine ⟨4061206301601580065788891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829883470937546842103709 4061206301601580065788891)
                      ·
                        rfl

theorem cell23_7909171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 2, 3].length) (baseStart_7909171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909171 prefixEnd_7909171 := by exact prefixLift 7909171
  have htrace : WordTrace (prefixWord ++ tailWord_7909171) baseStart_7909171 baseEnd_7909171 := by
    simpa [prefixWord, tailWord_7909171, baseEnd_7909171] using wordTrace_append hprefix tailTrace_7909171
  have hstable : (prefixWord ++ tailWord_7909171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909171).length < 2 ^ (prefixWord ++ tailWord_7909171).sum := by decide
  have hdescent : baseEnd_7909171 < baseStart_7909171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909187 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 1, 5]
def baseStart_7909187 : Nat := 118140960795 + 7909187 * 2 ^ 59
def prefixEnd_7909187 : Nat := 4983230072969 + 3 ^ 40 * 7909187 * 2
def baseEnd_7909187 : Nat := 1353738172430684001062939

theorem tailTrace_7909187 : CollatzResearch.WordTrace tailWord_7909187 prefixEnd_7909187 1353738172430684001062939 := by
  unfold tailWord_7909187
  simp only [CollatzResearch.WordTrace]
  refine ⟨288471748797373755443493815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192314499198249170295662543 288471748797373755443493815)
  ·
    refine ⟨432707623196060633165240723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288471748797373755443493815 432707623196060633165240723)
    ·
      refine ⟨649061434794090949747861085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432707623196060633165240723 649061434794090949747861085)
      ·
        refine ⟨243398038047784106155447907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649061434794090949747861085 243398038047784106155447907)
        ·
          refine ⟨365097057071676159233171861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243398038047784106155447907 365097057071676159233171861)
          ·
            refine ⟨17113924550234819964054931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365097057071676159233171861 17113924550234819964054931)
            ·
              refine ⟨25670886825352229946082397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17113924550234819964054931 25670886825352229946082397)
              ·
                refine ⟨9626582559507086229780899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25670886825352229946082397 9626582559507086229780899)
                ·
                  refine ⟨14439873839260629344671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626582559507086229780899 14439873839260629344671349)
                  ·
                    refine ⟨1353738172430684001062939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14439873839260629344671349 1353738172430684001062939)
                    ·
                      rfl

theorem cell23_7909187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 5].length) (baseStart_7909187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909187 prefixEnd_7909187 := by exact prefixLift 7909187
  have htrace : WordTrace (prefixWord ++ tailWord_7909187) baseStart_7909187 baseEnd_7909187 := by
    simpa [prefixWord, tailWord_7909187, baseEnd_7909187] using wordTrace_append hprefix tailTrace_7909187
  have hstable : (prefixWord ++ tailWord_7909187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909187).length < 2 ^ (prefixWord ++ tailWord_7909187).sum := by decide
  have hdescent : baseEnd_7909187 < baseStart_7909187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909201 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_7909201 : Nat := 118140960795 + 7909201 * 2 ^ 59
def prefixEnd_7909201 : Nat := 4983230072969 + 3 ^ 40 * 7909201 * 2
def baseEnd_7909201 : Nat := 4061221706021214948413753

theorem tailTrace_7909201 : CollatzResearch.WordTrace tailWord_7909201 prefixEnd_7909201 4061221706021214948413753 := by
  unfold tailWord_7909201
  simp only [CollatzResearch.WordTrace]
  refine ⟨288472259419323035834503457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192314839612882023889668971 288472259419323035834503457)
  ·
    refine ⟨216354194564492276875877593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288472259419323035834503457 216354194564492276875877593)
    ·
      refine ⟨162265645923369207656908195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216354194564492276875877593 162265645923369207656908195)
      ·
        refine ⟨243398468885053811485362293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162265645923369207656908195 243398468885053811485362293)
        ·
          refine ⟨22818606457973794826752715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243398468885053811485362293 22818606457973794826752715)
          ·
            refine ⟨34227909686960692240129073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22818606457973794826752715 34227909686960692240129073)
            ·
              refine ⟨25670932265220519180096805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34227909686960692240129073 25670932265220519180096805)
              ·
                refine ⟨4813299799728847346268151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25670932265220519180096805 4813299799728847346268151)
                ·
                  refine ⟨7219949699593271019402227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813299799728847346268151 7219949699593271019402227)
                  ·
                    refine ⟨10829924549389906529103341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219949699593271019402227 10829924549389906529103341)
                    ·
                      refine ⟨4061221706021214948413753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10829924549389906529103341 4061221706021214948413753)
                      ·
                        rfl

theorem cell23_7909201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_7909201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909201 prefixEnd_7909201 := by exact prefixLift 7909201
  have htrace : WordTrace (prefixWord ++ tailWord_7909201) baseStart_7909201 baseEnd_7909201 := by
    simpa [prefixWord, tailWord_7909201, baseEnd_7909201] using wordTrace_append hprefix tailTrace_7909201
  have hstable : (prefixWord ++ tailWord_7909201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909201).length < 2 ^ (prefixWord ++ tailWord_7909201).sum := by decide
  have hdescent : baseEnd_7909201 < baseStart_7909201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909224 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7909224 : Nat := 118140960795 + 7909224 * 2 ^ 59
def prefixEnd_7909224 : Nat := 4983230072969 + 3 ^ 40 * 7909224 * 2
def baseEnd_7909224 : Nat := 4061233516076268358426147

theorem tailTrace_7909224 : CollatzResearch.WordTrace tailWord_7909224 prefixEnd_7909224 4061233516076268358426147 := by
  unfold tailWord_7909224
  simp only [CollatzResearch.WordTrace]
  refine ⟨144236549149119855381295363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192315398865493140508393817 144236549149119855381295363)
  ·
    refine ⟨216354823723679783071943045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144236549149119855381295363 216354823723679783071943045)
    ·
      refine ⟨40566529448189959325989321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216354823723679783071943045 40566529448189959325989321)
      ·
        refine ⟨30424897086142469494491991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40566529448189959325989321 30424897086142469494491991)
        ·
          refine ⟨45637345629213704241737987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30424897086142469494491991 45637345629213704241737987)
          ·
            refine ⟨68456018443820556362606981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45637345629213704241737987 68456018443820556362606981)
            ·
              refine ⟨12835503458216354317988809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68456018443820556362606981 12835503458216354317988809)
              ·
                refine ⟨9626627593662265738491607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12835503458216354317988809 9626627593662265738491607)
                ·
                  refine ⟨14439941390493398607737411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626627593662265738491607 14439941390493398607737411)
                  ·
                    refine ⟨21659912085740097911606117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14439941390493398607737411 21659912085740097911606117)
                    ·
                      refine ⟨4061233516076268358426147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21659912085740097911606117 4061233516076268358426147)
                      ·
                        rfl

theorem cell23_7909224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7909224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909224 prefixEnd_7909224 := by exact prefixLift 7909224
  have htrace : WordTrace (prefixWord ++ tailWord_7909224) baseStart_7909224 baseEnd_7909224 := by
    simpa [prefixWord, tailWord_7909224, baseEnd_7909224] using wordTrace_append hprefix tailTrace_7909224
  have hstable : (prefixWord ++ tailWord_7909224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909224).length < 2 ^ (prefixWord ++ tailWord_7909224).sum := by decide
  have hdescent : baseEnd_7909224 < baseStart_7909224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909237 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7909237 : Nat := 118140960795 + 7909237 * 2 ^ 59
def prefixEnd_7909237 : Nat := 4983230072969 + 3 ^ 40 * 7909237 * 2
def baseEnd_7909237 : Nat := 4061240191324776807563587

theorem tailTrace_7909237 : CollatzResearch.WordTrace tailWord_7909237 prefixEnd_7909237 4061240191324776807563587 := by
  unfold tailWord_7909237
  simp only [CollatzResearch.WordTrace]
  refine ⟨288473572447192613982813965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192315714964795075988542643 288473572447192613982813965)
  ·
    refine ⟨108177589667697230243555237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288473572447192613982813965 108177589667697230243555237)
    ·
      refine ⟨20283298062693230670666607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108177589667697230243555237 20283298062693230670666607)
      ·
        refine ⟨30424947094039846005999911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283298062693230670666607 30424947094039846005999911)
        ·
          refine ⟨45637420641059769008999867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30424947094039846005999911 45637420641059769008999867)
          ·
            refine ⟨68456130961589653513499801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45637420641059769008999867 68456130961589653513499801)
            ·
              refine ⟨51342098221192240135124851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68456130961589653513499801 51342098221192240135124851)
              ·
                refine ⟨77013147331788360202687277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51342098221192240135124851 77013147331788360202687277)
                ·
                  refine ⟨28879930249420635076007729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77013147331788360202687277 28879930249420635076007729)
                  ·
                    refine ⟨21659947687065476307005797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28879930249420635076007729 21659947687065476307005797)
                    ·
                      refine ⟨4061240191324776807563587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21659947687065476307005797 4061240191324776807563587)
                      ·
                        rfl

theorem cell23_7909237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7909237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909237 prefixEnd_7909237 := by exact prefixLift 7909237
  have htrace : WordTrace (prefixWord ++ tailWord_7909237) baseStart_7909237 baseEnd_7909237 := by
    simpa [prefixWord, tailWord_7909237, baseEnd_7909237] using wordTrace_append hprefix tailTrace_7909237
  have hstable : (prefixWord ++ tailWord_7909237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909237).length < 2 ^ (prefixWord ++ tailWord_7909237).sum := by decide
  have hdescent : baseEnd_7909237 < baseStart_7909237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909260 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_7909260 : Nat := 118140960795 + 7909260 * 2 ^ 59
def prefixEnd_7909260 : Nat := 4983230072969 + 3 ^ 40 * 7909260 * 2
def baseEnd_7909260 : Nat := 1353750667126610072525327

theorem tailTrace_7909260 : CollatzResearch.WordTrace tailWord_7909260 prefixEnd_7909260 1353750667126610072525327 := by
  unfold tailWord_7909260
  simp only [CollatzResearch.WordTrace]
  refine ⟨144237205663054644455450617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192316274217406192607267489 144237205663054644455450617)
  ·
    refine ⟨108177904247290983341587963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144237205663054644455450617 108177904247290983341587963)
    ·
      refine ⟨162266856370936475012381945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108177904247290983341587963 162266856370936475012381945)
      ·
        refine ⟨121700142278202356259286459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162266856370936475012381945 121700142278202356259286459)
        ·
          refine ⟨182550213417303534388929689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121700142278202356259286459 182550213417303534388929689)
          ·
            refine ⟨136912660062977650791697267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182550213417303534388929689 136912660062977650791697267)
            ·
              refine ⟨205368990094466476187545901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136912660062977650791697267 205368990094466476187545901)
              ·
                refine ⟨77013371285424928570329713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205368990094466476187545901 77013371285424928570329713)
                ·
                  refine ⟨57760028464068696427747285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77013371285424928570329713 57760028464068696427747285)
                  ·
                    refine ⟨1353750667126610072525327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57760028464068696427747285 1353750667126610072525327)
                    ·
                      rfl

theorem cell23_7909260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_7909260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909260 prefixEnd_7909260 := by exact prefixLift 7909260
  have htrace : WordTrace (prefixWord ++ tailWord_7909260) baseStart_7909260 baseEnd_7909260 := by
    simpa [prefixWord, tailWord_7909260, baseEnd_7909260] using wordTrace_append hprefix tailTrace_7909260
  have hstable : (prefixWord ++ tailWord_7909260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909260).length < 2 ^ (prefixWord ++ tailWord_7909260).sum := by decide
  have hdescent : baseEnd_7909260 < baseStart_7909260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909268 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7909268 : Nat := 118140960795 + 7909268 * 2 ^ 59
def prefixEnd_7909268 : Nat := 4983230072969 + 3 ^ 40 * 7909268 * 2
def baseEnd_7909268 : Nat := 1353752036408355395425315

theorem tailTrace_7909268 : CollatzResearch.WordTrace tailWord_7909268 prefixEnd_7909268 1353752036408355395425315 := by
  unfold tailWord_7909268
  simp only [CollatzResearch.WordTrace]
  refine ⟨144237351555040153138596229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192316468740053537518128305 144237351555040153138596229)
  ·
    refine ⟨27044503416570028713486793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144237351555040153138596229 27044503416570028713486793)
    ·
      refine ⟨20283377562427521535115095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27044503416570028713486793 20283377562427521535115095)
      ·
        refine ⟨30425066343641282302672643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283377562427521535115095 30425066343641282302672643)
        ·
          refine ⟨45637599515461923454008965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30425066343641282302672643 45637599515461923454008965)
          ·
            refine ⟨8557049909149110647626681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45637599515461923454008965 8557049909149110647626681)
            ·
              refine ⟨6417787431861832985720011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557049909149110647626681 6417787431861832985720011)
              ·
                refine ⟨9626681147792749478580017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417787431861832985720011 9626681147792749478580017)
                ·
                  refine ⟨7220010860844562108935013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9626681147792749478580017 7220010860844562108935013)
                  ·
                    refine ⟨1353752036408355395425315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220010860844562108935013 1353752036408355395425315)
                    ·
                      rfl

theorem cell23_7909268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7909268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909268 prefixEnd_7909268 := by exact prefixLift 7909268
  have htrace : WordTrace (prefixWord ++ tailWord_7909268) baseStart_7909268 baseEnd_7909268 := by
    simpa [prefixWord, tailWord_7909268, baseEnd_7909268] using wordTrace_append hprefix tailTrace_7909268
  have hstable : (prefixWord ++ tailWord_7909268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909268).length < 2 ^ (prefixWord ++ tailWord_7909268).sum := by decide
  have hdescent : baseEnd_7909268 < baseStart_7909268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909278 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7909278 : Nat := 118140960795 + 7909278 * 2 ^ 59
def prefixEnd_7909278 : Nat := 4983230072969 + 3 ^ 40 * 7909278 * 2
def baseEnd_7909278 : Nat := 4061261244031611147150899

theorem tailTrace_7909278 : CollatzResearch.WordTrace tailWord_7909278 prefixEnd_7909278 4061261244031611147150899 := by
  unfold tailWord_7909278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059383480005509748132061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192316711893362718656704325 36059383480005509748132061)
  ·
    refine ⟨13522268805002066155549523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36059383480005509748132061 13522268805002066155549523)
    ·
      refine ⟨20283403207503099233324285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522268805002066155549523 20283403207503099233324285)
      ·
        refine ⟨7606276202813662212496607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20283403207503099233324285 7606276202813662212496607)
        ·
          refine ⟨11409414304220493318744911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606276202813662212496607 11409414304220493318744911)
          ·
            refine ⟨17114121456330739978117367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409414304220493318744911 17114121456330739978117367)
            ·
              refine ⟨25671182184496109967176051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114121456330739978117367 25671182184496109967176051)
              ·
                refine ⟨38506773276744164950764077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25671182184496109967176051 38506773276744164950764077)
                ·
                  refine ⟨14440039978779061856536529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38506773276744164950764077 14440039978779061856536529)
                  ·
                    refine ⟨10830029984084296392402397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14440039978779061856536529 10830029984084296392402397)
                    ·
                      refine ⟨4061261244031611147150899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830029984084296392402397 4061261244031611147150899)
                      ·
                        rfl

theorem cell23_7909278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7909278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909278 prefixEnd_7909278 := by exact prefixLift 7909278
  have htrace : WordTrace (prefixWord ++ tailWord_7909278) baseStart_7909278 baseEnd_7909278 := by
    simpa [prefixWord, tailWord_7909278, baseEnd_7909278] using wordTrace_append hprefix tailTrace_7909278
  have hstable : (prefixWord ++ tailWord_7909278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909278).length < 2 ^ (prefixWord ++ tailWord_7909278).sum := by decide
  have hdescent : baseEnd_7909278 < baseStart_7909278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909280 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_7909280 : Nat := 118140960795 + 7909280 * 2 ^ 59
def prefixEnd_7909280 : Nat := 4983230072969 + 3 ^ 40 * 7909280 * 2
def baseEnd_7909280 : Nat := 4061262270992920139325889

theorem tailTrace_7909280 : CollatzResearch.WordTrace tailWord_7909280 prefixEnd_7909280 4061262270992920139325889 := by
  unfold tailWord_7909280
  simp only [CollatzResearch.WordTrace]
  refine ⟨144237570393018416163314647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192316760524024554884419529 144237570393018416163314647)
  ·
    refine ⟨216356355589527624244971971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144237570393018416163314647 216356355589527624244971971)
    ·
      refine ⟨324534533384291436367457957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216356355589527624244971971 324534533384291436367457957)
      ·
        refine ⟨60850225009554644318898367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324534533384291436367457957 60850225009554644318898367)
        ·
          refine ⟨91275337514331966478347551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60850225009554644318898367 91275337514331966478347551)
          ·
            refine ⟨136913006271497949717521327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91275337514331966478347551 136913006271497949717521327)
            ·
              refine ⟨205369509407246924576281991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136913006271497949717521327 205369509407246924576281991)
              ·
                refine ⟨308054264110870386864422987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205369509407246924576281991 308054264110870386864422987)
                ·
                  refine ⟨462081396166305580296634481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308054264110870386864422987 462081396166305580296634481)
                  ·
                    refine ⟨346561047124729185222475861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462081396166305580296634481 346561047124729185222475861)
                    ·
                      refine ⟨4061262270992920139325889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346561047124729185222475861 4061262270992920139325889)
                      ·
                        rfl

theorem cell23_7909280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_7909280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909280 prefixEnd_7909280 := by exact prefixLift 7909280
  have htrace : WordTrace (prefixWord ++ tailWord_7909280) baseStart_7909280 baseEnd_7909280 := by
    simpa [prefixWord, tailWord_7909280, baseEnd_7909280] using wordTrace_append hprefix tailTrace_7909280
  have hstable : (prefixWord ++ tailWord_7909280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909280).length < 2 ^ (prefixWord ++ tailWord_7909280).sum := by decide
  have hdescent : baseEnd_7909280 < baseStart_7909280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909327 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_7909327 : Nat := 118140960795 + 7909327 * 2 ^ 59
def prefixEnd_7909327 : Nat := 4983230072969 + 3 ^ 40 * 7909327 * 2
def baseEnd_7909327 : Nat := 4061286404583681455438173

theorem tailTrace_7909327 : CollatzResearch.WordTrace tailWord_7909327 prefixEnd_7909327 4061286404583681455438173 := by
  unfold tailWord_7909327
  simp only [CollatzResearch.WordTrace]
  refine ⟨288476855016866559353590235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192317903344577706235726823 288476855016866559353590235)
  ·
    refine ⟨432715282525299839030385353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288476855016866559353590235 432715282525299839030385353)
    ·
      refine ⟨324536461893974879272789015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432715282525299839030385353 324536461893974879272789015)
      ·
        refine ⟨486804692840962318909183523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324536461893974879272789015 486804692840962318909183523)
        ·
          refine ⟨730207039261443478363775285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486804692840962318909183523 730207039261443478363775285)
          ·
            refine ⟨68456909930760326096603933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 730207039261443478363775285 68456909930760326096603933)
            ·
              refine ⟨25671341224035122286226475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68456909930760326096603933 25671341224035122286226475)
              ·
                refine ⟨38507011836052683429339713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25671341224035122286226475 38507011836052683429339713)
                ·
                  refine ⟨28880258877039512572004785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38507011836052683429339713 28880258877039512572004785)
                  ·
                    refine ⟨21660194157779634429003589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28880258877039512572004785 21660194157779634429003589)
                    ·
                      refine ⟨4061286404583681455438173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21660194157779634429003589 4061286404583681455438173)
                      ·
                        rfl

theorem cell23_7909327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_7909327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909327 prefixEnd_7909327 := by exact prefixLift 7909327
  have htrace : WordTrace (prefixWord ++ tailWord_7909327) baseStart_7909327 baseEnd_7909327 := by
    simpa [prefixWord, tailWord_7909327, baseEnd_7909327] using wordTrace_append hprefix tailTrace_7909327
  have hstable : (prefixWord ++ tailWord_7909327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909327).length < 2 ^ (prefixWord ++ tailWord_7909327).sum := by decide
  have hdescent : baseEnd_7909327 < baseStart_7909327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909377 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7909377 : Nat := 118140960795 + 7909377 * 2 ^ 59
def prefixEnd_7909377 : Nat := 4983230072969 + 3 ^ 40 * 7909377 * 2
def baseEnd_7909377 : Nat := 4061312078616406259812943

theorem tailTrace_7909377 : CollatzResearch.WordTrace tailWord_7909377 prefixEnd_7909377 4061312078616406259812943 := by
  unfold tailWord_7909377
  simp only [CollatzResearch.WordTrace]
  refine ⟨288478678666685417892910385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192319119111123611928606923 288478678666685417892910385)
  ·
    refine ⟨216359009000014063419682789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288478678666685417892910385 216359009000014063419682789)
    ·
      refine ⟨40567314187502636891190523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216359009000014063419682789 40567314187502636891190523)
      ·
        refine ⟨60850971281253955336785785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567314187502636891190523 60850971281253955336785785)
        ·
          refine ⟨45638228460940466502589339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60850971281253955336785785 45638228460940466502589339)
          ·
            refine ⟨68457342691410699753884009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45638228460940466502589339 68457342691410699753884009)
            ·
              refine ⟨51343007018558024815413007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68457342691410699753884009 51343007018558024815413007)
              ·
                refine ⟨77014510527837037223119511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51343007018558024815413007 77014510527837037223119511)
                ·
                  refine ⟨115521765791755555834679267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77014510527837037223119511 115521765791755555834679267)
                  ·
                    refine ⟨173282648687633333752018901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115521765791755555834679267 173282648687633333752018901)
                    ·
                      refine ⟨4061312078616406259812943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173282648687633333752018901 4061312078616406259812943)
                      ·
                        rfl

theorem cell23_7909377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7909377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909377 prefixEnd_7909377 := by exact prefixLift 7909377
  have htrace : WordTrace (prefixWord ++ tailWord_7909377) baseStart_7909377 baseEnd_7909377 := by
    simpa [prefixWord, tailWord_7909377, baseEnd_7909377] using wordTrace_append hprefix tailTrace_7909377
  have hstable : (prefixWord ++ tailWord_7909377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909377).length < 2 ^ (prefixWord ++ tailWord_7909377).sum := by decide
  have hdescent : baseEnd_7909377 < baseStart_7909377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909387 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_7909387 : Nat := 118140960795 + 7909387 * 2 ^ 59
def prefixEnd_7909387 : Nat := 4983230072969 + 3 ^ 40 * 7909387 * 2
def baseEnd_7909387 : Nat := 4061317213422951220687897

theorem tailTrace_7909387 : CollatzResearch.WordTrace tailWord_7909387 prefixEnd_7909387 4061317213422951220687897 := by
  unfold tailWord_7909387
  simp only [CollatzResearch.WordTrace]
  refine ⟨288479043396649189600774415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192319362264432793067182943 288479043396649189600774415)
  ·
    refine ⟨432718565094973784401161623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288479043396649189600774415 432718565094973784401161623)
    ·
      refine ⟨649077847642460676601742435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432718565094973784401161623 649077847642460676601742435)
      ·
        refine ⟨973616771463691014902613653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649077847642460676601742435 973616771463691014902613653)
        ·
          refine ⟨45638286162360516323560015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 973616771463691014902613653 45638286162360516323560015)
          ·
            refine ⟨68457429243540774485340023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45638286162360516323560015 68457429243540774485340023)
            ·
              refine ⟨102686143865311161728010035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68457429243540774485340023 102686143865311161728010035)
              ·
                refine ⟨154029215797966742592015053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102686143865311161728010035 154029215797966742592015053)
                ·
                  refine ⟨57760955924237528472005645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154029215797966742592015053 57760955924237528472005645)
                  ·
                    refine ⟨21660358471589073177002117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57760955924237528472005645 21660358471589073177002117)
                    ·
                      refine ⟨4061317213422951220687897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21660358471589073177002117 4061317213422951220687897)
                      ·
                        rfl

theorem cell23_7909387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_7909387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909387 prefixEnd_7909387 := by exact prefixLift 7909387
  have htrace : WordTrace (prefixWord ++ tailWord_7909387) baseStart_7909387 baseEnd_7909387 := by
    simpa [prefixWord, tailWord_7909387, baseEnd_7909387] using wordTrace_append hprefix tailTrace_7909387
  have hstable : (prefixWord ++ tailWord_7909387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909387).length < 2 ^ (prefixWord ++ tailWord_7909387).sum := by decide
  have hdescent : baseEnd_7909387 < baseStart_7909387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909404 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7909404 : Nat := 118140960795 + 7909404 * 2 ^ 59
def prefixEnd_7909404 : Nat := 4983230072969 + 3 ^ 40 * 7909404 * 2
def baseEnd_7909404 : Nat := 4061325942594077654175319

theorem tailTrace_7909404 : CollatzResearch.WordTrace tailWord_7909404 prefixEnd_7909404 4061325942594077654175319 := by
  unfold tailWord_7909404
  simp only [CollatzResearch.WordTrace]
  refine ⟨144239831718793800752071633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192319775625058401002762177 144239831718793800752071633)
  ·
    refine ⟨108179873789095350564053725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144239831718793800752071633 108179873789095350564053725)
    ·
      refine ⟨40567452670910756461520147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108179873789095350564053725 40567452670910756461520147)
      ·
        refine ⟨60851179006366134692280221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567452670910756461520147 60851179006366134692280221)
        ·
          refine ⟨22819192127387300509605083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60851179006366134692280221 22819192127387300509605083)
          ·
            refine ⟨34228788191080950764407625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22819192127387300509605083 34228788191080950764407625)
            ·
              refine ⟨25671591143310713073305719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34228788191080950764407625 25671591143310713073305719)
              ·
                refine ⟨38507386714966069609958579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25671591143310713073305719 38507386714966069609958579)
                ·
                  refine ⟨57761080072449104414937869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38507386714966069609958579 57761080072449104414937869)
                  ·
                    refine ⟨21660405027168414155601701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57761080072449104414937869 21660405027168414155601701)
                    ·
                      refine ⟨4061325942594077654175319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21660405027168414155601701 4061325942594077654175319)
                      ·
                        rfl

theorem cell23_7909404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7909404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909404 prefixEnd_7909404 := by exact prefixLift 7909404
  have htrace : WordTrace (prefixWord ++ tailWord_7909404) baseStart_7909404 baseEnd_7909404 := by
    simpa [prefixWord, tailWord_7909404, baseEnd_7909404] using wordTrace_append hprefix tailTrace_7909404
  have hstable : (prefixWord ++ tailWord_7909404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909404).length < 2 ^ (prefixWord ++ tailWord_7909404).sum := by decide
  have hdescent : baseEnd_7909404 < baseStart_7909404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909424 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_7909424 : Nat := 118140960795 + 7909424 * 2 ^ 59
def prefixEnd_7909424 : Nat := 4983230072969 + 3 ^ 40 * 7909424 * 2
def baseEnd_7909424 : Nat := 4061336212207167575925227

theorem tailTrace_7909424 : CollatzResearch.WordTrace tailWord_7909424 prefixEnd_7909424 4061336212207167575925227 := by
  unfold tailWord_7909424
  simp only [CollatzResearch.WordTrace]
  refine ⟨144240196448757572459935663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192320261931676763279914217 144240196448757572459935663)
  ·
    refine ⟨216360294673136358689903495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144240196448757572459935663 216360294673136358689903495)
    ·
      refine ⟨324540442009704538034855243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216360294673136358689903495 324540442009704538034855243)
      ·
        refine ⟨486810663014556807052282865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324540442009704538034855243 486810663014556807052282865)
        ·
          refine ⟨365107997260917605289212149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486810663014556807052282865 365107997260917605289212149)
          ·
            refine ⟨34228874743211025495863639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365107997260917605289212149 34228874743211025495863639)
            ·
              refine ⟨51343312114816538243795459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34228874743211025495863639 51343312114816538243795459)
              ·
                refine ⟨77014968172224807365693189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51343312114816538243795459 77014968172224807365693189)
                ·
                  refine ⟨14440306532292151381067473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77014968172224807365693189 14440306532292151381067473)
                  ·
                    refine ⟨10830229899219113535800605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14440306532292151381067473 10830229899219113535800605)
                    ·
                      refine ⟨4061336212207167575925227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830229899219113535800605 4061336212207167575925227)
                      ·
                        rfl

theorem cell23_7909424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_7909424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909424 prefixEnd_7909424 := by exact prefixLift 7909424
  have htrace : WordTrace (prefixWord ++ tailWord_7909424) baseStart_7909424 baseEnd_7909424 := by
    simpa [prefixWord, tailWord_7909424, baseEnd_7909424] using wordTrace_append hprefix tailTrace_7909424
  have hstable : (prefixWord ++ tailWord_7909424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909424).length < 2 ^ (prefixWord ++ tailWord_7909424).sum := by decide
  have hdescent : baseEnd_7909424 < baseStart_7909424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909427 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 8]
def baseStart_7909427 : Nat := 118140960795 + 7909427 * 2 ^ 59
def prefixEnd_7909427 : Nat := 4983230072969 + 3 ^ 40 * 7909427 * 2
def baseEnd_7909427 : Nat := 451259750294347896020857

theorem tailTrace_7909427 : CollatzResearch.WordTrace tailWord_7909427 prefixEnd_7909427 451259750294347896020857 := by
  unfold tailWord_7909427
  simp only [CollatzResearch.WordTrace]
  refine ⟨288480502316504276432230535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192320334877669517621487023 288480502316504276432230535)
  ·
    refine ⟨432720753474756414648345803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288480502316504276432230535 432720753474756414648345803)
    ·
      refine ⟨649081130212134621972518705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432720753474756414648345803 649081130212134621972518705)
      ·
        refine ⟨486810847659100966479389029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649081130212134621972518705 486810847659100966479389029)
        ·
          refine ⟨91277033936081431214885443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486810847659100966479389029 91277033936081431214885443)
          ·
            refine ⟨136915550904122146822328165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91277033936081431214885443 136915550904122146822328165)
            ·
              refine ⟨25671665794522902529186531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136915550904122146822328165 25671665794522902529186531)
              ·
                refine ⟨38507498691784353793779797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25671665794522902529186531 38507498691784353793779797)
                ·
                  refine ⟨451259750294347896020857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38507498691784353793779797 451259750294347896020857)
                  ·
                    rfl

theorem cell23_7909427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 8].length) (baseStart_7909427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909427 prefixEnd_7909427 := by exact prefixLift 7909427
  have htrace : WordTrace (prefixWord ++ tailWord_7909427) baseStart_7909427 baseEnd_7909427 := by
    simpa [prefixWord, tailWord_7909427, baseEnd_7909427] using wordTrace_append hprefix tailTrace_7909427
  have hstable : (prefixWord ++ tailWord_7909427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909427).length < 2 ^ (prefixWord ++ tailWord_7909427).sum := by decide
  have hdescent : baseEnd_7909427 < baseStart_7909427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909431 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 1, 4]
def baseStart_7909431 : Nat := 118140960795 + 7909431 * 2 ^ 59
def prefixEnd_7909431 : Nat := 4983230072969 + 3 ^ 40 * 7909431 * 2
def baseEnd_7909431 : Nat := 1353779935523916349512565

theorem tailTrace_7909431 : CollatzResearch.WordTrace tailWord_7909431 prefixEnd_7909431 1353779935523916349512565 := by
  unfold tailWord_7909431
  simp only [CollatzResearch.WordTrace]
  refine ⟨288480648208489785115376147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192320432138993190076917431 288480648208489785115376147)
  ·
    refine ⟨432720972312734677673064221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288480648208489785115376147 432720972312734677673064221)
    ·
      refine ⟨162270364617275504127399083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432720972312734677673064221 162270364617275504127399083)
      ·
        refine ⟨243405546925913256191098625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162270364617275504127399083 243405546925913256191098625)
        ·
          refine ⟨182554160194434942143323969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243405546925913256191098625 182554160194434942143323969)
          ·
            refine ⟨136915620145826206607492977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182554160194434942143323969 136915620145826206607492977)
            ·
              refine ⟨102686715109369654955619733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136915620145826206607492977 102686715109369654955619733)
              ·
                refine ⟨4813439770751702576044675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102686715109369654955619733 4813439770751702576044675)
                ·
                  refine ⟨7220159656127553864067013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813439770751702576044675 7220159656127553864067013)
                  ·
                    refine ⟨1353779935523916349512565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220159656127553864067013 1353779935523916349512565)
                    ·
                      rfl

theorem cell23_7909431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_7909431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909431 prefixEnd_7909431 := by exact prefixLift 7909431
  have htrace : WordTrace (prefixWord ++ tailWord_7909431) baseStart_7909431 baseEnd_7909431 := by
    simpa [prefixWord, tailWord_7909431, baseEnd_7909431] using wordTrace_append hprefix tailTrace_7909431
  have hstable : (prefixWord ++ tailWord_7909431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909431).length < 2 ^ (prefixWord ++ tailWord_7909431).sum := by decide
  have hdescent : baseEnd_7909431 < baseStart_7909431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909458 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_7909458 : Nat := 118140960795 + 7909458 * 2 ^ 59
def prefixEnd_7909458 : Nat := 4983230072969 + 3 ^ 40 * 7909458 * 2
def baseEnd_7909458 : Nat := 4061353670549420442900071

theorem tailTrace_7909458 : CollatzResearch.WordTrace tailWord_7909458 prefixEnd_7909458 4061353670549420442900071 := by
  unfold tailWord_7909458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72120408244847992181652257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192321088652927979151072685 72120408244847992181652257)
  ·
    refine ⟨54090306183635994136239193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72120408244847992181652257 54090306183635994136239193)
    ·
      refine ⟨40567729637726995602179395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54090306183635994136239193 40567729637726995602179395)
      ·
        refine ⟨60851594456590493403269093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567729637726995602179395 60851594456590493403269093)
        ·
          refine ⟨11409673960610717513112955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60851594456590493403269093 11409673960610717513112955)
          ·
            refine ⟨17114510940916076269669433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409673960610717513112955 17114510940916076269669433)
            ·
              refine ⟨12835883205687057202252075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17114510940916076269669433 12835883205687057202252075)
              ·
                refine ⟨19253824808530585803378113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835883205687057202252075 19253824808530585803378113)
                ·
                  refine ⟨14440368606397939352533585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19253824808530585803378113 14440368606397939352533585)
                  ·
                    refine ⟨10830276454798454514400189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14440368606397939352533585 10830276454798454514400189)
                    ·
                      refine ⟨4061353670549420442900071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830276454798454514400189 4061353670549420442900071)
                      ·
                        rfl

theorem cell23_7909458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_7909458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909458 prefixEnd_7909458 := by exact prefixLift 7909458
  have htrace : WordTrace (prefixWord ++ tailWord_7909458) baseStart_7909458 baseEnd_7909458 := by
    simpa [prefixWord, tailWord_7909458, baseEnd_7909458] using wordTrace_append hprefix tailTrace_7909458
  have hstable : (prefixWord ++ tailWord_7909458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909458).length < 2 ^ (prefixWord ++ tailWord_7909458).sum := by decide
  have hdescent : baseEnd_7909458 < baseStart_7909458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909481 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 2, 3, 2]
def baseStart_7909481 : Nat := 118140960795 + 7909481 * 2 ^ 59
def prefixEnd_7909481 : Nat := 4983230072969 + 3 ^ 40 * 7909481 * 2
def baseEnd_7909481 : Nat := 4061365480604473852912465

theorem tailTrace_7909481 : CollatzResearch.WordTrace tailWord_7909481 prefixEnd_7909481 4061365480604473852912465 := by
  unfold tailWord_7909481
  simp only [CollatzResearch.WordTrace]
  refine ⟨288482471858308643654696297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192321647905539095769797531 288482471858308643654696297)
  ·
    refine ⟨216361853893731482741022223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288482471858308643654696297 216361853893731482741022223)
    ·
      refine ⟨324542780840597224111533335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216361853893731482741022223 324542780840597224111533335)
      ·
        refine ⟨486814171260895836167300003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324542780840597224111533335 486814171260895836167300003)
        ·
          refine ⟨730221256891343754250950005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486814171260895836167300003 730221256891343754250950005)
          ·
            refine ⟨68458242833563476961026563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 730221256891343754250950005 68458242833563476961026563)
            ·
              refine ⟨102687364250345215441539845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68458242833563476961026563 102687364250345215441539845)
              ·
                refine ⟨19253880796939727895288721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102687364250345215441539845 19253880796939727895288721)
                ·
                  refine ⟨14440410597704795921466541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19253880796939727895288721 14440410597704795921466541)
                  ·
                    refine ⟨5415153974139298470549953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14440410597704795921466541 5415153974139298470549953)
                    ·
                      refine ⟨4061365480604473852912465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415153974139298470549953 4061365480604473852912465)
                      ·
                        rfl

theorem cell23_7909481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 3, 2].length) (baseStart_7909481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909481 prefixEnd_7909481 := by exact prefixLift 7909481
  have htrace : WordTrace (prefixWord ++ tailWord_7909481) baseStart_7909481 baseEnd_7909481 := by
    simpa [prefixWord, tailWord_7909481, baseEnd_7909481] using wordTrace_append hprefix tailTrace_7909481
  have hstable : (prefixWord ++ tailWord_7909481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909481).length < 2 ^ (prefixWord ++ tailWord_7909481).sum := by decide
  have hdescent : baseEnd_7909481 < baseStart_7909481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909482 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_7909482 : Nat := 118140960795 + 7909482 * 2 ^ 59
def prefixEnd_7909482 : Nat := 4983230072969 + 3 ^ 40 * 7909482 * 2
def baseEnd_7909482 : Nat := 1353788664695042782999987

theorem tailTrace_7909482 : CollatzResearch.WordTrace tailWord_7909482 prefixEnd_7909482 1353788664695042782999987 := by
  unfold tailWord_7909482
  simp only [CollatzResearch.WordTrace]
  refine ⟨72120627082826255206370675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192321672220870013883655133 72120627082826255206370675)
  ·
    refine ⟨108180940624239382809556013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72120627082826255206370675 108180940624239382809556013)
    ·
      refine ⟨40567852734089768553583505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108180940624239382809556013 40567852734089768553583505)
      ·
        refine ⟨30425889550567326415187629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40567852734089768553583505 30425889550567326415187629)
        ·
          refine ⟨11409708581462747405695361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30425889550567326415187629 11409708581462747405695361)
          ·
            refine ⟨8557281436097060554271521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11409708581462747405695361 8557281436097060554271521)
            ·
              refine ⟨6417961077072795415703641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557281436097060554271521 6417961077072795415703641)
              ·
                refine ⟨4813470807804596561777731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6417961077072795415703641 4813470807804596561777731)
                ·
                  refine ⟨7220206211706894842666597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813470807804596561777731 7220206211706894842666597)
                  ·
                    refine ⟨1353788664695042782999987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220206211706894842666597 1353788664695042782999987)
                    ·
                      rfl

theorem cell23_7909482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_7909482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909482 prefixEnd_7909482 := by exact prefixLift 7909482
  have htrace : WordTrace (prefixWord ++ tailWord_7909482) baseStart_7909482 baseEnd_7909482 := by
    simpa [prefixWord, tailWord_7909482, baseEnd_7909482] using wordTrace_append hprefix tailTrace_7909482
  have hstable : (prefixWord ++ tailWord_7909482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909482).length < 2 ^ (prefixWord ++ tailWord_7909482).sum := by decide
  have hdescent : baseEnd_7909482 < baseStart_7909482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909504 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_7909504 : Nat := 118140960795 + 7909504 * 2 ^ 59
def prefixEnd_7909504 : Nat := 4983230072969 + 3 ^ 40 * 7909504 * 2
def baseEnd_7909504 : Nat := 1353792430219842420974953

theorem tailTrace_7909504 : CollatzResearch.WordTrace tailWord_7909504 prefixEnd_7909504 1353792430219842420974953 := by
  unfold tailWord_7909504
  simp only [CollatzResearch.WordTrace]
  refine ⟨144241655368612659291391783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192322207158150212388522377 144241655368612659291391783)
  ·
    refine ⟨216362483052918988937087675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144241655368612659291391783 216362483052918988937087675)
    ·
      refine ⟨324543724579378483405631513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216362483052918988937087675 324543724579378483405631513)
      ·
        refine ⟨243407793434533862554223635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324543724579378483405631513 243407793434533862554223635)
        ·
          refine ⟨365111690151800793831335453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243407793434533862554223635 365111690151800793831335453)
          ·
            refine ⟨136916883806925297686750795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365111690151800793831335453 136916883806925297686750795)
            ·
              refine ⟨205375325710387946530126193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136916883806925297686750795 205375325710387946530126193)
              ·
                refine ⟨154031494282790959897594645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205375325710387946530126193 154031494282790959897594645)
                ·
                  refine ⟨7220226294505826245199749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154031494282790959897594645 7220226294505826245199749)
                  ·
                    refine ⟨1353792430219842420974953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220226294505826245199749 1353792430219842420974953)
                    ·
                      rfl

theorem cell23_7909504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_7909504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909504 prefixEnd_7909504 := by exact prefixLift 7909504
  have htrace : WordTrace (prefixWord ++ tailWord_7909504) baseStart_7909504 baseEnd_7909504 := by
    simpa [prefixWord, tailWord_7909504, baseEnd_7909504] using wordTrace_append hprefix tailTrace_7909504
  have hstable : (prefixWord ++ tailWord_7909504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909504).length < 2 ^ (prefixWord ++ tailWord_7909504).sum := by decide
  have hdescent : baseEnd_7909504 < baseStart_7909504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909528 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7909528 : Nat := 118140960795 + 7909528 * 2 ^ 59
def prefixEnd_7909528 : Nat := 4983230072969 + 3 ^ 40 * 7909528 * 2
def baseEnd_7909528 : Nat := 4061389614195235169024749

theorem tailTrace_7909528 : CollatzResearch.WordTrace tailWord_7909528 prefixEnd_7909528 4061389614195235169024749 := by
  unfold tailWord_7909528
  simp only [CollatzResearch.WordTrace]
  refine ⟨144242093044569185340828619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192322790726092247121104825 144242093044569185340828619)
  ·
    refine ⟨216363139566853778011242929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144242093044569185340828619 216363139566853778011242929)
    ·
      refine ⟨162272354675140333508432197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216363139566853778011242929 162272354675140333508432197)
      ·
        refine ⟨30426066501588812532831037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162272354675140333508432197 30426066501588812532831037)
        ·
          refine ⟨11409774938095804699811639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30426066501588812532831037 11409774938095804699811639)
          ·
            refine ⟨17114662407143707049717459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409774938095804699811639 17114662407143707049717459)
            ·
              refine ⟨25671993610715560574576189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114662407143707049717459 25671993610715560574576189)
              ·
                refine ⟨9626997604018335215466071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25671993610715560574576189 9626997604018335215466071)
                ·
                  refine ⟨14440496406027502823199107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626997604018335215466071 14440496406027502823199107)
                  ·
                    refine ⟨21660744609041254234798661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14440496406027502823199107 21660744609041254234798661)
                    ·
                      refine ⟨4061389614195235169024749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21660744609041254234798661 4061389614195235169024749)
                      ·
                        rfl

theorem cell23_7909528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7909528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909528 prefixEnd_7909528 := by exact prefixLift 7909528
  have htrace : WordTrace (prefixWord ++ tailWord_7909528) baseStart_7909528 baseEnd_7909528 := by
    simpa [prefixWord, tailWord_7909528, baseEnd_7909528] using wordTrace_append hprefix tailTrace_7909528
  have hstable : (prefixWord ++ tailWord_7909528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909528).length < 2 ^ (prefixWord ++ tailWord_7909528).sum := by decide
  have hdescent : baseEnd_7909528 < baseStart_7909528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909538 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7909538 : Nat := 118140960795 + 7909538 * 2 ^ 59
def prefixEnd_7909538 : Nat := 4983230072969 + 3 ^ 40 * 7909538 * 2
def baseEnd_7909538 : Nat := 1353798249667260043299901

theorem tailTrace_7909538 : CollatzResearch.WordTrace tailWord_7909538 prefixEnd_7909538 1353798249667260043299901 := by
  unfold tailWord_7909538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72121137704775535597380317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192323033879401428259680845 72121137704775535597380317)
  ·
    refine ⟨27045426639290825849017619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72121137704775535597380317 27045426639290825849017619)
    ·
      refine ⟨40568139958936238773526429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27045426639290825849017619 40568139958936238773526429)
      ·
        refine ⟨15213052484601089540072411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40568139958936238773526429 15213052484601089540072411)
        ·
          refine ⟨22819578726901634310108617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15213052484601089540072411 22819578726901634310108617)
          ·
            refine ⟨17114684045176225732581463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22819578726901634310108617 17114684045176225732581463)
            ·
              refine ⟨25672026067764338598872195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114684045176225732581463 25672026067764338598872195)
              ·
                refine ⟨38508039101646507898308293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25672026067764338598872195 38508039101646507898308293)
                ·
                  refine ⟨7220257331558720230932805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38508039101646507898308293 7220257331558720230932805)
                  ·
                    refine ⟨1353798249667260043299901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220257331558720230932805 1353798249667260043299901)
                    ·
                      rfl

theorem cell23_7909538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7909538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909538 prefixEnd_7909538 := by exact prefixLift 7909538
  have htrace : WordTrace (prefixWord ++ tailWord_7909538) baseStart_7909538 baseEnd_7909538 := by
    simpa [prefixWord, tailWord_7909538, baseEnd_7909538] using wordTrace_append hprefix tailTrace_7909538
  have hstable : (prefixWord ++ tailWord_7909538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909538).length < 2 ^ (prefixWord ++ tailWord_7909538).sum := by decide
  have hdescent : baseEnd_7909538 < baseStart_7909538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909571 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 7, 3, 2]
def baseStart_7909571 : Nat := 118140960795 + 7909571 * 2 ^ 59
def prefixEnd_7909571 : Nat := 4983230072969 + 3 ^ 40 * 7909571 * 2
def baseEnd_7909571 : Nat := 4061411693863378500787051

theorem tailTrace_7909571 : CollatzResearch.WordTrace tailWord_7909571 prefixEnd_7909571 4061411693863378500787051 := by
  unfold tailWord_7909571
  simp only [CollatzResearch.WordTrace]
  refine ⟨288485754427982589025472567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192323836285321726016981711 288485754427982589025472567)
  ·
    refine ⟨432728631641973883538208851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288485754427982589025472567 432728631641973883538208851)
    ·
      refine ⟨649092947462960825307313277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432728631641973883538208851 649092947462960825307313277)
      ·
        refine ⟨243409855298610309490242479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649092947462960825307313277 243409855298610309490242479)
        ·
          refine ⟨365114782947915464235363719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243409855298610309490242479 365114782947915464235363719)
          ·
            refine ⟨547672174421873196353045579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365114782947915464235363719 547672174421873196353045579)
            ·
              refine ⟨821508261632809794529568369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547672174421873196353045579 821508261632809794529568369)
              ·
                refine ⟨616131196224607345897176277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821508261632809794529568369 616131196224607345897176277)
                ·
                  refine ⟨14440574911514234669465069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 616131196224607345897176277 14440574911514234669465069)
                  ·
                    refine ⟨5415215591817838001049401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14440574911514234669465069 5415215591817838001049401)
                    ·
                      refine ⟨4061411693863378500787051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415215591817838001049401 4061411693863378500787051)
                      ·
                        rfl

theorem cell23_7909571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_7909571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909571 prefixEnd_7909571 := by exact prefixLift 7909571
  have htrace : WordTrace (prefixWord ++ tailWord_7909571) baseStart_7909571 baseEnd_7909571 := by
    simpa [prefixWord, tailWord_7909571, baseEnd_7909571] using wordTrace_append hprefix tailTrace_7909571
  have hstable : (prefixWord ++ tailWord_7909571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909571).length < 2 ^ (prefixWord ++ tailWord_7909571).sum := by decide
  have hdescent : baseEnd_7909571 < baseStart_7909571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909594 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_7909594 : Nat := 118140960795 + 7909594 * 2 ^ 59
def prefixEnd_7909594 : Nat := 4983230072969 + 3 ^ 40 * 7909594 * 2
def baseEnd_7909594 : Nat := 1353807834639477303599815

theorem tailTrace_7909594 : CollatzResearch.WordTrace tailWord_7909594 prefixEnd_7909594 1353807834639477303599815 := by
  unfold tailWord_7909594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72121648326724815988389959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192324395537932842635706557 72121648326724815988389959)
  ·
    refine ⟨108182472490087223982584939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72121648326724815988389959 108182472490087223982584939)
    ·
      refine ⟨162273708735130835973877409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108182472490087223982584939 162273708735130835973877409)
      ·
        refine ⟨121705281551348126980408057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162273708735130835973877409 121705281551348126980408057)
        ·
          refine ⟨91278961163511095235306043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121705281551348126980408057 91278961163511095235306043)
          ·
            refine ⟨136918441745266642852959065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91278961163511095235306043 136918441745266642852959065)
            ·
              refine ⟨102688831308949982139719299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136918441745266642852959065 102688831308949982139719299)
              ·
                refine ⟨154033246963424973209578949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102688831308949982139719299 154033246963424973209578949)
                ·
                  refine ⟨28881233805642182476796053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154033246963424973209578949 28881233805642182476796053)
                  ·
                    refine ⟨1353807834639477303599815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28881233805642182476796053 1353807834639477303599815)
                    ·
                      rfl

theorem cell23_7909594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_7909594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909594 prefixEnd_7909594 := by exact prefixLift 7909594
  have htrace : WordTrace (prefixWord ++ tailWord_7909594) baseStart_7909594 baseEnd_7909594 := by
    simpa [prefixWord, tailWord_7909594, baseEnd_7909594] using wordTrace_append hprefix tailTrace_7909594
  have hstable : (prefixWord ++ tailWord_7909594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909594).length < 2 ^ (prefixWord ++ tailWord_7909594).sum := by decide
  have hdescent : baseEnd_7909594 < baseStart_7909594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909596 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7909596 : Nat := 118140960795 + 7909596 * 2 ^ 59
def prefixEnd_7909596 : Nat := 4983230072969 + 3 ^ 40 * 7909596 * 2
def baseEnd_7909596 : Nat := 4061424530879740902974437

theorem tailTrace_7909596 : CollatzResearch.WordTrace tailWord_7909596 prefixEnd_7909596 4061424530879740902974437 := by
  unfold tailWord_7909596
  simp only [CollatzResearch.WordTrace]
  refine ⟨144243333126446009147566321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192324444168594678863421761 144243333126446009147566321)
  ·
    refine ⟨108182499844834506860674741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144243333126446009147566321 108182499844834506860674741)
    ·
      refine ⟨10142109360453235018188257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108182499844834506860674741 10142109360453235018188257)
      ·
        refine ⟨7606582020339926263641193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10142109360453235018188257 7606582020339926263641193)
        ·
          refine ⟨5704936515254944697730895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606582020339926263641193 5704936515254944697730895)
          ·
            refine ⟨8557404772882417046596343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704936515254944697730895 8557404772882417046596343)
            ·
              refine ⟨12836107159323625569894515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557404772882417046596343 12836107159323625569894515)
              ·
                refine ⟨19254160738985438354841773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836107159323625569894515 19254160738985438354841773)
                ·
                  refine ⟨7220310277119539383065665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19254160738985438354841773 7220310277119539383065665)
                  ·
                    refine ⟨5415232707839654537299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220310277119539383065665 5415232707839654537299249)
                    ·
                      refine ⟨4061424530879740902974437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415232707839654537299249 4061424530879740902974437)
                      ·
                        rfl

theorem cell23_7909596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7909596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909596 prefixEnd_7909596 := by exact prefixLift 7909596
  have htrace : WordTrace (prefixWord ++ tailWord_7909596) baseStart_7909596 baseEnd_7909596 := by
    simpa [prefixWord, tailWord_7909596, baseEnd_7909596] using wordTrace_append hprefix tailTrace_7909596
  have hstable : (prefixWord ++ tailWord_7909596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909596).length < 2 ^ (prefixWord ++ tailWord_7909596).sum := by decide
  have hdescent : baseEnd_7909596 < baseStart_7909596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909604 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7909604 : Nat := 118140960795 + 7909604 * 2 ^ 59
def prefixEnd_7909604 : Nat := 4983230072969 + 3 ^ 40 * 7909604 * 2
def baseEnd_7909604 : Nat := 4061428638724976871674399

theorem tailTrace_7909604 : CollatzResearch.WordTrace tailWord_7909604 prefixEnd_7909604 4061428638724976871674399 := by
  unfold tailWord_7909604
  simp only [CollatzResearch.WordTrace]
  refine ⟨144243479018431517830711933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192324638691242023774282577 144243479018431517830711933)
  ·
    refine ⟨54091304631911819186516975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144243479018431517830711933 54091304631911819186516975)
    ·
      refine ⟨81136956947867728779775463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54091304631911819186516975 81136956947867728779775463)
      ·
        refine ⟨121705435421801593169663195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81136956947867728779775463 121705435421801593169663195)
        ·
          refine ⟨182558153132702389754494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121705435421801593169663195 182558153132702389754494793)
          ·
            refine ⟨136918614849526792315871095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182558153132702389754494793 136918614849526792315871095)
            ·
              refine ⟨205377922274290188473806643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136918614849526792315871095 205377922274290188473806643)
              ·
                refine ⟨308066883411435282710709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205377922274290188473806643 308066883411435282710709965)
                ·
                  refine ⟨115525081279288231016516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308066883411435282710709965 115525081279288231016516237)
                  ·
                    refine ⟨43321905479733086631193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115525081279288231016516237 43321905479733086631193589)
                    ·
                      refine ⟨4061428638724976871674399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43321905479733086631193589 4061428638724976871674399)
                      ·
                        rfl

theorem cell23_7909604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7909604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909604 prefixEnd_7909604 := by exact prefixLift 7909604
  have htrace : WordTrace (prefixWord ++ tailWord_7909604) baseStart_7909604 baseEnd_7909604 := by
    simpa [prefixWord, tailWord_7909604, baseEnd_7909604] using wordTrace_append hprefix tailTrace_7909604
  have hstable : (prefixWord ++ tailWord_7909604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909604).length < 2 ^ (prefixWord ++ tailWord_7909604).sum := by decide
  have hdescent : baseEnd_7909604 < baseStart_7909604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909624 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 7]
def baseStart_7909624 : Nat := 118140960795 + 7909624 * 2 ^ 59
def prefixEnd_7909624 : Nat := 4983230072969 + 3 ^ 40 * 7909624 * 2
def baseEnd_7909624 : Nat := 451270989815340754824923

theorem tailTrace_7909624 : CollatzResearch.WordTrace tailWord_7909624 prefixEnd_7909624 451270989815340754824923 := by
  unfold tailWord_7909624
  simp only [CollatzResearch.WordTrace]
  refine ⟨144243843748395289538575963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192325124997860386051434617 144243843748395289538575963)
  ·
    refine ⟨216365765622592934307863945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144243843748395289538575963 216365765622592934307863945)
    ·
      refine ⟨162274324216944700730897959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216365765622592934307863945 162274324216944700730897959)
      ·
        refine ⟨243411486325417051096346939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162274324216944700730897959 243411486325417051096346939)
        ·
          refine ⟨365117229488125576644520409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243411486325417051096346939 365117229488125576644520409)
          ·
            refine ⟨273837922116094182483390307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365117229488125576644520409 273837922116094182483390307)
            ·
              refine ⟨410756883174141273725085461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273837922116094182483390307 410756883174141273725085461)
              ·
                refine ⟨19254228898787872205863381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 410756883174141273725085461 19254228898787872205863381)
                ·
                  refine ⟨451270989815340754824923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19254228898787872205863381 451270989815340754824923)
                  ·
                    rfl

theorem cell23_7909624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_7909624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909624 prefixEnd_7909624 := by exact prefixLift 7909624
  have htrace : WordTrace (prefixWord ++ tailWord_7909624) baseStart_7909624 baseEnd_7909624 := by
    simpa [prefixWord, tailWord_7909624, baseEnd_7909624] using wordTrace_append hprefix tailTrace_7909624
  have hstable : (prefixWord ++ tailWord_7909624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909624).length < 2 ^ (prefixWord ++ tailWord_7909624).sum := by decide
  have hdescent : baseEnd_7909624 < baseStart_7909624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909639 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7909639 : Nat := 118140960795 + 7909639 * 2 ^ 59
def prefixEnd_7909639 : Nat := 4983230072969 + 3 ^ 40 * 7909639 * 2
def baseEnd_7909639 : Nat := 4061446610547884234736739

theorem tailTrace_7909639 : CollatzResearch.WordTrace tailWord_7909639 prefixEnd_7909639 4061446610547884234736739 := by
  unfold tailWord_7909639
  simp only [CollatzResearch.WordTrace]
  refine ⟨288488234591736236638947971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192325489727824157759298647 288488234591736236638947971)
  ·
    refine ⟨432732351887604354958421957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288488234591736236638947971 432732351887604354958421957)
    ·
      refine ⟨81137315978925816554704117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432732351887604354958421957 81137315978925816554704117)
      ·
        refine ⟨7606623373024295302003511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81137315978925816554704117 7606623373024295302003511)
        ·
          refine ⟨11409935059536442953005267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606623373024295302003511 11409935059536442953005267)
          ·
            refine ⟨17114902589304664429507901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409935059536442953005267 17114902589304664429507901)
            ·
              refine ⟨6418088470989249161065463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17114902589304664429507901 6418088470989249161065463)
              ·
                refine ⟨9627132706483873741598195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418088470989249161065463 9627132706483873741598195)
                ·
                  refine ⟨14440699059725810612397293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9627132706483873741598195 14440699059725810612397293)
                  ·
                    refine ⟨5415262147397178979648985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14440699059725810612397293 5415262147397178979648985)
                    ·
                      refine ⟨4061446610547884234736739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415262147397178979648985 4061446610547884234736739)
                      ·
                        rfl

theorem cell23_7909639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7909639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909639 prefixEnd_7909639 := by exact prefixLift 7909639
  have htrace : WordTrace (prefixWord ++ tailWord_7909639) baseStart_7909639 baseEnd_7909639 := by
    simpa [prefixWord, tailWord_7909639, baseEnd_7909639] using wordTrace_append hprefix tailTrace_7909639
  have hstable : (prefixWord ++ tailWord_7909639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909639).length < 2 ^ (prefixWord ++ tailWord_7909639).sum := by decide
  have hdescent : baseEnd_7909639 < baseStart_7909639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909668 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_7909668 : Nat := 118140960795 + 7909668 * 2 ^ 59
def prefixEnd_7909668 : Nat := 4983230072969 + 3 ^ 40 * 7909668 * 2
def baseEnd_7909668 : Nat := 4061461501486864621274105

theorem tailTrace_7909668 : CollatzResearch.WordTrace tailWord_7909668 prefixEnd_7909668 4061461501486864621274105 := by
  unfold tailWord_7909668
  simp only [CollatzResearch.WordTrace]
  refine ⟨144244646154315587295876829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192326194872420783061169105 144244646154315587295876829)
  ·
    refine ⟨54091742307868345235953811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144244646154315587295876829 54091742307868345235953811)
    ·
      refine ⟨81137613461802517853930717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54091742307868345235953811 81137613461802517853930717)
      ·
        refine ⟨30426605048175944195224019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81137613461802517853930717 30426605048175944195224019)
        ·
          refine ⟨45639907572263916292836029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30426605048175944195224019 45639907572263916292836029)
          ·
            refine ⟨17114965339598968609813511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45639907572263916292836029 17114965339598968609813511)
            ·
              refine ⟨25672448009398452914720267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114965339598968609813511 25672448009398452914720267)
              ·
                refine ⟨38508672014097679372080401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25672448009398452914720267 38508672014097679372080401)
                ·
                  refine ⟨28881504010573259529060301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38508672014097679372080401 28881504010573259529060301)
                  ·
                    refine ⟨10830564003964972323397613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28881504010573259529060301 10830564003964972323397613)
                    ·
                      refine ⟨4061461501486864621274105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830564003964972323397613 4061461501486864621274105)
                      ·
                        rfl

theorem cell23_7909668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_7909668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909668 prefixEnd_7909668 := by exact prefixLift 7909668
  have htrace : WordTrace (prefixWord ++ tailWord_7909668) baseStart_7909668 baseEnd_7909668 := by
    simpa [prefixWord, tailWord_7909668, baseEnd_7909668] using wordTrace_append hprefix tailTrace_7909668
  have hstable : (prefixWord ++ tailWord_7909668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909668).length < 2 ^ (prefixWord ++ tailWord_7909668).sum := by decide
  have hdescent : baseEnd_7909668 < baseStart_7909668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909708 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_7909708 : Nat := 118140960795 + 7909708 * 2 ^ 59
def prefixEnd_7909708 : Nat := 4983230072969 + 3 ^ 40 * 7909708 * 2
def baseEnd_7909708 : Nat := 4061482040713044464773921

theorem tailTrace_7909708 : CollatzResearch.WordTrace tailWord_7909708 prefixEnd_7909708 4061482040713044464773921 := by
  unfold tailWord_7909708
  simp only [CollatzResearch.WordTrace]
  refine ⟨144245375614243130711604889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192327167485657507615473185 144245375614243130711604889)
  ·
    refine ⟨108184031710682348033703667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144245375614243130711604889 108184031710682348033703667)
    ·
      refine ⟨162276047566023522050555501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108184031710682348033703667 162276047566023522050555501)
      ·
        refine ⟨60853517837258820768958313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162276047566023522050555501 60853517837258820768958313)
        ·
          refine ⟨45640138377944115576718735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60853517837258820768958313 45640138377944115576718735)
          ·
            refine ⟨68460207566916173365078103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45640138377944115576718735 68460207566916173365078103)
            ·
              refine ⟨102690311350374260047617155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68460207566916173365078103 102690311350374260047617155)
              ·
                refine ⟨154035467025561390071425733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102690311350374260047617155 154035467025561390071425733)
                ·
                  refine ⟨28881650067292760638392325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154035467025561390071425733 28881650067292760638392325)
                  ·
                    refine ⟨5415309387617392619698561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28881650067292760638392325 5415309387617392619698561)
                    ·
                      refine ⟨4061482040713044464773921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415309387617392619698561 4061482040713044464773921)
                      ·
                        rfl

theorem cell23_7909708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_7909708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909708 prefixEnd_7909708 := by exact prefixLift 7909708
  have htrace : WordTrace (prefixWord ++ tailWord_7909708) baseStart_7909708 baseEnd_7909708 := by
    simpa [prefixWord, tailWord_7909708, baseEnd_7909708] using wordTrace_append hprefix tailTrace_7909708
  have hstable : (prefixWord ++ tailWord_7909708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909708).length < 2 ^ (prefixWord ++ tailWord_7909708).sum := by decide
  have hdescent : baseEnd_7909708 < baseStart_7909708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909781 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7909781 : Nat := 118140960795 + 7909781 * 2 ^ 59
def prefixEnd_7909781 : Nat := 4983230072969 + 3 ^ 40 * 7909781 * 2
def baseEnd_7909781 : Nat := 4061519524800822679161085

theorem tailTrace_7909781 : CollatzResearch.WordTrace tailWord_7909781 prefixEnd_7909781 4061519524800822679161085 := by
  unfold tailWord_7909781
  simp only [CollatzResearch.WordTrace]
  refine ⟨288493413757221794890617197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192328942504814529927078131 288493413757221794890617197)
  ·
    refine ⟨108185030158958173083981449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288493413757221794890617197 108185030158958173083981449)
    ·
      refine ⟨81138772619218629812986087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108185030158958173083981449 81138772619218629812986087)
      ·
        refine ⟨121708158928827944719479131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81138772619218629812986087 121708158928827944719479131)
        ·
          refine ⟨182562238393241917079218697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121708158928827944719479131 182562238393241917079218697)
          ·
            refine ⟨136921678794931437809414023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182562238393241917079218697 136921678794931437809414023)
            ·
              refine ⟨205382518192397156714121035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136921678794931437809414023 205382518192397156714121035)
              ·
                refine ⟨308073777288595735071181553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205382518192397156714121035 308073777288595735071181553)
                ·
                  refine ⟨231055332966446801303386165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308073777288595735071181553 231055332966446801303386165)
                  ·
                    refine ⟨21661437465604387622192453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231055332966446801303386165 21661437465604387622192453)
                    ·
                      refine ⟨4061519524800822679161085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21661437465604387622192453 4061519524800822679161085)
                      ·
                        rfl

theorem cell23_7909781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7909781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909781 prefixEnd_7909781 := by exact prefixLift 7909781
  have htrace : WordTrace (prefixWord ++ tailWord_7909781) baseStart_7909781 baseEnd_7909781 := by
    simpa [prefixWord, tailWord_7909781, baseEnd_7909781] using wordTrace_append hprefix tailTrace_7909781
  have hstable : (prefixWord ++ tailWord_7909781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909781).length < 2 ^ (prefixWord ++ tailWord_7909781).sum := by decide
  have hdescent : baseEnd_7909781 < baseStart_7909781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909795 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 1, 5]
def baseStart_7909795 : Nat := 118140960795 + 7909795 * 2 ^ 59
def prefixEnd_7909795 : Nat := 4983230072969 + 3 ^ 40 * 7909795 * 2
def baseEnd_7909795 : Nat := 1353842237843328541462007

theorem tailTrace_7909795 : CollatzResearch.WordTrace tailWord_7909795 prefixEnd_7909795 1353842237843328541462007 := by
  unfold tailWord_7909795
  simp only [CollatzResearch.WordTrace]
  refine ⟨288493924379171075281626839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192329282919447383521084559 288493924379171075281626839)
  ·
    refine ⟨432740886568756612922440259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288493924379171075281626839 432740886568756612922440259)
    ·
      refine ⟨649111329853134919383660389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432740886568756612922440259 649111329853134919383660389)
      ·
        refine ⟨121708374347462797384436323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649111329853134919383660389 121708374347462797384436323)
        ·
          refine ⟨182562561521194196076654485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121708374347462797384436323 182562561521194196076654485)
          ·
            refine ⟨8557620071305977941093179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182562561521194196076654485 8557620071305977941093179)
            ·
              refine ⟨12836430106958966911639769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557620071305977941093179 12836430106958966911639769)
              ·
                refine ⟨9627322580219225183729827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12836430106958966911639769 9627322580219225183729827)
                ·
                  refine ⟨14440983870328837775594741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9627322580219225183729827 14440983870328837775594741)
                  ·
                    refine ⟨1353842237843328541462007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14440983870328837775594741 1353842237843328541462007)
                    ·
                      rfl

theorem cell23_7909795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 5].length) (baseStart_7909795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909795 prefixEnd_7909795 := by exact prefixLift 7909795
  have htrace : WordTrace (prefixWord ++ tailWord_7909795) baseStart_7909795 baseEnd_7909795 := by
    simpa [prefixWord, tailWord_7909795, baseEnd_7909795] using wordTrace_append hprefix tailTrace_7909795
  have hstable : (prefixWord ++ tailWord_7909795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909795).length < 2 ^ (prefixWord ++ tailWord_7909795).sum := by decide
  have hdescent : baseEnd_7909795 < baseStart_7909795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909801 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_7909801 : Nat := 118140960795 + 7909801 * 2 ^ 59
def prefixEnd_7909801 : Nat := 4983230072969 + 3 ^ 40 * 7909801 * 2
def baseEnd_7909801 : Nat := 4061529794413912600910993

theorem tailTrace_7909801 : CollatzResearch.WordTrace tailWord_7909801 prefixEnd_7909801 4061529794413912600910993 := by
  unfold tailWord_7909801
  simp only [CollatzResearch.WordTrace]
  refine ⟨288494143217149338306345257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192329428811432892204230171 288494143217149338306345257)
  ·
    refine ⟨216370607412862003729758943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288494143217149338306345257 216370607412862003729758943)
    ·
      refine ⟨324555911119293005594638415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216370607412862003729758943 324555911119293005594638415)
      ·
        refine ⟨486833866678939508391957623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324555911119293005594638415 486833866678939508391957623)
        ·
          refine ⟨730250800018409262587936435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486833866678939508391957623 730250800018409262587936435)
          ·
            refine ⟨1095376200027613893881904653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730250800018409262587936435 1095376200027613893881904653)
            ·
              refine ⟨410766075010355210205714245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095376200027613893881904653 410766075010355210205714245)
              ·
                refine ⟨77018639064441601913571421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410766075010355210205714245 77018639064441601913571421)
                ·
                  refine ⟨28881989649165600717589283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77018639064441601913571421 28881989649165600717589283)
                  ·
                    refine ⟨43322984473748401076383925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28881989649165600717589283 43322984473748401076383925)
                    ·
                      refine ⟨4061529794413912600910993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43322984473748401076383925 4061529794413912600910993)
                      ·
                        rfl

theorem cell23_7909801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_7909801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909801 prefixEnd_7909801 := by exact prefixLift 7909801
  have htrace : WordTrace (prefixWord ++ tailWord_7909801) baseStart_7909801 baseEnd_7909801 := by
    simpa [prefixWord, tailWord_7909801, baseEnd_7909801] using wordTrace_append hprefix tailTrace_7909801
  have hstable : (prefixWord ++ tailWord_7909801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909801).length < 2 ^ (prefixWord ++ tailWord_7909801).sum := by decide
  have hdescent : baseEnd_7909801 < baseStart_7909801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909821 : List Nat := [1, 4, 1, 2, 2, 13]
def baseStart_7909821 : Nat := 118140960795 + 7909821 * 2 ^ 59
def prefixEnd_7909821 : Nat := 4983230072969 + 3 ^ 40 * 7909821 * 2
def baseEnd_7909821 : Nat := 16714156642086430134407

theorem tailTrace_7909821 : CollatzResearch.WordTrace tailWord_7909821 prefixEnd_7909821 16714156642086430134407 := by
  unfold tailWord_7909821
  simp only [CollatzResearch.WordTrace]
  refine ⟨288494872677076881722073317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192329915118051254481382211 288494872677076881722073317)
  ·
    refine ⟨54092788626951915322888747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288494872677076881722073317 54092788626951915322888747)
    ·
      refine ⟨81139182940427872984333121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54092788626951915322888747 81139182940427872984333121)
      ·
        refine ⟨60854387205320904738249841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81139182940427872984333121 60854387205320904738249841)
        ·
          refine ⟨45640790403990678553687381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60854387205320904738249841 45640790403990678553687381)
          ·
            refine ⟨16714156642086430134407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45640790403990678553687381 16714156642086430134407)
            ·
              rfl

theorem cell23_7909821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 13].length) (baseStart_7909821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909821 prefixEnd_7909821 := by exact prefixLift 7909821
  have htrace : WordTrace (prefixWord ++ tailWord_7909821) baseStart_7909821 baseEnd_7909821 := by
    simpa [prefixWord, tailWord_7909821, baseEnd_7909821] using wordTrace_append hprefix tailTrace_7909821
  have hstable : (prefixWord ++ tailWord_7909821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909821).length < 2 ^ (prefixWord ++ tailWord_7909821).sum := by decide
  have hdescent : baseEnd_7909821 < baseStart_7909821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909841 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_7909841 : Nat := 118140960795 + 7909841 * 2 ^ 59
def prefixEnd_7909841 : Nat := 4983230072969 + 3 ^ 40 * 7909841 * 2
def baseEnd_7909841 : Nat := 4061550333640092444410809

theorem tailTrace_7909841 : CollatzResearch.WordTrace tailWord_7909841 prefixEnd_7909841 4061550333640092444410809 := by
  unfold tailWord_7909841
  simp only [CollatzResearch.WordTrace]
  refine ⟨288495602137004425137801377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192330401424669616758534251 288495602137004425137801377)
  ·
    refine ⟨216371701602753318853351033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288495602137004425137801377 216371701602753318853351033)
    ·
      refine ⟨162278776202064989140013275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216371701602753318853351033 162278776202064989140013275)
      ·
        refine ⟨243418164303097483710019913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162278776202064989140013275 243418164303097483710019913)
        ·
          refine ⟨182563623227323112782514935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243418164303097483710019913 182563623227323112782514935)
          ·
            refine ⟨273845434840984669173772403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182563623227323112782514935 273845434840984669173772403)
            ·
              refine ⟨410768152261477003760658605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273845434840984669173772403 410768152261477003760658605)
              ·
                refine ⟨154038057098053876410246977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410768152261477003760658605 154038057098053876410246977)
                ·
                  refine ⟨115528542823540407307685233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154038057098053876410246977 115528542823540407307685233)
                  ·
                    refine ⟨86646407117655305480763925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115528542823540407307685233 86646407117655305480763925)
                    ·
                      refine ⟨4061550333640092444410809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86646407117655305480763925 4061550333640092444410809)
                      ·
                        rfl

theorem cell23_7909841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_7909841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909841 prefixEnd_7909841 := by exact prefixLift 7909841
  have htrace : WordTrace (prefixWord ++ tailWord_7909841) baseStart_7909841 baseEnd_7909841 := by
    simpa [prefixWord, tailWord_7909841, baseEnd_7909841] using wordTrace_append hprefix tailTrace_7909841
  have hstable : (prefixWord ++ tailWord_7909841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909841).length < 2 ^ (prefixWord ++ tailWord_7909841).sum := by decide
  have hdescent : baseEnd_7909841 < baseStart_7909841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909842 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_7909842 : Nat := 118140960795 + 7909842 * 2 ^ 59
def prefixEnd_7909842 : Nat := 4983230072969 + 3 ^ 40 * 7909842 * 2
def baseEnd_7909842 : Nat := 1353850282373582313499435

theorem tailTrace_7909842 : CollatzResearch.WordTrace tailWord_7909842 prefixEnd_7909842 1353850282373582313499435 := by
  unfold tailWord_7909842
  simp only [CollatzResearch.WordTrace]
  refine ⟨72123909652500200577146945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192330425740000534872391853 72123909652500200577146945)
  ·
    refine ⟨54092932239375150432860209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72123909652500200577146945 54092932239375150432860209)
    ·
      refine ⟨40569699179531362824645157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54092932239375150432860209 40569699179531362824645157)
      ·
        refine ⟨7606818596162130529620967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40569699179531362824645157 7606818596162130529620967)
        ·
          refine ⟨11410227894243195794431451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606818596162130529620967 11410227894243195794431451)
          ·
            refine ⟨17115341841364793691647177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11410227894243195794431451 17115341841364793691647177)
            ·
              refine ⟨12836506381023595268735383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17115341841364793691647177 12836506381023595268735383)
              ·
                refine ⟨19254759571535392903103075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836506381023595268735383 19254759571535392903103075)
                ·
                  refine ⟨28882139357303089354654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19254759571535392903103075 28882139357303089354654613)
                  ·
                    refine ⟨1353850282373582313499435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28882139357303089354654613 1353850282373582313499435)
                    ·
                      rfl

theorem cell23_7909842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_7909842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909842 prefixEnd_7909842 := by exact prefixLift 7909842
  have htrace : WordTrace (prefixWord ++ tailWord_7909842) baseStart_7909842 baseEnd_7909842 := by
    simpa [prefixWord, tailWord_7909842, baseEnd_7909842] using wordTrace_append hprefix tailTrace_7909842
  have hstable : (prefixWord ++ tailWord_7909842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909842).length < 2 ^ (prefixWord ++ tailWord_7909842).sum := by decide
  have hdescent : baseEnd_7909842 < baseStart_7909842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909845 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7909845 : Nat := 118140960795 + 7909845 * 2 ^ 59
def prefixEnd_7909845 : Nat := 4983230072969 + 3 ^ 40 * 7909845 * 2
def baseEnd_7909845 : Nat := 4061552387562710428760791

theorem tailTrace_7909845 : CollatzResearch.WordTrace tailWord_7909845 prefixEnd_7909845 4061552387562710428760791 := by
  unfold tailWord_7909845
  simp only [CollatzResearch.WordTrace]
  refine ⟨288495748028989933820946989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192330498685993289213964659 288495748028989933820946989)
  ·
    refine ⟨108185905510871225182855121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288495748028989933820946989 108185905510871225182855121)
    ·
      refine ⟨81139429133153418887141341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108185905510871225182855121 81139429133153418887141341)
      ·
        refine ⟨30427285924932532082678003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81139429133153418887141341 30427285924932532082678003)
        ·
          refine ⟨45640928887398798124017005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30427285924932532082678003 45640928887398798124017005)
          ·
            refine ⟨17115348332774549296506377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45640928887398798124017005 17115348332774549296506377)
            ·
              refine ⟨12836511249580911972379783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17115348332774549296506377 12836511249580911972379783)
              ·
                refine ⟨19254766874371367958569675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836511249580911972379783 19254766874371367958569675)
                ·
                  refine ⟨28882150311557051937854513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19254766874371367958569675 28882150311557051937854513)
                  ·
                    refine ⟨21661612733667788953390885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28882150311557051937854513 21661612733667788953390885)
                    ·
                      refine ⟨4061552387562710428760791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21661612733667788953390885 4061552387562710428760791)
                      ·
                        rfl

theorem cell23_7909845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7909845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909845 prefixEnd_7909845 := by exact prefixLift 7909845
  have htrace : WordTrace (prefixWord ++ tailWord_7909845) baseStart_7909845 baseEnd_7909845 := by
    simpa [prefixWord, tailWord_7909845, baseEnd_7909845] using wordTrace_append hprefix tailTrace_7909845
  have hstable : (prefixWord ++ tailWord_7909845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909845).length < 2 ^ (prefixWord ++ tailWord_7909845).sum := by decide
  have hdescent : baseEnd_7909845 < baseStart_7909845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909866 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_7909866 : Nat := 118140960795 + 7909866 * 2 ^ 59
def prefixEnd_7909866 : Nat := 4983230072969 + 3 ^ 40 * 7909866 * 2
def baseEnd_7909866 : Nat := 4061563170656454846598195

theorem tailTrace_7909866 : CollatzResearch.WordTrace tailWord_7909866 prefixEnd_7909866 4061563170656454846598195 := by
  unfold tailWord_7909866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72124128490478463601865363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192331009307942569604974301 72124128490478463601865363)
  ·
    refine ⟨108186192735717695402798045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72124128490478463601865363 108186192735717695402798045)
    ·
      refine ⟨40569822275894135776049267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108186192735717695402798045 40569822275894135776049267)
      ·
        refine ⟨60854733413841203664073901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40569822275894135776049267 60854733413841203664073901)
        ·
          refine ⟨22820525030190451374027713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60854733413841203664073901 22820525030190451374027713)
          ·
            refine ⟨17115393772642838530520785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22820525030190451374027713 17115393772642838530520785)
            ·
              refine ⟨12836545329482128897890589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17115393772642838530520785 12836545329482128897890589)
              ·
                refine ⟨4813704498555798336708971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12836545329482128897890589 4813704498555798336708971)
                ·
                  refine ⟨7220556747833697505063457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813704498555798336708971 7220556747833697505063457)
                  ·
                    refine ⟨5415417560875273128797593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220556747833697505063457 5415417560875273128797593)
                    ·
                      refine ⟨4061563170656454846598195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415417560875273128797593 4061563170656454846598195)
                      ·
                        rfl

theorem cell23_7909866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_7909866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909866 prefixEnd_7909866 := by exact prefixLift 7909866
  have htrace : WordTrace (prefixWord ++ tailWord_7909866) baseStart_7909866 baseEnd_7909866 := by
    simpa [prefixWord, tailWord_7909866, baseEnd_7909866] using wordTrace_append hprefix tailTrace_7909866
  have hstable : (prefixWord ++ tailWord_7909866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909866).length < 2 ^ (prefixWord ++ tailWord_7909866).sum := by decide
  have hdescent : baseEnd_7909866 < baseStart_7909866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909869 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7909869 : Nat := 118140960795 + 7909869 * 2 ^ 59
def prefixEnd_7909869 : Nat := 4983230072969 + 3 ^ 40 * 7909869 * 2
def baseEnd_7909869 : Nat := 4061564711098418334860681

theorem tailTrace_7909869 : CollatzResearch.WordTrace tailWord_7909869 prefixEnd_7909869 4061564711098418334860681 := by
  unfold tailWord_7909869
  simp only [CollatzResearch.WordTrace]
  refine ⟨288496623380902985919820661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192331082253935323946547107 288496623380902985919820661)
  ·
    refine ⟨27046558441959654929983187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288496623380902985919820661 27046558441959654929983187)
    ·
      refine ⟨40569837662939482394974781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27046558441959654929983187 40569837662939482394974781)
      ·
        refine ⟨15213689123602305898115543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40569837662939482394974781 15213689123602305898115543)
        ·
          refine ⟨22820533685403458847173315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15213689123602305898115543 22820533685403458847173315)
          ·
            refine ⟨34230800528105188270759973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22820533685403458847173315 34230800528105188270759973)
            ·
              refine ⟨6418275099019722800767495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34230800528105188270759973 6418275099019722800767495)
              ·
                refine ⟨9627412648529584201151243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418275099019722800767495 9627412648529584201151243)
                ·
                  refine ⟨14441118972794376301726865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9627412648529584201151243 14441118972794376301726865)
                  ·
                    refine ⟨10830839229595782226295149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14441118972794376301726865 10830839229595782226295149)
                    ·
                      refine ⟨4061564711098418334860681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830839229595782226295149 4061564711098418334860681)
                      ·
                        rfl

theorem cell23_7909869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7909869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909869 prefixEnd_7909869 := by exact prefixLift 7909869
  have htrace : WordTrace (prefixWord ++ tailWord_7909869) baseStart_7909869 baseEnd_7909869 := by
    simpa [prefixWord, tailWord_7909869, baseEnd_7909869] using wordTrace_append hprefix tailTrace_7909869
  have hstable : (prefixWord ++ tailWord_7909869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909869).length < 2 ^ (prefixWord ++ tailWord_7909869).sum := by decide
  have hdescent : baseEnd_7909869 < baseStart_7909869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909898 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_7909898 : Nat := 118140960795 + 7909898 * 2 ^ 59
def prefixEnd_7909898 : Nat := 4983230072969 + 3 ^ 40 * 7909898 * 2
def baseEnd_7909898 : Nat := 1353859867345799573799349

theorem tailTrace_7909898 : CollatzResearch.WordTrace tailWord_7909898 prefixEnd_7909898 1353859867345799573799349 := by
  unfold tailWord_7909898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72124420274449480968156587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192331787398531949248417565 72124420274449480968156587)
  ·
    refine ⟨108186630411674221452234881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72124420274449480968156587 108186630411674221452234881)
    ·
      refine ⟨81139972808755666089176161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108186630411674221452234881 81139972808755666089176161)
      ·
        refine ⟨60854979606566749566882121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81139972808755666089176161 60854979606566749566882121)
        ·
          refine ⟨45641234704925062175161591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60854979606566749566882121 45641234704925062175161591)
          ·
            refine ⟨68461852057387593262742387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45641234704925062175161591 68461852057387593262742387)
            ·
              refine ⟨102692778086081389894113581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68461852057387593262742387 102692778086081389894113581)
              ·
                refine ⟨38509791782280521210292593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102692778086081389894113581 38509791782280521210292593)
                ·
                  refine ⟨28882343836710390907719445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38509791782280521210292593 28882343836710390907719445)
                  ·
                    refine ⟨1353859867345799573799349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28882343836710390907719445 1353859867345799573799349)
                    ·
                      rfl

theorem cell23_7909898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_7909898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909898 prefixEnd_7909898 := by exact prefixLift 7909898
  have htrace : WordTrace (prefixWord ++ tailWord_7909898) baseStart_7909898 baseEnd_7909898 := by
    simpa [prefixWord, tailWord_7909898, baseEnd_7909898] using wordTrace_append hprefix tailTrace_7909898
  have hstable : (prefixWord ++ tailWord_7909898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909898).length < 2 ^ (prefixWord ++ tailWord_7909898).sum := by decide
  have hdescent : baseEnd_7909898 < baseStart_7909898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909899 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 2, 1, 3]
def baseStart_7909899 : Nat := 118140960795 + 7909899 * 2 ^ 59
def prefixEnd_7909899 : Nat := 4983230072969 + 3 ^ 40 * 7909899 * 2
def baseEnd_7909899 : Nat := 4061580115518053217485543

theorem tailTrace_7909899 : CollatzResearch.WordTrace tailWord_7909899 prefixEnd_7909899 4061580115518053217485543 := by
  unfold tailWord_7909899
  simp only [CollatzResearch.WordTrace]
  refine ⟨288497717570794301043412751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192331811713862867362275167 288497717570794301043412751)
  ·
    refine ⟨432746576356191451565119127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288497717570794301043412751 432746576356191451565119127)
    ·
      refine ⟨649119864534287177347678691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432746576356191451565119127 649119864534287177347678691)
      ·
        refine ⟨973679796801430766021518037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649119864534287177347678691 973679796801430766021518037)
        ·
          refine ⟨22820620237533533578629329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 973679796801430766021518037 22820620237533533578629329)
          ·
            refine ⟨17115465178150150183971997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22820620237533533578629329 17115465178150150183971997)
            ·
              refine ⟨6418299441806306318989499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17115465178150150183971997 6418299441806306318989499)
              ·
                refine ⟨9627449162709459478484249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418299441806306318989499 9627449162709459478484249)
                ·
                  refine ⟨7220586872032094608863187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627449162709459478484249 7220586872032094608863187)
                  ·
                    refine ⟨10830880308048141913294781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7220586872032094608863187 10830880308048141913294781)
                    ·
                      refine ⟨4061580115518053217485543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830880308048141913294781 4061580115518053217485543)
                      ·
                        rfl

theorem cell23_7909899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 2, 1, 3].length) (baseStart_7909899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909899 prefixEnd_7909899 := by exact prefixLift 7909899
  have htrace : WordTrace (prefixWord ++ tailWord_7909899) baseStart_7909899 baseEnd_7909899 := by
    simpa [prefixWord, tailWord_7909899, baseEnd_7909899] using wordTrace_append hprefix tailTrace_7909899
  have hstable : (prefixWord ++ tailWord_7909899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909899).length < 2 ^ (prefixWord ++ tailWord_7909899).sum := by decide
  have hdescent : baseEnd_7909899 < baseStart_7909899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909905 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_7909905 : Nat := 118140960795 + 7909905 * 2 ^ 59
def prefixEnd_7909905 : Nat := 4983230072969 + 3 ^ 40 * 7909905 * 2
def baseEnd_7909905 : Nat := 4061583196401980194010515

theorem tailTrace_7909905 : CollatzResearch.WordTrace tailWord_7909905 prefixEnd_7909905 4061583196401980194010515 := by
  unfold tailWord_7909905
  simp only [CollatzResearch.WordTrace]
  refine ⟨288497936408772564068131169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192331957605848376045420779 288497936408772564068131169)
  ·
    refine ⟨216373452306579423051098377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288497936408772564068131169 216373452306579423051098377)
    ·
      refine ⟨162280089229934567288323783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216373452306579423051098377 162280089229934567288323783)
      ·
        refine ⟨243420133844901850932485675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162280089229934567288323783 243420133844901850932485675)
        ·
          refine ⟨365130200767352776398728513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243420133844901850932485675 365130200767352776398728513)
          ·
            refine ⟨273847650575514582299046385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365130200767352776398728513 273847650575514582299046385)
            ·
              refine ⟨205385737931635936724284789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273847650575514582299046385 205385737931635936724284789)
              ·
                refine ⟨19254912931090869067901699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205385737931635936724284789 19254912931090869067901699)
                ·
                  refine ⟨28882369396636303601852549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19254912931090869067901699 28882369396636303601852549)
                  ·
                    refine ⟨5415444261869306925347353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28882369396636303601852549 5415444261869306925347353)
                    ·
                      refine ⟨4061583196401980194010515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415444261869306925347353 4061583196401980194010515)
                      ·
                        rfl

theorem cell23_7909905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_7909905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909905 prefixEnd_7909905 := by exact prefixLift 7909905
  have htrace : WordTrace (prefixWord ++ tailWord_7909905) baseStart_7909905 baseEnd_7909905 := by
    simpa [prefixWord, tailWord_7909905, baseEnd_7909905] using wordTrace_append hprefix tailTrace_7909905
  have hstable : (prefixWord ++ tailWord_7909905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909905).length < 2 ^ (prefixWord ++ tailWord_7909905).sum := by decide
  have hdescent : baseEnd_7909905 < baseStart_7909905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909950 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7909950 : Nat := 118140960795 + 7909950 * 2 ^ 59
def prefixEnd_7909950 : Nat := 4983230072969 + 3 ^ 40 * 7909950 * 2
def baseEnd_7909950 : Nat := 4061606303031432517947809

theorem tailTrace_7909950 : CollatzResearch.WordTrace tailWord_7909950 prefixEnd_7909950 4061606303031432517947809 := by
  unfold tailWord_7909950
  simp only [CollatzResearch.WordTrace]
  refine ⟨36062447211701192094189913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192333051795739691169012869 36062447211701192094189913)
  ·
    refine ⟨27046835408775894070642435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36062447211701192094189913 27046835408775894070642435)
    ·
      refine ⟨40570253113163841105963653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27046835408775894070642435 40570253113163841105963653)
      ·
        refine ⟨7606922458718220207368185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40570253113163841105963653 7606922458718220207368185)
        ·
          refine ⟨5705191844038665155526139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606922458718220207368185 5705191844038665155526139)
          ·
            refine ⟨8557787766057997733289209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705191844038665155526139 8557787766057997733289209)
            ·
              refine ⟨6418340824543498299966907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557787766057997733289209 6418340824543498299966907)
              ·
                refine ⟨9627511236815247449950361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418340824543498299966907 9627511236815247449950361)
                ·
                  refine ⟨7220633427611435587462771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627511236815247449950361 7220633427611435587462771)
                  ·
                    refine ⟨10830950141417153381194157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7220633427611435587462771 10830950141417153381194157)
                    ·
                      refine ⟨4061606303031432517947809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10830950141417153381194157 4061606303031432517947809)
                      ·
                        rfl

theorem cell23_7909950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7909950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909950 prefixEnd_7909950 := by exact prefixLift 7909950
  have htrace : WordTrace (prefixWord ++ tailWord_7909950) baseStart_7909950 baseEnd_7909950 := by
    simpa [prefixWord, tailWord_7909950, baseEnd_7909950] using wordTrace_append hprefix tailTrace_7909950
  have hstable : (prefixWord ++ tailWord_7909950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909950).length < 2 ^ (prefixWord ++ tailWord_7909950).sum := by decide
  have hdescent : baseEnd_7909950 < baseStart_7909950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7909975 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 2, 5]
def baseStart_7909975 : Nat := 118140960795 + 7909975 * 2 ^ 59
def prefixEnd_7909975 : Nat := 4983230072969 + 3 ^ 40 * 7909975 * 2
def baseEnd_7909975 : Nat := 1353873046682598306711731

theorem tailTrace_7909975 : CollatzResearch.WordTrace tailWord_7909975 prefixEnd_7909975 1353873046682598306711731 := by
  unfold tailWord_7909975
  simp only [CollatzResearch.WordTrace]
  refine ⟨288500489518518966023179379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192333659679012644015452919 288500489518518966023179379)
  ·
    refine ⟨432750734277778449034769069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288500489518518966023179379 432750734277778449034769069)
    ·
      refine ⟨162281525354166918388038401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432750734277778449034769069 162281525354166918388038401)
      ·
        refine ⟨121711144015625188791028801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162281525354166918388038401 121711144015625188791028801)
        ·
          refine ⟨91283358011718891593271601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121711144015625188791028801 91283358011718891593271601)
          ·
            refine ⟨68462518508789168694953701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91283358011718891593271601 68462518508789168694953701)
            ·
              refine ⟨12836722220397969130303819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68462518508789168694953701 12836722220397969130303819)
              ·
                refine ⟨19255083330596953695455729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836722220397969130303819 19255083330596953695455729)
                ·
                  refine ⟨14441312497947715271591797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19255083330596953695455729 14441312497947715271591797)
                  ·
                    refine ⟨1353873046682598306711731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14441312497947715271591797 1353873046682598306711731)
                    ·
                      rfl

theorem cell23_7909975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_7909975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7909975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7909975 prefixEnd_7909975 := by exact prefixLift 7909975
  have htrace : WordTrace (prefixWord ++ tailWord_7909975) baseStart_7909975 baseEnd_7909975 := by
    simpa [prefixWord, tailWord_7909975, baseEnd_7909975] using wordTrace_append hprefix tailTrace_7909975
  have hstable : (prefixWord ++ tailWord_7909975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7909975).length < 2 ^ (prefixWord ++ tailWord_7909975).sum := by decide
  have hdescent : baseEnd_7909975 < baseStart_7909975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7909975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910008 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_7910008 : Nat := 118140960795 + 7910008 * 2 ^ 59
def prefixEnd_7910008 : Nat := 4983230072969 + 3 ^ 40 * 7910008 * 2
def baseEnd_7910008 : Nat := 4061636084909393291022541

theorem tailTrace_7910008 : CollatzResearch.WordTrace tailWord_7910008 prefixEnd_7910008 4061636084909393291022541 := by
  unfold tailWord_7910008
  simp only [CollatzResearch.WordTrace]
  refine ⟨144250846563699706329565339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192334462084932941772753785 144250846563699706329565339)
  ·
    refine ⟨216376269845549559494348009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144250846563699706329565339 216376269845549559494348009)
    ·
      refine ⟨162282202384162169620761007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216376269845549559494348009 162282202384162169620761007)
      ·
        refine ⟨243423303576243254431141511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162282202384162169620761007 243423303576243254431141511)
        ·
          refine ⟨365134955364364881646712267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243423303576243254431141511 365134955364364881646712267)
          ·
            refine ⟨547702433046547322470068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365134955364364881646712267 547702433046547322470068401)
            ·
              refine ⟨410776824784910491852551301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547702433046547322470068401 410776824784910491852551301)
              ·
                refine ⟨77020654647170717222353369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410776824784910491852551301 77020654647170717222353369)
                ·
                  refine ⟨57765490985378037916765027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77020654647170717222353369 57765490985378037916765027)
                  ·
                    refine ⟨86648236478067056875147541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57765490985378037916765027 86648236478067056875147541)
                    ·
                      refine ⟨4061636084909393291022541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86648236478067056875147541 4061636084909393291022541)
                      ·
                        rfl

theorem cell23_7910008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_7910008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910008 prefixEnd_7910008 := by exact prefixLift 7910008
  have htrace : WordTrace (prefixWord ++ tailWord_7910008) baseStart_7910008 baseEnd_7910008 := by
    simpa [prefixWord, tailWord_7910008, baseEnd_7910008] using wordTrace_append hprefix tailTrace_7910008
  have hstable : (prefixWord ++ tailWord_7910008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910008).length < 2 ^ (prefixWord ++ tailWord_7910008).sum := by decide
  have hdescent : baseEnd_7910008 < baseStart_7910008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910039 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 1, 4]
def baseStart_7910039 : Nat := 118140960795 + 7910039 * 2 ^ 59
def prefixEnd_7910039 : Nat := 4983230072969 + 3 ^ 40 * 7910039 * 2
def baseEnd_7910039 : Nat := 1353884000936560889911633

theorem tailTrace_7910039 : CollatzResearch.WordTrace tailWord_7910039 prefixEnd_7910039 1353884000936560889911633 := by
  unfold tailWord_7910039
  simp only [CollatzResearch.WordTrace]
  refine ⟨288502823790287104953509171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192335215860191403302339447 288502823790287104953509171)
  ·
    refine ⟨432754235685430657430263757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288502823790287104953509171 432754235685430657430263757)
    ·
      refine ⟨162282838382036496536348909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432754235685430657430263757 162282838382036496536348909)
      ·
        refine ⟨60856064393263686201130841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162282838382036496536348909 60856064393263686201130841)
        ·
          refine ⟨45642048294947764650848131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60856064393263686201130841 45642048294947764650848131)
          ·
            refine ⟨68463072442421646976272197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45642048294947764650848131 68463072442421646976272197)
            ·
              refine ⟨12836826082954058808051037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68463072442421646976272197 12836826082954058808051037)
              ·
                refine ⟨4813809781107772053019139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12836826082954058808051037 4813809781107772053019139)
                ·
                  refine ⟨7220714671661658079528709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813809781107772053019139 7220714671661658079528709)
                  ·
                    refine ⟨1353884000936560889911633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220714671661658079528709 1353884000936560889911633)
                    ·
                      rfl

theorem cell23_7910039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_7910039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910039 prefixEnd_7910039 := by exact prefixLift 7910039
  have htrace : WordTrace (prefixWord ++ tailWord_7910039) baseStart_7910039 baseEnd_7910039 := by
    simpa [prefixWord, tailWord_7910039, baseEnd_7910039] using wordTrace_append hprefix tailTrace_7910039
  have hstable : (prefixWord ++ tailWord_7910039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910039).length < 2 ^ (prefixWord ++ tailWord_7910039).sum := by decide
  have hdescent : baseEnd_7910039 < baseStart_7910039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910069 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 6]
def baseStart_7910069 : Nat := 118140960795 + 7910069 * 2 ^ 59
def prefixEnd_7910069 : Nat := 4983230072969 + 3 ^ 40 * 7910069 * 2
def baseEnd_7910069 : Nat := 451296378581035283595529

theorem tailTrace_7910069 : CollatzResearch.WordTrace tailWord_7910069 prefixEnd_7910069 451296378581035283595529 := by
  unfold tailWord_7910069
  simp only [CollatzResearch.WordTrace]
  refine ⟨288503917980178420077101261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192335945320118946718067507 288503917980178420077101261)
  ·
    refine ⟨108188969242566907528912973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288503917980178420077101261 108188969242566907528912973)
    ·
      refine ⟨40570863465962590323342365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108188969242566907528912973 40570863465962590323342365)
      ·
        refine ⟨15214073799735971371253387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40570863465962590323342365 15214073799735971371253387)
        ·
          refine ⟨22821110699603957056880081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214073799735971371253387 22821110699603957056880081)
          ·
            refine ⟨17115833024702967792660061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821110699603957056880081 17115833024702967792660061)
            ·
              refine ⟨6418437384263612922247523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17115833024702967792660061 6418437384263612922247523)
              ·
                refine ⟨9627656076395419383371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418437384263612922247523 9627656076395419383371285)
                ·
                  refine ⟨451296378581035283595529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627656076395419383371285 451296378581035283595529)
                  ·
                    rfl

theorem cell23_7910069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_7910069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910069 prefixEnd_7910069 := by exact prefixLift 7910069
  have htrace : WordTrace (prefixWord ++ tailWord_7910069) baseStart_7910069 baseEnd_7910069 := by
    simpa [prefixWord, tailWord_7910069, baseEnd_7910069] using wordTrace_append hprefix tailTrace_7910069
  have hstable : (prefixWord ++ tailWord_7910069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910069).length < 2 ^ (prefixWord ++ tailWord_7910069).sum := by decide
  have hdescent : baseEnd_7910069 < baseStart_7910069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910112 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_7910112 : Nat := 118140960795 + 7910112 * 2 ^ 59
def prefixEnd_7910112 : Nat := 4983230072969 + 3 ^ 40 * 7910112 * 2
def baseEnd_7910112 : Nat := 1353896495632486961374021

theorem tailTrace_7910112 : CollatzResearch.WordTrace tailWord_7910112 prefixEnd_7910112 1353896495632486961374021 := by
  unfold tailWord_7910112
  simp only [CollatzResearch.WordTrace]
  refine ⟨144252743159511319210458295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192336990879348425613944393 144252743159511319210458295)
  ·
    refine ⟨216379114739266978815687443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144252743159511319210458295 216379114739266978815687443)
    ·
      refine ⟨324568672108900468223531165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216379114739266978815687443 324568672108900468223531165)
      ·
        refine ⟨121713252040837675583824187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324568672108900468223531165 121713252040837675583824187)
        ·
          refine ⟨182569878061256513375736281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121713252040837675583824187 182569878061256513375736281)
          ·
            refine ⟨136927408545942385031802211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182569878061256513375736281 136927408545942385031802211)
            ·
              refine ⟨205391112818913577547703317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136927408545942385031802211 205391112818913577547703317)
              ·
                refine ⟨9627708413386573947548593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205391112818913577547703317 9627708413386573947548593)
                ·
                  refine ⟨7220781310039930460661445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627708413386573947548593 7220781310039930460661445)
                  ·
                    refine ⟨1353896495632486961374021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220781310039930460661445 1353896495632486961374021)
                    ·
                      rfl

theorem cell23_7910112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_7910112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910112 prefixEnd_7910112 := by exact prefixLift 7910112
  have htrace : WordTrace (prefixWord ++ tailWord_7910112) baseStart_7910112 baseEnd_7910112 := by
    simpa [prefixWord, tailWord_7910112, baseEnd_7910112] using wordTrace_append hprefix tailTrace_7910112
  have hstable : (prefixWord ++ tailWord_7910112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910112).length < 2 ^ (prefixWord ++ tailWord_7910112).sum := by decide
  have hdescent : baseEnd_7910112 < baseStart_7910112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910113 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_7910113 : Nat := 118140960795 + 7910113 * 2 ^ 59
def prefixEnd_7910113 : Nat := 4983230072969 + 3 ^ 40 * 7910113 * 2
def baseEnd_7910113 : Nat := 4061690000378115380209559

theorem tailTrace_7910113 : CollatzResearch.WordTrace tailWord_7910113 prefixEnd_7910113 4061690000378115380209559 := by
  unfold tailWord_7910113
  simp only [CollatzResearch.WordTrace]
  refine ⟨288505522792019015591702993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192337015194679343727801995 288505522792019015591702993)
  ·
    refine ⟨216379142094014261693777245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288505522792019015591702993 216379142094014261693777245)
    ·
      refine ⟨81142178285255348135166467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216379142094014261693777245 81142178285255348135166467)
      ·
        refine ⟨121713267427883022202749701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81142178285255348135166467 121713267427883022202749701)
        ·
          refine ⟨22821237642728066663015569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121713267427883022202749701 22821237642728066663015569)
          ·
            refine ⟨17115928232046049997261677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821237642728066663015569 17115928232046049997261677)
            ·
              refine ⟨6418473087017268748973129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17115928232046049997261677 6418473087017268748973129)
              ·
                refine ⟨4813854815262951561729847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418473087017268748973129 4813854815262951561729847)
                ·
                  refine ⟨7220782222894427342594771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813854815262951561729847 7220782222894427342594771)
                  ·
                    refine ⟨10831173334341641013892157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7220782222894427342594771 10831173334341641013892157)
                    ·
                      refine ⟨4061690000378115380209559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831173334341641013892157 4061690000378115380209559)
                      ·
                        rfl

theorem cell23_7910113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_7910113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910113 prefixEnd_7910113 := by exact prefixLift 7910113
  have htrace : WordTrace (prefixWord ++ tailWord_7910113) baseStart_7910113 baseEnd_7910113 := by
    simpa [prefixWord, tailWord_7910113, baseEnd_7910113] using wordTrace_append hprefix tailTrace_7910113
  have hstable : (prefixWord ++ tailWord_7910113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910113).length < 2 ^ (prefixWord ++ tailWord_7910113).sum := by decide
  have hdescent : baseEnd_7910113 < baseStart_7910113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910122 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_7910122 : Nat := 118140960795 + 7910122 * 2 ^ 59
def prefixEnd_7910122 : Nat := 4983230072969 + 3 ^ 40 * 7910122 * 2
def baseEnd_7910122 : Nat := 4061694621704005844997017

theorem tailTrace_7910122 : CollatzResearch.WordTrace tailWord_7910122 prefixEnd_7910122 4061694621704005844997017 := by
  unfold tailWord_7910122
  simp only [CollatzResearch.WordTrace]
  refine ⟨72126462762246602532195155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192337234032657606752520413 72126462762246602532195155)
  ·
    refine ⟨108189694143369903798292733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72126462762246602532195155 108189694143369903798292733)
    ·
      refine ⟨40571135303763713924359775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108189694143369903798292733 40571135303763713924359775)
      ·
        refine ⟨60856702955645570886539663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571135303763713924359775 60856702955645570886539663)
        ·
          refine ⟨91285054433468356329809495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60856702955645570886539663 91285054433468356329809495)
          ·
            refine ⟨136927581650202534494714243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91285054433468356329809495 136927581650202534494714243)
            ·
              refine ⟨205391372475303801742071365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136927581650202534494714243 205391372475303801742071365)
              ·
                refine ⟨38510882339119462826638381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205391372475303801742071365 38510882339119462826638381)
                ·
                  refine ⟨14441580877169798559989393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38510882339119462826638381 14441580877169798559989393)
                  ·
                    refine ⟨10831185657877348919992045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14441580877169798559989393 10831185657877348919992045)
                    ·
                      refine ⟨4061694621704005844997017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831185657877348919992045 4061694621704005844997017)
                      ·
                        rfl

theorem cell23_7910122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_7910122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910122 prefixEnd_7910122 := by exact prefixLift 7910122
  have htrace : WordTrace (prefixWord ++ tailWord_7910122) baseStart_7910122 baseEnd_7910122 := by
    simpa [prefixWord, tailWord_7910122, baseEnd_7910122] using wordTrace_append hprefix tailTrace_7910122
  have hstable : (prefixWord ++ tailWord_7910122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910122).length < 2 ^ (prefixWord ++ tailWord_7910122).sum := by decide
  have hdescent : baseEnd_7910122 < baseStart_7910122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910142 : List Nat := [4, 2, 2, 1, 2, 1, 2, 9]
def baseStart_7910142 : Nat := 118140960795 + 7910142 * 2 ^ 59
def prefixEnd_7910142 : Nat := 4983230072969 + 3 ^ 40 * 7910142 * 2
def baseEnd_7910142 : Nat := 150433514493225769138775

theorem tailTrace_7910142 : CollatzResearch.WordTrace tailWord_7910142 prefixEnd_7910142 150433514493225769138775 := by
  unfold tailWord_7910142
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063322563614244193063585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192337720339275969029672453 36063322563614244193063585)
  ·
    refine ⟨27047491922710683144797689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36063322563614244193063585 27047491922710683144797689)
    ·
      refine ⟨20285618942033012358598267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27047491922710683144797689 20285618942033012358598267)
      ·
        refine ⟨30428428413049518537897401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20285618942033012358598267 30428428413049518537897401)
        ·
          refine ⟨22821321309787138903423051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30428428413049518537897401 22821321309787138903423051)
          ·
            refine ⟨34231981964680708355134577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22821321309787138903423051 34231981964680708355134577)
            ·
              refine ⟨25673986473510531266350933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34231981964680708355134577 25673986473510531266350933)
              ·
                refine ⟨150433514493225769138775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25673986473510531266350933 150433514493225769138775)
                ·
                  rfl

theorem cell23_7910142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_7910142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910142 prefixEnd_7910142 := by exact prefixLift 7910142
  have htrace : WordTrace (prefixWord ++ tailWord_7910142) baseStart_7910142 baseEnd_7910142 := by
    simpa [prefixWord, tailWord_7910142, baseEnd_7910142] using wordTrace_append hprefix tailTrace_7910142
  have hstable : (prefixWord ++ tailWord_7910142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910142).length < 2 ^ (prefixWord ++ tailWord_7910142).sum := by decide
  have hdescent : baseEnd_7910142 < baseStart_7910142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910152 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_7910152 : Nat := 118140960795 + 7910152 * 2 ^ 59
def prefixEnd_7910152 : Nat := 4983230072969 + 3 ^ 40 * 7910152 * 2
def baseEnd_7910152 : Nat := 4061710026123640727621879

theorem tailTrace_7910152 : CollatzResearch.WordTrace tailWord_7910152 prefixEnd_7910152 4061710026123640727621879 := by
  unfold tailWord_7910152
  simp only [CollatzResearch.WordTrace]
  refine ⟨144253472619438862626186355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192337963492585150168248473 144253472619438862626186355)
  ·
    refine ⟨216380208929158293939279533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144253472619438862626186355 216380208929158293939279533)
    ·
      refine ⟨81142578348434360227229825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216380208929158293939279533 81142578348434360227229825)
      ·
        refine ⟨60856933761325770170422369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81142578348434360227229825 60856933761325770170422369)
        ·
          refine ⟨45642700320994327627816777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60856933761325770170422369 45642700320994327627816777)
          ·
            refine ⟨34232025240745745720862583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45642700320994327627816777 34232025240745745720862583)
            ·
              refine ⟨51348037861118618581293875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34232025240745745720862583 51348037861118618581293875)
              ·
                refine ⟨77022056791677927871940813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51348037861118618581293875 77022056791677927871940813)
                ·
                  refine ⟨28883271296879222951977805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77022056791677927871940813 28883271296879222951977805)
                  ·
                    refine ⟨10831226736329708606991677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28883271296879222951977805 10831226736329708606991677)
                    ·
                      refine ⟨4061710026123640727621879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831226736329708606991677 4061710026123640727621879)
                      ·
                        rfl

theorem cell23_7910152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_7910152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910152 prefixEnd_7910152 := by exact prefixLift 7910152
  have htrace : WordTrace (prefixWord ++ tailWord_7910152) baseStart_7910152 baseEnd_7910152 := by
    simpa [prefixWord, tailWord_7910152, baseEnd_7910152] using wordTrace_append hprefix tailTrace_7910152
  have hstable : (prefixWord ++ tailWord_7910152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910152).length < 2 ^ (prefixWord ++ tailWord_7910152).sum := by decide
  have hdescent : baseEnd_7910152 < baseStart_7910152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910185 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_7910185 : Nat := 118140960795 + 7910185 * 2 ^ 59
def prefixEnd_7910185 : Nat := 4983230072969 + 3 ^ 40 * 7910185 * 2
def baseEnd_7910185 : Nat := 1353908990328413032836409

theorem tailTrace_7910185 : CollatzResearch.WordTrace tailWord_7910185 prefixEnd_7910185 1353908990328413032836409 := by
  unfold tailWord_7910185
  simp only [CollatzResearch.WordTrace]
  refine ⟨288508148847758171888324009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192338765898505447925549339 288508148847758171888324009)
  ·
    refine ⟨216381111635818628916243007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288508148847758171888324009 216381111635818628916243007)
    ·
      refine ⟨324571667453727943374364511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216381111635818628916243007 324571667453727943374364511)
      ·
        refine ⟨486857501180591915061546767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324571667453727943374364511 486857501180591915061546767)
        ·
          refine ⟨730286251770887872592320151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486857501180591915061546767 730286251770887872592320151)
          ·
            refine ⟨1095429377656331808888480227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730286251770887872592320151 1095429377656331808888480227)
            ·
              refine ⟨1643144066484497713332720341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095429377656331808888480227 1643144066484497713332720341)
              ·
                refine ⟨38511189058230415156235633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1643144066484497713332720341 38511189058230415156235633)
                ·
                  refine ⟨28883391793672811367176725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38511189058230415156235633 28883391793672811367176725)
                  ·
                    refine ⟨1353908990328413032836409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28883391793672811367176725 1353908990328413032836409)
                    ·
                      rfl

theorem cell23_7910185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_7910185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910185 prefixEnd_7910185 := by exact prefixLift 7910185
  have htrace : WordTrace (prefixWord ++ tailWord_7910185) baseStart_7910185 baseEnd_7910185 := by
    simpa [prefixWord, tailWord_7910185, baseEnd_7910185] using wordTrace_append hprefix tailTrace_7910185
  have hstable : (prefixWord ++ tailWord_7910185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910185).length < 2 ^ (prefixWord ++ tailWord_7910185).sum := by decide
  have hdescent : baseEnd_7910185 < baseStart_7910185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910215 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 11]
def baseStart_7910215 : Nat := 118140960795 + 7910215 * 2 ^ 59
def prefixEnd_7910215 : Nat := 4983230072969 + 3 ^ 40 * 7910215 * 2
def baseEnd_7910215 : Nat := 451304708378319331237121

theorem tailTrace_7910215 : CollatzResearch.WordTrace tailWord_7910215 prefixEnd_7910215 451304708378319331237121 := by
  unfold tailWord_7910215
  simp only [CollatzResearch.WordTrace]
  refine ⟨288509243037649487011916099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192339495358432991341277399 288509243037649487011916099)
  ·
    refine ⟨432763864556474230517874149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288509243037649487011916099 432763864556474230517874149)
    ·
      refine ⟨81143224604338918222101403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432763864556474230517874149 81143224604338918222101403)
      ·
        refine ⟨121714836906508377333152105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81143224604338918222101403 121714836906508377333152105)
        ·
          refine ⟨91286127679881282999864079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121714836906508377333152105 91286127679881282999864079)
          ·
            refine ⟨136929191519821924499796119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91286127679881282999864079 136929191519821924499796119)
            ·
              refine ⟨205393787279732886749694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136929191519821924499796119 205393787279732886749694179)
              ·
                refine ⟨308090680919599330124541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205393787279732886749694179 308090680919599330124541269)
                ·
                  refine ⟨451304708378319331237121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 308090680919599330124541269 451304708378319331237121)
                  ·
                    rfl

theorem cell23_7910215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 11].length) (baseStart_7910215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910215 prefixEnd_7910215 := by exact prefixLift 7910215
  have htrace : WordTrace (prefixWord ++ tailWord_7910215) baseStart_7910215 baseEnd_7910215 := by
    simpa [prefixWord, tailWord_7910215, baseEnd_7910215] using wordTrace_append hprefix tailTrace_7910215
  have hstable : (prefixWord ++ tailWord_7910215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910215).length < 2 ^ (prefixWord ++ tailWord_7910215).sum := by decide
  have hdescent : baseEnd_7910215 < baseStart_7910215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910226 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_7910226 : Nat := 118140960795 + 7910226 * 2 ^ 59
def prefixEnd_7910226 : Nat := 4983230072969 + 3 ^ 40 * 7910226 * 2
def baseEnd_7910226 : Nat := 4061748023692073438096539

theorem tailTrace_7910226 : CollatzResearch.WordTrace tailWord_7910226 prefixEnd_7910226 4061748023692073438096539 := by
  unfold tailWord_7910226
  simp only [CollatzResearch.WordTrace]
  refine ⟨72127411060152408972641633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192339762827073090593711021 72127411060152408972641633)
  ·
    refine ⟨54095558295114306729481225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72127411060152408972641633 54095558295114306729481225)
    ·
      refine ⟨40571668721335730047110919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54095558295114306729481225 40571668721335730047110919)
      ·
        refine ⟨60857503082003595070666379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571668721335730047110919 60857503082003595070666379)
        ·
          refine ⟨91286254623005392605999569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60857503082003595070666379 91286254623005392605999569)
          ·
            refine ⟨68464690967254044454499677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91286254623005392605999569 68464690967254044454499677)
            ·
              refine ⟨25674259112720266670437379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68464690967254044454499677 25674259112720266670437379)
              ·
                refine ⟨38511388669080400005656069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25674259112720266670437379 38511388669080400005656069)
                ·
                  refine ⟨7220885375452575001060513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38511388669080400005656069 7220885375452575001060513)
                  ·
                    refine ⟨5415664031589431250795385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220885375452575001060513 5415664031589431250795385)
                    ·
                      refine ⟨4061748023692073438096539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415664031589431250795385 4061748023692073438096539)
                      ·
                        rfl

theorem cell23_7910226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_7910226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910226 prefixEnd_7910226 := by exact prefixLift 7910226
  have htrace : WordTrace (prefixWord ++ tailWord_7910226) baseStart_7910226 baseEnd_7910226 := by
    simpa [prefixWord, tailWord_7910226, baseEnd_7910226] using wordTrace_append hprefix tailTrace_7910226
  have hstable : (prefixWord ++ tailWord_7910226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910226).length < 2 ^ (prefixWord ++ tailWord_7910226).sum := by decide
  have hdescent : baseEnd_7910226 < baseStart_7910226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910279 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 2, 5]
def baseStart_7910279 : Nat := 118140960795 + 7910279 * 2 ^ 59
def prefixEnd_7910279 : Nat := 4983230072969 + 3 ^ 40 * 7910279 * 2
def baseEnd_7910279 : Nat := 1353925079388920576911265

theorem tailTrace_7910279 : CollatzResearch.WordTrace tailWord_7910279 prefixEnd_7910279 1353925079388920576911265 := by
  unfold tailWord_7910279
  simp only [CollatzResearch.WordTrace]
  refine ⟨288511577309417625942245891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192341051539611750628163927 288511577309417625942245891)
  ·
    refine ⟨432767365964126438913368837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288511577309417625942245891 432767365964126438913368837)
    ·
      refine ⟨81143881118273707296256657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432767365964126438913368837 81143881118273707296256657)
      ·
        refine ⟨60857910838705280472192493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81143881118273707296256657 60857910838705280472192493)
        ·
          refine ⟨22821716564514480177072185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60857910838705280472192493 22821716564514480177072185)
          ·
            refine ⟨17116287423385860132804139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821716564514480177072185 17116287423385860132804139)
            ·
              refine ⟨25674431135078790199206209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17116287423385860132804139 25674431135078790199206209)
              ·
                refine ⟨19255823351309092649404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25674431135078790199206209 19255823351309092649404657)
                ·
                  refine ⟨14441867513481819487053493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19255823351309092649404657 14441867513481819487053493)
                  ·
                    refine ⟨1353925079388920576911265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14441867513481819487053493 1353925079388920576911265)
                    ·
                      rfl

theorem cell23_7910279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_7910279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910279 prefixEnd_7910279 := by exact prefixLift 7910279
  have htrace : WordTrace (prefixWord ++ tailWord_7910279) baseStart_7910279 baseEnd_7910279 := by
    simpa [prefixWord, tailWord_7910279, baseEnd_7910279] using wordTrace_append hprefix tailTrace_7910279
  have hstable : (prefixWord ++ tailWord_7910279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910279).length < 2 ^ (prefixWord ++ tailWord_7910279).sum := by decide
  have hdescent : baseEnd_7910279 < baseStart_7910279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910294 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7910294 : Nat := 118140960795 + 7910294 * 2 ^ 59
def prefixEnd_7910294 : Nat := 4983230072969 + 3 ^ 40 * 7910294 * 2
def baseEnd_7910294 : Nat := 4061782940376579172046227

theorem tailTrace_7910294 : CollatzResearch.WordTrace tailWord_7910294 prefixEnd_7910294 4061782940376579172046227 := by
  unfold tailWord_7910294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032007775272705219002621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192341416269575522336027957 18032007775272705219002621)
  ·
    refine ⟨6762002915727264457125983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18032007775272705219002621 6762002915727264457125983)
    ·
      refine ⟨10143004373590896685688975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762002915727264457125983 10143004373590896685688975)
      ·
        refine ⟨15214506560386345028533463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143004373590896685688975 15214506560386345028533463)
        ·
          refine ⟨22821759840579517542800195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214506560386345028533463 22821759840579517542800195)
          ·
            refine ⟨34232639760869276314200293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22821759840579517542800195 34232639760869276314200293)
            ·
              refine ⟨6418619955162989308912555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34232639760869276314200293 6418619955162989308912555)
              ·
                refine ⟨9627929932744483963368833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418619955162989308912555 9627929932744483963368833)
                ·
                  refine ⟨7220947449558362972526625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627929932744483963368833 7220947449558362972526625)
                  ·
                    refine ⟨5415710587168772229394969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220947449558362972526625 5415710587168772229394969)
                    ·
                      refine ⟨4061782940376579172046227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415710587168772229394969 4061782940376579172046227)
                      ·
                        rfl

theorem cell23_7910294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7910294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910294 prefixEnd_7910294 := by exact prefixLift 7910294
  have htrace : WordTrace (prefixWord ++ tailWord_7910294) baseStart_7910294 baseEnd_7910294 := by
    simpa [prefixWord, tailWord_7910294, baseEnd_7910294] using wordTrace_append hprefix tailTrace_7910294
  have hstable : (prefixWord ++ tailWord_7910294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910294).length < 2 ^ (prefixWord ++ tailWord_7910294).sum := by decide
  have hdescent : baseEnd_7910294 < baseStart_7910294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910343 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 1, 4]
def baseStart_7910343 : Nat := 118140960795 + 7910343 * 2 ^ 59
def prefixEnd_7910343 : Nat := 4983230072969 + 3 ^ 40 * 7910343 * 2
def baseEnd_7910343 : Nat := 1353936033642883160111167

theorem tailTrace_7910343 : CollatzResearch.WordTrace tailWord_7910343 prefixEnd_7910343 1353936033642883160111167 := by
  unfold tailWord_7910343
  simp only [CollatzResearch.WordTrace]
  refine ⟨288513911581185764872575683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192342607720790509915050455 288513911581185764872575683)
  ·
    refine ⟨432770867371778647308863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288513911581185764872575683 432770867371778647308863525)
    ·
      refine ⟨81144537632208496370411911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432770867371778647308863525 81144537632208496370411911)
      ·
        refine ⟨121716806448312744555617867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81144537632208496370411911 121716806448312744555617867)
        ·
          refine ⟨182575209672469116833426801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121716806448312744555617867 182575209672469116833426801)
          ·
            refine ⟨136931407254351837625070101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182575209672469116833426801 136931407254351837625070101)
            ·
              refine ⟨6418659715047742388675161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136931407254351837625070101 6418659715047742388675161)
              ·
                refine ⟨4813994786285806791506371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418659715047742388675161 4813994786285806791506371)
                ·
                  refine ⟨7220992179428710187259557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813994786285806791506371 7220992179428710187259557)
                  ·
                    refine ⟨1353936033642883160111167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220992179428710187259557 1353936033642883160111167)
                    ·
                      rfl

theorem cell23_7910343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_7910343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910343 prefixEnd_7910343 := by exact prefixLift 7910343
  have htrace : WordTrace (prefixWord ++ tailWord_7910343) baseStart_7910343 baseEnd_7910343 := by
    simpa [prefixWord, tailWord_7910343, baseEnd_7910343] using wordTrace_append hprefix tailTrace_7910343
  have hstable : (prefixWord ++ tailWord_7910343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910343).length < 2 ^ (prefixWord ++ tailWord_7910343).sum := by decide
  have hdescent : baseEnd_7910343 < baseStart_7910343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910369 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_7910369 : Nat := 118140960795 + 7910369 * 2 ^ 59
def prefixEnd_7910369 : Nat := 4983230072969 + 3 ^ 40 * 7910369 * 2
def baseEnd_7910369 : Nat := 1353940483808555459536127

theorem tailTrace_7910369 : CollatzResearch.WordTrace tailWord_7910369 prefixEnd_7910369 1353940483808555459536127 := by
  unfold tailWord_7910369
  simp only [CollatzResearch.WordTrace]
  refine ⟨288514859879091571313022161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192343239919394380875348107 288514859879091571313022161)
  ·
    refine ⟨216386144909318678484766621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288514859879091571313022161 216386144909318678484766621)
    ·
      refine ⟨81144804340994504431787483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216386144909318678484766621 81144804340994504431787483)
      ·
        refine ⟨121717206511491756647681225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81144804340994504431787483 121717206511491756647681225)
        ·
          refine ⟨91287904883618817485760919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121717206511491756647681225 91287904883618817485760919)
          ·
            refine ⟨136931857325428226228641379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91287904883618817485760919 136931857325428226228641379)
            ·
              refine ⟨205397785988142339342962069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136931857325428226228641379 205397785988142339342962069)
              ·
                refine ⟨9628021218194172156701347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205397785988142339342962069 9628021218194172156701347)
                ·
                  refine ⟨14442031827291258235052021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628021218194172156701347 14442031827291258235052021)
                  ·
                    refine ⟨1353940483808555459536127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14442031827291258235052021 1353940483808555459536127)
                    ·
                      rfl

theorem cell23_7910369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_7910369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910369 prefixEnd_7910369 := by exact prefixLift 7910369
  have htrace : WordTrace (prefixWord ++ tailWord_7910369) baseStart_7910369 baseEnd_7910369 := by
    simpa [prefixWord, tailWord_7910369, baseEnd_7910369] using wordTrace_append hprefix tailTrace_7910369
  have hstable : (prefixWord ++ tailWord_7910369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910369).length < 2 ^ (prefixWord ++ tailWord_7910369).sum := by decide
  have hdescent : baseEnd_7910369 < baseStart_7910369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910370 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7910370 : Nat := 118140960795 + 7910370 * 2 ^ 59
def prefixEnd_7910370 : Nat := 4983230072969 + 3 ^ 40 * 7910370 * 2
def baseEnd_7910370 : Nat := 4061821964906320874695877

theorem tailTrace_7910370 : CollatzResearch.WordTrace tailWord_7910370 prefixEnd_7910370 4061821964906320874695877 := by
  unfold tailWord_7910370
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128724088021987120952141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192343264234725298989205709 72128724088021987120952141)
  ·
    refine ⟨27048271533008245170357053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72128724088021987120952141 27048271533008245170357053)
    ·
      refine ⟨10143101824878091938883895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27048271533008245170357053 10143101824878091938883895)
      ·
        refine ⟨15214652737317137908325843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143101824878091938883895 15214652737317137908325843)
        ·
          refine ⟨22821979105975706862488765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214652737317137908325843 22821979105975706862488765)
          ·
            refine ⟨8558242164740890073433287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22821979105975706862488765 8558242164740890073433287)
            ·
              refine ⟨12837363247111335110149931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558242164740890073433287 12837363247111335110149931)
              ·
                refine ⟨19256044870667002665224897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12837363247111335110149931 19256044870667002665224897)
                ·
                  refine ⟨14442033653000251998918673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19256044870667002665224897 14442033653000251998918673)
                  ·
                    refine ⟨10831525239750188999189005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14442033653000251998918673 10831525239750188999189005)
                    ·
                      refine ⟨4061821964906320874695877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831525239750188999189005 4061821964906320874695877)
                      ·
                        rfl

theorem cell23_7910370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7910370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910370 prefixEnd_7910370 := by exact prefixLift 7910370
  have htrace : WordTrace (prefixWord ++ tailWord_7910370) baseStart_7910370 baseEnd_7910370 := by
    simpa [prefixWord, tailWord_7910370, baseEnd_7910370] using wordTrace_append hprefix tailTrace_7910370
  have hstable : (prefixWord ++ tailWord_7910370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910370).length < 2 ^ (prefixWord ++ tailWord_7910370).sum := by decide
  have hdescent : baseEnd_7910370 < baseStart_7910370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910383 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 1, 1, 3]
def baseStart_7910383 : Nat := 118140960795 + 7910383 * 2 ^ 59
def prefixEnd_7910383 : Nat := 4983230072969 + 3 ^ 40 * 7910383 * 2
def baseEnd_7910383 : Nat := 4061828640154829323833317

theorem tailTrace_7910383 : CollatzResearch.WordTrace tailWord_7910383 prefixEnd_7910383 4061828640154829323833317 := by
  unfold tailWord_7910383
  simp only [CollatzResearch.WordTrace]
  refine ⟨288515370501040851704031803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192343580334027234469354535 288515370501040851704031803)
  ·
    refine ⟨432773055751561277556047705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288515370501040851704031803 432773055751561277556047705)
    ·
      refine ⟨324579791813670958167035779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432773055751561277556047705 324579791813670958167035779)
      ·
        refine ⟨486869687720506437250553669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324579791813670958167035779 486869687720506437250553669)
        ·
          refine ⟨91288066447594956984478813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486869687720506437250553669 91288066447594956984478813)
          ·
            refine ⟨34233024917848108869179555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91288066447594956984478813 34233024917848108869179555)
            ·
              refine ⟨51349537376772163303769333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34233024917848108869179555 51349537376772163303769333)
              ·
                refine ⟨4814019129072390309728375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51349537376772163303769333 4814019129072390309728375)
                ·
                  refine ⟨7221028693608585464592563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814019129072390309728375 7221028693608585464592563)
                  ·
                    refine ⟨10831543040412878196888845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7221028693608585464592563 10831543040412878196888845)
                    ·
                      refine ⟨4061828640154829323833317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831543040412878196888845 4061828640154829323833317)
                      ·
                        rfl

theorem cell23_7910383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 1, 1, 3].length) (baseStart_7910383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910383 prefixEnd_7910383 := by exact prefixLift 7910383
  have htrace : WordTrace (prefixWord ++ tailWord_7910383) baseStart_7910383 baseEnd_7910383 := by
    simpa [prefixWord, tailWord_7910383, baseEnd_7910383] using wordTrace_append hprefix tailTrace_7910383
  have hstable : (prefixWord ++ tailWord_7910383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910383).length < 2 ^ (prefixWord ++ tailWord_7910383).sum := by decide
  have hdescent : baseEnd_7910383 < baseStart_7910383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910409 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_7910409 : Nat := 118140960795 + 7910409 * 2 ^ 59
def prefixEnd_7910409 : Nat := 4983230072969 + 3 ^ 40 * 7910409 * 2
def baseEnd_7910409 : Nat := 4061841990651846222108197

theorem tailTrace_7910409 : CollatzResearch.WordTrace tailWord_7910409 prefixEnd_7910409 4061841990651846222108197 := by
  unfold tailWord_7910409
  simp only [CollatzResearch.WordTrace]
  refine ⟨288516318798946658144478281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192344212532631105429652187 288516318798946658144478281)
  ·
    refine ⟨216387239099209993608358711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288516318798946658144478281 216387239099209993608358711)
    ·
      refine ⟨324580858648814990412538067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216387239099209993608358711 324580858648814990412538067)
      ·
        refine ⟨486871287973222485618807101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324580858648814990412538067 486871287973222485618807101)
        ·
          refine ⟨182576732989958432107052663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486871287973222485618807101 182576732989958432107052663)
          ·
            refine ⟨273865099484937648160578995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182576732989958432107052663 273865099484937648160578995)
            ·
              refine ⟨410797649227406472240868493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273865099484937648160578995 410797649227406472240868493)
              ·
                refine ⟨154049118460277427090325685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410797649227406472240868493 154049118460277427090325685)
                ·
                  refine ⟨14442104855651008789718033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154049118460277427090325685 14442104855651008789718033)
                  ·
                    refine ⟨10831578641738256592288525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14442104855651008789718033 10831578641738256592288525)
                    ·
                      refine ⟨4061841990651846222108197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831578641738256592288525 4061841990651846222108197)
                      ·
                        rfl

theorem cell23_7910409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_7910409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910409 prefixEnd_7910409 := by exact prefixLift 7910409
  have htrace : WordTrace (prefixWord ++ tailWord_7910409) baseStart_7910409 baseEnd_7910409 := by
    simpa [prefixWord, tailWord_7910409, baseEnd_7910409] using wordTrace_append hprefix tailTrace_7910409
  have hstable : (prefixWord ++ tailWord_7910409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910409).length < 2 ^ (prefixWord ++ tailWord_7910409).sum := by decide
  have hdescent : baseEnd_7910409 < baseStart_7910409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910423 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7910423 : Nat := 118140960795 + 7910423 * 2 ^ 59
def prefixEnd_7910423 : Nat := 4983230072969 + 3 ^ 40 * 7910423 * 2
def baseEnd_7910423 : Nat := 4061849179381009167333133

theorem tailTrace_7910423 : CollatzResearch.WordTrace tailWord_7910423 prefixEnd_7910423 4061849179381009167333133 := by
  unfold tailWord_7910423
  simp only [CollatzResearch.WordTrace]
  refine ⟨288516829420895938535487923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192344552947263959023658615 288516829420895938535487923)
  ·
    refine ⟨432775244131343907803231885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288516829420895938535487923 432775244131343907803231885)
    ·
      refine ⟨162290716549253965426211957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432775244131343907803231885 162290716549253965426211957)
      ·
        refine ⟨15214754676492559258707371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162290716549253965426211957 15214754676492559258707371)
        ·
          refine ⟨22822132014738838888061057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214754676492559258707371 22822132014738838888061057)
          ·
            refine ⟨17116599011054129166045793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22822132014738838888061057 17116599011054129166045793)
            ·
              refine ⟨12837449258290596874534345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17116599011054129166045793 12837449258290596874534345)
              ·
                refine ⟨9628086943717947655900759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12837449258290596874534345 9628086943717947655900759)
                ·
                  refine ⟨14442130415576921483851139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628086943717947655900759 14442130415576921483851139)
                  ·
                    refine ⟨21663195623365382225776709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14442130415576921483851139 21663195623365382225776709)
                    ·
                      refine ⟨4061849179381009167333133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21663195623365382225776709 4061849179381009167333133)
                      ·
                        rfl

theorem cell23_7910423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7910423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910423 prefixEnd_7910423 := by exact prefixLift 7910423
  have htrace : WordTrace (prefixWord ++ tailWord_7910423) baseStart_7910423 baseEnd_7910423 := by
    simpa [prefixWord, tailWord_7910423, baseEnd_7910423] using wordTrace_append hprefix tailTrace_7910423
  have hstable : (prefixWord ++ tailWord_7910423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910423).length < 2 ^ (prefixWord ++ tailWord_7910423).sum := by decide
  have hdescent : baseEnd_7910423 < baseStart_7910423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910494 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7910494 : Nat := 118140960795 + 7910494 * 2 ^ 59
def prefixEnd_7910494 : Nat := 4983230072969 + 3 ^ 40 * 7910494 * 2
def baseEnd_7910494 : Nat := 4061885636507478389545307

theorem tailTrace_7910494 : CollatzResearch.WordTrace tailWord_7910494 prefixEnd_7910494 4061885636507478389545307 := by
  unfold tailWord_7910494
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064927375454839707665317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192346279335759145107548357 36064927375454839707665317)
  ·
    refine ⟨6762173882897782445187247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36064927375454839707665317 6762173882897782445187247)
    ·
      refine ⟨10143260824346673667780871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762173882897782445187247 10143260824346673667780871)
      ·
        refine ⟨15214891236520010501671307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143260824346673667780871 15214891236520010501671307)
        ·
          refine ⟨22822336854780015752506961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214891236520010501671307 22822336854780015752506961)
          ·
            refine ⟨17116752641085011814380221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22822336854780015752506961 17116752641085011814380221)
            ·
              refine ⟨6418782240406879430392583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17116752641085011814380221 6418782240406879430392583)
              ·
                refine ⟨9628173360610319145588875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418782240406879430392583 9628173360610319145588875)
                ·
                  refine ⟨14442260040915478718383313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628173360610319145588875 14442260040915478718383313)
                  ·
                    refine ⟨10831695030686609038787485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14442260040915478718383313 10831695030686609038787485)
                    ·
                      refine ⟨4061885636507478389545307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10831695030686609038787485 4061885636507478389545307)
                      ·
                        rfl

theorem cell23_7910494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7910494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910494 prefixEnd_7910494 := by exact prefixLift 7910494
  have htrace : WordTrace (prefixWord ++ tailWord_7910494) baseStart_7910494 baseEnd_7910494 := by
    simpa [prefixWord, tailWord_7910494, baseEnd_7910494] using wordTrace_append hprefix tailTrace_7910494
  have hstable : (prefixWord ++ tailWord_7910494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910494).length < 2 ^ (prefixWord ++ tailWord_7910494).sum := by decide
  have hdescent : baseEnd_7910494 < baseStart_7910494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910519 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 7]
def baseStart_7910519 : Nat := 118140960795 + 7910519 * 2 ^ 59
def prefixEnd_7910519 : Nat := 4983230072969 + 3 ^ 40 * 7910519 * 2
def baseEnd_7910519 : Nat := 451322052613760087970299

theorem tailTrace_7910519 : CollatzResearch.WordTrace tailWord_7910519 prefixEnd_7910519 451322052613760087970299 := by
  unfold tailWord_7910519
  simp only [CollatzResearch.WordTrace]
  refine ⟨288520330828548146930982611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192346887219032097953988407 288520330828548146930982611)
  ·
    refine ⟨432780496242822220396473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288520330828548146930982611 432780496242822220396473917)
    ·
      refine ⟨162292686091058332648677719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432780496242822220396473917 162292686091058332648677719)
      ·
        refine ⟨243439029136587498973016579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162292686091058332648677719 243439029136587498973016579)
        ·
          refine ⟨365158543704881248459524869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243439029136587498973016579 365158543704881248459524869)
          ·
            refine ⟨68467226944665234086160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365158543704881248459524869 68467226944665234086160913)
            ·
              refine ⟨51350420208498925564620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68467226944665234086160913 51350420208498925564620685)
              ·
                refine ⟨19256407578187097086732757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51350420208498925564620685 19256407578187097086732757)
                ·
                  refine ⟨451322052613760087970299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19256407578187097086732757 451322052613760087970299)
                  ·
                    rfl

theorem cell23_7910519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 7].length) (baseStart_7910519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910519 prefixEnd_7910519 := by exact prefixLift 7910519
  have htrace : WordTrace (prefixWord ++ tailWord_7910519) baseStart_7910519 baseEnd_7910519 := by
    simpa [prefixWord, tailWord_7910519, baseEnd_7910519] using wordTrace_append hprefix tailTrace_7910519
  have hstable : (prefixWord ++ tailWord_7910519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910519).length < 2 ^ (prefixWord ++ tailWord_7910519).sum := by decide
  have hdescent : baseEnd_7910519 < baseStart_7910519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910569 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_7910569 : Nat := 118140960795 + 7910569 * 2 ^ 59
def prefixEnd_7910569 : Nat := 4983230072969 + 3 ^ 40 * 7910569 * 2
def baseEnd_7910569 : Nat := 4061924147556565596107461

theorem tailTrace_7910569 : CollatzResearch.WordTrace tailWord_7910569 prefixEnd_7910569 4061924147556565596107461 := by
  unfold tailWord_7910569
  simp only [CollatzResearch.WordTrace]
  refine ⟨288522154478367005470302761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192348102985578003646868507 288522154478367005470302761)
  ·
    refine ⟨216391615858775254102727071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288522154478367005470302761 216391615858775254102727071)
    ·
      refine ⟨324587423788162881154090607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216391615858775254102727071 324587423788162881154090607)
      ·
        refine ⟨486881135682244321731135911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324587423788162881154090607 486881135682244321731135911)
        ·
          refine ⟨730321703523366482596703867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486881135682244321731135911 730321703523366482596703867)
          ·
            refine ⟨1095482555285049723895055801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730321703523366482596703867 1095482555285049723895055801)
            ·
              refine ⟨821611916463787292921291851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095482555285049723895055801 821611916463787292921291851)
              ·
                refine ⟨1232417874695680939381937777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821611916463787292921291851 1232417874695680939381937777)
                ·
                  refine ⟨924313406021760704536453333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232417874695680939381937777 924313406021760704536453333)
                  ·
                    refine ⟨21663595453635016512573125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 924313406021760704536453333 21663595453635016512573125)
                    ·
                      refine ⟨4061924147556565596107461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21663595453635016512573125 4061924147556565596107461)
                      ·
                        rfl

theorem cell23_7910569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_7910569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910569 prefixEnd_7910569 := by exact prefixLift 7910569
  have htrace : WordTrace (prefixWord ++ tailWord_7910569) baseStart_7910569 baseEnd_7910569 := by
    simpa [prefixWord, tailWord_7910569, baseEnd_7910569] using wordTrace_append hprefix tailTrace_7910569
  have hstable : (prefixWord ++ tailWord_7910569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910569).length < 2 ^ (prefixWord ++ tailWord_7910569).sum := by decide
  have hdescent : baseEnd_7910569 < baseStart_7910569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910570 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_7910570 : Nat := 118140960795 + 7910570 * 2 ^ 59
def prefixEnd_7910570 : Nat := 4983230072969 + 3 ^ 40 * 7910570 * 2
def baseEnd_7910570 : Nat := 451324962337468899132773

theorem tailTrace_7910570 : CollatzResearch.WordTrace tailWord_7910570 prefixEnd_7910570 451324962337468899132773 := by
  unfold tailWord_7910570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72130547737840845660272291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192348127300908921760726109 72130547737840845660272291)
  ·
    refine ⟨108195821606761268490408437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72130547737840845660272291 108195821606761268490408437)
    ·
      refine ⟨10143358275633868920975791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108195821606761268490408437 10143358275633868920975791)
      ·
        refine ⟨15215037413450803381463687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143358275633868920975791 15215037413450803381463687)
        ·
          refine ⟨22822556120176205072195531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215037413450803381463687 22822556120176205072195531)
          ·
            refine ⟨34233834180264307608293297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822556120176205072195531 34233834180264307608293297)
            ·
              refine ⟨25675375635198230706219973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34233834180264307608293297 25675375635198230706219973)
              ·
                refine ⟨4814132931599668257416245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25675375635198230706219973 4814132931599668257416245)
                ·
                  refine ⟨451324962337468899132773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4814132931599668257416245 451324962337468899132773)
                  ·
                    rfl

theorem cell23_7910570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_7910570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910570 prefixEnd_7910570 := by exact prefixLift 7910570
  have htrace : WordTrace (prefixWord ++ tailWord_7910570) baseStart_7910570 baseEnd_7910570 := by
    simpa [prefixWord, tailWord_7910570, baseEnd_7910570] using wordTrace_append hprefix tailTrace_7910570
  have hstable : (prefixWord ++ tailWord_7910570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910570).length < 2 ^ (prefixWord ++ tailWord_7910570).sum := by decide
  have hdescent : baseEnd_7910570 < baseStart_7910570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910643 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 6]
def baseStart_7910643 : Nat := 118140960795 + 7910643 * 2 ^ 59
def prefixEnd_7910643 : Nat := 4983230072969 + 3 ^ 40 * 7910643 * 2
def baseEnd_7910643 : Nat := 451329127236110922953569

theorem tailTrace_7910643 : CollatzResearch.WordTrace tailWord_7910643 prefixEnd_7910643 451329127236110922953569 := by
  unfold tailWord_7910643
  simp only [CollatzResearch.WordTrace]
  refine ⟨288524853480098916108496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192349902320065944072331055 288524853480098916108496583)
  ·
    refine ⟨432787280220148374162744875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288524853480098916108496583 432787280220148374162744875)
    ·
      refine ⟨649180920330222561244117313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432787280220148374162744875 649180920330222561244117313)
      ·
        refine ⟨486885690247666920933087985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649180920330222561244117313 486885690247666920933087985)
        ·
          refine ⟨365164267685750190699815989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486885690247666920933087985 365164267685750190699815989)
          ·
            refine ⟨34234150095539080378107749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 365164267685750190699815989 34234150095539080378107749)
            ·
              refine ⟨6418903142913577570895203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34234150095539080378107749 6418903142913577570895203)
              ·
                refine ⟨9628354714370366356342805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418903142913577570895203 9628354714370366356342805)
                ·
                  refine ⟨451329127236110922953569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9628354714370366356342805 451329127236110922953569)
                  ·
                    rfl

theorem cell23_7910643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 6].length) (baseStart_7910643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910643 prefixEnd_7910643 := by exact prefixLift 7910643
  have htrace : WordTrace (prefixWord ++ tailWord_7910643) baseStart_7910643 baseEnd_7910643 := by
    simpa [prefixWord, tailWord_7910643, baseEnd_7910643] using wordTrace_append hprefix tailTrace_7910643
  have hstable : (prefixWord ++ tailWord_7910643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910643).length < 2 ^ (prefixWord ++ tailWord_7910643).sum := by decide
  have hdescent : baseEnd_7910643 < baseStart_7910643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910680 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_7910680 : Nat := 118140960795 + 7910680 * 2 ^ 59
def prefixEnd_7910680 : Nat := 4983230072969 + 3 ^ 40 * 7910680 * 2
def baseEnd_7910680 : Nat := 4061981143909214661819451

theorem tailTrace_7910680 : CollatzResearch.WordTrace tailWord_7910680 prefixEnd_7910680 4061981143909214661819451 := by
  unfold tailWord_7910680
  simp only [CollatzResearch.WordTrace]
  refine ⟨144263101490482435713796747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192350801987309914285062329 144263101490482435713796747)
  ·
    refine ⟨216394652235723653570695121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144263101490482435713796747 216394652235723653570695121)
    ·
      refine ⟨162295989176792740178021341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216394652235723653570695121 162295989176792740178021341)
      ·
        refine ⟨60860995941297277566758003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162295989176792740178021341 60860995941297277566758003)
        ·
          refine ⟨91291493911945916350137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60860995941297277566758003 91291493911945916350137005)
          ·
            refine ⟨34234310216979718631301377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91291493911945916350137005 34234310216979718631301377)
            ·
              refine ⟨25675732662734788973476033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34234310216979718631301377 25675732662734788973476033)
              ·
                refine ⟨19256799497051091730107025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25675732662734788973476033 19256799497051091730107025)
                ·
                  refine ⟨14442599622788318797580269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19256799497051091730107025 14442599622788318797580269)
                  ·
                    refine ⟨5415974858545619549092601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14442599622788318797580269 5415974858545619549092601)
                    ·
                      refine ⟨4061981143909214661819451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5415974858545619549092601 4061981143909214661819451)
                      ·
                        rfl

theorem cell23_7910680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_7910680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910680 prefixEnd_7910680 := by exact prefixLift 7910680
  have htrace : WordTrace (prefixWord ++ tailWord_7910680) baseStart_7910680 baseEnd_7910680 := by
    simpa [prefixWord, tailWord_7910680, baseEnd_7910680] using wordTrace_append hprefix tailTrace_7910680
  have hstable : (prefixWord ++ tailWord_7910680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910680).length < 2 ^ (prefixWord ++ tailWord_7910680).sum := by decide
  have hdescent : baseEnd_7910680 < baseStart_7910680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910693 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_7910693 : Nat := 118140960795 + 7910693 * 2 ^ 59
def prefixEnd_7910693 : Nat := 4983230072969 + 3 ^ 40 * 7910693 * 2
def baseEnd_7910693 : Nat := 4061987819157723110956891

theorem tailTrace_7910693 : CollatzResearch.WordTrace tailWord_7910693 prefixEnd_7910693 4061987819157723110956891 := by
  unfold tailWord_7910693
  simp only [CollatzResearch.WordTrace]
  refine ⟨288526677129917774647816733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192351118086611849765211155 288526677129917774647816733)
  ·
    refine ⟨108197503923719165492931275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288526677129917774647816733 108197503923719165492931275)
    ·
      refine ⟨162296255885578748239396913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108197503923719165492931275 162296255885578748239396913)
      ·
        refine ⟨121722191914184061179547685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162296255885578748239396913 121722191914184061179547685)
        ·
          refine ⟨22822910983909511471165191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121722191914184061179547685 22822910983909511471165191)
          ·
            refine ⟨34234366475864267206747787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822910983909511471165191 34234366475864267206747787)
            ·
              refine ⟨51351549713796400810121681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34234366475864267206747787 51351549713796400810121681)
              ·
                refine ⟨38513662285347300607591261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51351549713796400810121681 38513662285347300607591261)
                ·
                  refine ⟨14442623357005237727846723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38513662285347300607591261 14442623357005237727846723)
                  ·
                    refine ⟨21663935035507856591770085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14442623357005237727846723 21663935035507856591770085)
                    ·
                      refine ⟨4061987819157723110956891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21663935035507856591770085 4061987819157723110956891)
                      ·
                        rfl

theorem cell23_7910693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_7910693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910693 prefixEnd_7910693 := by exact prefixLift 7910693
  have htrace : WordTrace (prefixWord ++ tailWord_7910693) baseStart_7910693 baseEnd_7910693 := by
    simpa [prefixWord, tailWord_7910693, baseEnd_7910693] using wordTrace_append hprefix tailTrace_7910693
  have hstable : (prefixWord ++ tailWord_7910693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910693).length < 2 ^ (prefixWord ++ tailWord_7910693).sum := by decide
  have hdescent : baseEnd_7910693 < baseStart_7910693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910724 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7910724 : Nat := 118140960795 + 7910724 * 2 ^ 59
def prefixEnd_7910724 : Nat := 4983230072969 + 3 ^ 40 * 7910724 * 2
def baseEnd_7910724 : Nat := 1354001245686004163223083

theorem tailTrace_7910724 : CollatzResearch.WordTrace tailWord_7910724 prefixEnd_7910724 1354001245686004163223083 := by
  unfold tailWord_7910724
  simp only [CollatzResearch.WordTrace]
  refine ⟨144263903896402733471097613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192351871861870311294796817 144263903896402733471097613)
  ·
    refine ⟨54098963961151025051661605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144263903896402733471097613 54098963961151025051661605)
    ·
      refine ⟨10143555742715817197186551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54098963961151025051661605 10143555742715817197186551)
      ·
        refine ⟨15215333614073725795779827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143555742715817197186551 15215333614073725795779827)
        ·
          refine ⟨22823000421110588693669741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215333614073725795779827 22823000421110588693669741)
          ·
            refine ⟨8558625157916470760126153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22823000421110588693669741 8558625157916470760126153)
            ·
              refine ⟨6418968868437353070094615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558625157916470760126153 6418968868437353070094615)
              ·
                refine ⟨9628453302656029605141923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418968868437353070094615 9628453302656029605141923)
                ·
                  refine ⟨14442679953984044407712885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628453302656029605141923 14442679953984044407712885)
                  ·
                    refine ⟨1354001245686004163223083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14442679953984044407712885 1354001245686004163223083)
                    ·
                      rfl

theorem cell23_7910724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7910724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910724 prefixEnd_7910724 := by exact prefixLift 7910724
  have htrace : WordTrace (prefixWord ++ tailWord_7910724) baseStart_7910724 baseEnd_7910724 := by
    simpa [prefixWord, tailWord_7910724, baseEnd_7910724] using wordTrace_append hprefix tailTrace_7910724
  have hstable : (prefixWord ++ tailWord_7910724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910724).length < 2 ^ (prefixWord ++ tailWord_7910724).sum := by decide
  have hdescent : baseEnd_7910724 < baseStart_7910724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910727 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_7910727 : Nat := 118140960795 + 7910727 * 2 ^ 59
def prefixEnd_7910727 : Nat := 4983230072969 + 3 ^ 40 * 7910727 * 2
def baseEnd_7910727 : Nat := 4062005277499975977931735

theorem tailTrace_7910727 : CollatzResearch.WordTrace tailWord_7910727 prefixEnd_7910727 4062005277499975977931735 := by
  unfold tailWord_7910727
  simp only [CollatzResearch.WordTrace]
  refine ⟨288527917211794598454554435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192351944807863065636369623 288527917211794598454554435)
  ·
    refine ⟨432791875817691897681831653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288527917211794598454554435 432791875817691897681831653)
    ·
      refine ⟨81148476715817230815343435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432791875817691897681831653 81148476715817230815343435)
      ·
        refine ⟨121722715073725846223015153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81148476715817230815343435 121722715073725846223015153)
        ·
          refine ⟨91292036305294384667261365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121722715073725846223015153 91292036305294384667261365)
          ·
            refine ⟨8558628403621348562555753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91292036305294384667261365 8558628403621348562555753)
            ·
              refine ⟨6418971302716011421916815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558628403621348562555753 6418971302716011421916815)
              ·
                refine ⟨9628456954074017132875223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418971302716011421916815 9628456954074017132875223)
                ·
                  refine ⟨14442685431111025699312835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628456954074017132875223 14442685431111025699312835)
                  ·
                    refine ⟨21664028146666538548969253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14442685431111025699312835 21664028146666538548969253)
                    ·
                      refine ⟨4062005277499975977931735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21664028146666538548969253 4062005277499975977931735)
                      ·
                        rfl

theorem cell23_7910727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_7910727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910727 prefixEnd_7910727 := by exact prefixLift 7910727
  have htrace : WordTrace (prefixWord ++ tailWord_7910727) baseStart_7910727 baseEnd_7910727 := by
    simpa [prefixWord, tailWord_7910727, baseEnd_7910727] using wordTrace_append hprefix tailTrace_7910727
  have hstable : (prefixWord ++ tailWord_7910727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910727).length < 2 ^ (prefixWord ++ tailWord_7910727).sum := by decide
  have hdescent : baseEnd_7910727 < baseStart_7910727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910746 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_7910746 : Nat := 118140960795 + 7910746 * 2 ^ 59
def prefixEnd_7910746 : Nat := 4983230072969 + 3 ^ 40 * 7910746 * 2
def baseEnd_7910746 : Nat := 1354005011210803801198049

theorem tailTrace_7910746 : CollatzResearch.WordTrace tailWord_7910746 prefixEnd_7910746 1354005011210803801198049 := by
  unfold tailWord_7910746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72132152549681441174874023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192352406799150509799664061 72132152549681441174874023)
  ·
    refine ⟨108198228824522161762311035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72132152549681441174874023 108198228824522161762311035)
    ·
      refine ⟨162297343236783242643466553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108198228824522161762311035 162297343236783242643466553)
      ·
        refine ⟨121723007427587431982599915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162297343236783242643466553 121723007427587431982599915)
        ·
          refine ⟨182584511141381147973899873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121723007427587431982599915 182584511141381147973899873)
          ·
            refine ⟨136938383356035860980424905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182584511141381147973899873 136938383356035860980424905)
            ·
              refine ⟨102703787517026895735318679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136938383356035860980424905 102703787517026895735318679)
              ·
                refine ⟨154055681275540343602978019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102703787517026895735318679 154055681275540343602978019)
                ·
                  refine ⟨231083521913310515404467029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154055681275540343602978019 231083521913310515404467029)
                  ·
                    refine ⟨1354005011210803801198049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231083521913310515404467029 1354005011210803801198049)
                    ·
                      rfl

theorem cell23_7910746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_7910746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910746 prefixEnd_7910746 := by exact prefixLift 7910746
  have htrace : WordTrace (prefixWord ++ tailWord_7910746) baseStart_7910746 baseEnd_7910746 := by
    simpa [prefixWord, tailWord_7910746, baseEnd_7910746] using wordTrace_append hprefix tailTrace_7910746
  have hstable : (prefixWord ++ tailWord_7910746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910746).length < 2 ^ (prefixWord ++ tailWord_7910746).sum := by decide
  have hdescent : baseEnd_7910746 < baseStart_7910746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910787 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 1, 3, 2]
def baseStart_7910787 : Nat := 118140960795 + 7910787 * 2 ^ 59
def prefixEnd_7910787 : Nat := 4983230072969 + 3 ^ 40 * 7910787 * 2
def baseEnd_7910787 : Nat := 4062036086339245743181459

theorem tailTrace_7910787 : CollatzResearch.WordTrace tailWord_7910787 prefixEnd_7910787 4062036086339245743181459 := by
  unfold tailWord_7910787
  simp only [CollatzResearch.WordTrace]
  refine ⟨288530105591577228701738615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192353403727718152467825743 288530105591577228701738615)
  ·
    refine ⟨432795158387365843052607923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288530105591577228701738615 432795158387365843052607923)
    ·
      refine ⟨649192737581048764578911885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432795158387365843052607923 649192737581048764578911885)
      ·
        refine ⟨243447276592893286717091957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649192737581048764578911885 243447276592893286717091957)
        ·
          refine ⟨22823182180583745629727371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243447276592893286717091957 22823182180583745629727371)
          ·
            refine ⟨34234773270875618444591057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22823182180583745629727371 34234773270875618444591057)
            ·
              refine ⟨25676079953156713833443293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34234773270875618444591057 25676079953156713833443293)
              ·
                refine ⟨9628529982433767687541235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25676079953156713833443293 9628529982433767687541235)
                ·
                  refine ⟨14442794973650651531311853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628529982433767687541235 14442794973650651531311853)
                  ·
                    refine ⟨5416048115118994324241945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14442794973650651531311853 5416048115118994324241945)
                    ·
                      refine ⟨4062036086339245743181459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416048115118994324241945 4062036086339245743181459)
                      ·
                        rfl

theorem cell23_7910787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_7910787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910787 prefixEnd_7910787 := by exact prefixLift 7910787
  have htrace : WordTrace (prefixWord ++ tailWord_7910787) baseStart_7910787 baseEnd_7910787 := by
    simpa [prefixWord, tailWord_7910787, baseEnd_7910787] using wordTrace_append hprefix tailTrace_7910787
  have hstable : (prefixWord ++ tailWord_7910787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910787).length < 2 ^ (prefixWord ++ tailWord_7910787).sum := by decide
  have hdescent : baseEnd_7910787 < baseStart_7910787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910823 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 9]
def baseStart_7910823 : Nat := 118140960795 + 7910823 * 2 ^ 59
def prefixEnd_7910823 : Nat := 4983230072969 + 3 ^ 40 * 7910823 * 2
def baseEnd_7910823 : Nat := 451339396849200844703477

theorem tailTrace_7910823 : CollatzResearch.WordTrace tailWord_7910823 prefixEnd_7910823 451339396849200844703477 := by
  unfold tailWord_7910823
  simp only [CollatzResearch.WordTrace]
  refine ⟨288531418619446806850049123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192354279079631204566699415 288531418619446806850049123)
  ·
    refine ⟨432797127929170210275073685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288531418619446806850049123 432797127929170210275073685)
    ·
      refine ⟨20287365371679853606644079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432797127929170210275073685 20287365371679853606644079)
      ·
        refine ⟨30431048057519780409966119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20287365371679853606644079 30431048057519780409966119)
        ·
          refine ⟨45646572086279670614949179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30431048057519780409966119 45646572086279670614949179)
          ·
            refine ⟨68469858129419505922423769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45646572086279670614949179 68469858129419505922423769)
            ·
              refine ⟨51352393597064629441817827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68469858129419505922423769 51352393597064629441817827)
              ·
                refine ⟨77028590395596944162726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51352393597064629441817827 77028590395596944162726741)
                ·
                  refine ⟨451339396849200844703477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77028590395596944162726741 451339396849200844703477)
                  ·
                    rfl

theorem cell23_7910823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 9].length) (baseStart_7910823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910823 prefixEnd_7910823 := by exact prefixLift 7910823
  have htrace : WordTrace (prefixWord ++ tailWord_7910823) baseStart_7910823 baseEnd_7910823 := by
    simpa [prefixWord, tailWord_7910823, baseEnd_7910823] using wordTrace_append hprefix tailTrace_7910823
  have hstable : (prefixWord ++ tailWord_7910823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910823).length < 2 ^ (prefixWord ++ tailWord_7910823).sum := by decide
  have hdescent : baseEnd_7910823 < baseStart_7910823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910863 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_7910863 : Nat := 118140960795 + 7910863 * 2 ^ 59
def prefixEnd_7910863 : Nat := 4983230072969 + 3 ^ 40 * 7910863 * 2
def baseEnd_7910863 : Nat := 4062075110868987445831109

theorem tailTrace_7910863 : CollatzResearch.WordTrace tailWord_7910863 prefixEnd_7910863 4062075110868987445831109 := by
  unfold tailWord_7910863
  simp only [CollatzResearch.WordTrace]
  refine ⟨288532877539301893681505243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192355251692867929121003495 288532877539301893681505243)
  ·
    refine ⟨432799316308952840522257865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288532877539301893681505243 432799316308952840522257865)
    ·
      refine ⟨324599487231714630391693399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432799316308952840522257865 324599487231714630391693399)
      ·
        refine ⟨486899230847571945587540099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324599487231714630391693399 486899230847571945587540099)
        ·
          refine ⟨730348846271357918381310149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486899230847571945587540099 730348846271357918381310149)
          ·
            refine ⟨136940408675879609696495653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730348846271357918381310149 136940408675879609696495653)
            ·
              refine ⟨25676326626727426818092935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136940408675879609696495653 25676326626727426818092935)
              ·
                refine ⟨38514489940091140227139403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25676326626727426818092935 38514489940091140227139403)
                ·
                  refine ⟨57771734910136710340709105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38514489940091140227139403 57771734910136710340709105)
                  ·
                    refine ⟨43328801182602532755531829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57771734910136710340709105 43328801182602532755531829)
                    ·
                      refine ⟨4062075110868987445831109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43328801182602532755531829 4062075110868987445831109)
                      ·
                        rfl

theorem cell23_7910863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_7910863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910863 prefixEnd_7910863 := by exact prefixLift 7910863
  have htrace : WordTrace (prefixWord ++ tailWord_7910863) baseStart_7910863 baseEnd_7910863 := by
    simpa [prefixWord, tailWord_7910863, baseEnd_7910863] using wordTrace_append hprefix tailTrace_7910863
  have hstable : (prefixWord ++ tailWord_7910863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910863).length < 2 ^ (prefixWord ++ tailWord_7910863).sum := by decide
  have hdescent : baseEnd_7910863 < baseStart_7910863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910887 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 2, 5]
def baseStart_7910887 : Nat := 118140960795 + 7910887 * 2 ^ 59
def prefixEnd_7910887 : Nat := 4983230072969 + 3 ^ 40 * 7910887 * 2
def baseEnd_7910887 : Nat := 1354029144801565117310333

theorem tailTrace_7910887 : CollatzResearch.WordTrace tailWord_7910887 prefixEnd_7910887 1354029144801565117310333 := by
  unfold tailWord_7910887
  simp only [CollatzResearch.WordTrace]
  refine ⟨288533752891214945780378915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192355835260809963853585943 288533752891214945780378915)
  ·
    refine ⟨432800629336822418670568373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288533752891214945780378915 432800629336822418670568373)
    ·
      refine ⟨40575059000327101750365785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432800629336822418670568373 40575059000327101750365785)
      ·
        refine ⟨30431294250245326312774339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40575059000327101750365785 30431294250245326312774339)
        ·
          refine ⟨45646941375367989469161509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30431294250245326312774339 45646941375367989469161509)
          ·
            refine ⟨8558801507881498025467783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45646941375367989469161509 8558801507881498025467783)
            ·
              refine ⟨12838202261822247038201675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558801507881498025467783 12838202261822247038201675)
              ·
                refine ⟨19257303392733370557302513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12838202261822247038201675 19257303392733370557302513)
                ·
                  refine ⟨14442977544550027917976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19257303392733370557302513 14442977544550027917976885)
                  ·
                    refine ⟨1354029144801565117310333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14442977544550027917976885 1354029144801565117310333)
                    ·
                      rfl

theorem cell23_7910887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_7910887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910887 prefixEnd_7910887 := by exact prefixLift 7910887
  have htrace : WordTrace (prefixWord ++ tailWord_7910887) baseStart_7910887 baseEnd_7910887 := by
    simpa [prefixWord, tailWord_7910887, baseEnd_7910887] using wordTrace_append hprefix tailTrace_7910887
  have hstable : (prefixWord ++ tailWord_7910887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910887).length < 2 ^ (prefixWord ++ tailWord_7910887).sum := by decide
  have hdescent : baseEnd_7910887 < baseStart_7910887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910940 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7910940 : Nat := 118140960795 + 7910940 * 2 ^ 59
def prefixEnd_7910940 : Nat := 4983230072969 + 3 ^ 40 * 7910940 * 2
def baseEnd_7910940 : Nat := 4062114648879383644568255

theorem tailTrace_7910940 : CollatzResearch.WordTrace tailWord_7910940 prefixEnd_7910940 4062114648879383644568255 := by
  unfold tailWord_7910940
  simp only [CollatzResearch.WordTrace]
  refine ⟨144267842980011467916029137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192357123973348623888038849 144267842980011467916029137)
  ·
    refine ⟨108200882235008600937021853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144267842980011467916029137 108200882235008600937021853)
    ·
      refine ⟨40575330838128225351383195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108200882235008600937021853 40575330838128225351383195)
      ·
        refine ⟨60862996257192338027074793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40575330838128225351383195 60862996257192338027074793)
        ·
          refine ⟨45647247192894253520306095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60862996257192338027074793 45647247192894253520306095)
          ·
            refine ⟨68470870789341380280459143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45647247192894253520306095 68470870789341380280459143)
            ·
              refine ⟨102706306184012070420688715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68470870789341380280459143 102706306184012070420688715)
              ·
                refine ⟨154059459276018105631033073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102706306184012070420688715 154059459276018105631033073)
                ·
                  refine ⟨115544594457013579223274805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154059459276018105631033073 115544594457013579223274805)
                  ·
                    refine ⟨10832305730345023052182013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115544594457013579223274805 10832305730345023052182013)
                    ·
                      refine ⟨4062114648879383644568255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832305730345023052182013 4062114648879383644568255)
                      ·
                        rfl

theorem cell23_7910940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7910940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910940 prefixEnd_7910940 := by exact prefixLift 7910940
  have htrace : WordTrace (prefixWord ++ tailWord_7910940) baseStart_7910940 baseEnd_7910940 := by
    simpa [prefixWord, tailWord_7910940, baseEnd_7910940] using wordTrace_append hprefix tailTrace_7910940
  have hstable : (prefixWord ++ tailWord_7910940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910940).length < 2 ^ (prefixWord ++ tailWord_7910940).sum := by decide
  have hdescent : baseEnd_7910940 < baseStart_7910940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910967 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_7910967 : Nat := 118140960795 + 7910967 * 2 ^ 59
def prefixEnd_7910967 : Nat := 4983230072969 + 3 ^ 40 * 7910967 * 2
def baseEnd_7910967 : Nat := 4062128512857055038930631

theorem tailTrace_7910967 : CollatzResearch.WordTrace tailWord_7910967 prefixEnd_7910967 4062128512857055038930631 := by
  unfold tailWord_7910967
  simp only [CollatzResearch.WordTrace]
  refine ⟨288536670730925119443291155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192357780487283412962194103 288536670730925119443291155)
  ·
    refine ⟨432805006096387679164936733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288536670730925119443291155 432805006096387679164936733)
    ·
      refine ⟨162301877286145379686851275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432805006096387679164936733 162301877286145379686851275)
      ·
        refine ⟨243452815929218069530276913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162301877286145379686851275 243452815929218069530276913)
        ·
          refine ⟨182589611946913552147707685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243452815929218069530276913 182589611946913552147707685)
          ·
            refine ⟨34235552240046291027695191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182589611946913552147707685 34235552240046291027695191)
            ·
              refine ⟨51353328360069436541542787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34235552240046291027695191 51353328360069436541542787)
              ·
                refine ⟨77029992540104154812314181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51353328360069436541542787 77029992540104154812314181)
                ·
                  refine ⟨14443123601269529027308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77029992540104154812314181 14443123601269529027308909)
                  ·
                    refine ⟨5416171350476073385240841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14443123601269529027308909 5416171350476073385240841)
                    ·
                      refine ⟨4062128512857055038930631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416171350476073385240841 4062128512857055038930631)
                      ·
                        rfl

theorem cell23_7910967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_7910967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910967 prefixEnd_7910967 := by exact prefixLift 7910967
  have htrace : WordTrace (prefixWord ++ tailWord_7910967) baseStart_7910967 baseEnd_7910967 := by
    simpa [prefixWord, tailWord_7910967, baseEnd_7910967] using wordTrace_append hprefix tailTrace_7910967
  have hstable : (prefixWord ++ tailWord_7910967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910967).length < 2 ^ (prefixWord ++ tailWord_7910967).sum := by decide
  have hdescent : baseEnd_7910967 < baseStart_7910967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910990 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_7910990 : Nat := 118140960795 + 7910990 * 2 ^ 59
def prefixEnd_7910990 : Nat := 4983230072969 + 3 ^ 40 * 7910990 * 2
def baseEnd_7910990 : Nat := 1354046774304036149647675

theorem tailTrace_7910990 : CollatzResearch.WordTrace tailWord_7910990 prefixEnd_7910990 1354046774304036149647675 := by
  unfold tailWord_7910990
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067188701230224296422303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192358339739894529580918949 36067188701230224296422303)
  ·
    refine ⟨54100783051845336444633455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36067188701230224296422303 54100783051845336444633455)
    ·
      refine ⟨81151174577768004666950183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54100783051845336444633455 81151174577768004666950183)
      ·
        refine ⟨121726761866652007000425275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81151174577768004666950183 121726761866652007000425275)
        ·
          refine ⟨182590142799978010500637913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121726761866652007000425275 182590142799978010500637913)
          ·
            refine ⟨136942607099983507875478435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182590142799978010500637913 136942607099983507875478435)
            ·
              refine ⟨205413910649975261813217653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136942607099983507875478435 205413910649975261813217653)
              ·
                refine ⟨19257554123435180794989155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205413910649975261813217653 19257554123435180794989155)
                ·
                  refine ⟨28886331185152771192483733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19257554123435180794989155 28886331185152771192483733)
                  ·
                    refine ⟨1354046774304036149647675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28886331185152771192483733 1354046774304036149647675)
                    ·
                      rfl

theorem cell23_7910990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_7910990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910990 prefixEnd_7910990 := by exact prefixLift 7910990
  have htrace : WordTrace (prefixWord ++ tailWord_7910990) baseStart_7910990 baseEnd_7910990 := by
    simpa [prefixWord, tailWord_7910990, baseEnd_7910990] using wordTrace_append hprefix tailTrace_7910990
  have hstable : (prefixWord ++ tailWord_7910990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910990).length < 2 ^ (prefixWord ++ tailWord_7910990).sum := by decide
  have hdescent : baseEnd_7910990 < baseStart_7910990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7910994 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_7910994 : Nat := 118140960795 + 7910994 * 2 ^ 59
def prefixEnd_7910994 : Nat := 4983230072969 + 3 ^ 40 * 7910994 * 2
def baseEnd_7910994 : Nat := 1354047458944908811097669

theorem tailTrace_7910994 : CollatzResearch.WordTrace tailWord_7910994 prefixEnd_7910994 1354047458944908811097669 := by
  unfold tailWord_7910994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72134413875456825763631009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192358437001218202036349357 72134413875456825763631009)
  ·
    refine ⟨54100810406592619322723257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72134413875456825763631009 54100810406592619322723257)
    ·
      refine ⟨40575607804944464492042443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54100810406592619322723257 40575607804944464492042443)
      ·
        refine ⟨60863411707416696738063665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40575607804944464492042443 60863411707416696738063665)
        ·
          refine ⟨45647558780562522553547749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60863411707416696738063665 45647558780562522553547749)
          ·
            refine ⟨8558917271355472978790203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45647558780562522553547749 8558917271355472978790203)
            ·
              refine ⟨12838375907033209468185305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558917271355472978790203 12838375907033209468185305)
              ·
                refine ⟨9628781930274907101138979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12838375907033209468185305 9628781930274907101138979)
                ·
                  refine ⟨14443172895412360651708469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628781930274907101138979 14443172895412360651708469)
                  ·
                    refine ⟨1354047458944908811097669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14443172895412360651708469 1354047458944908811097669)
                    ·
                      rfl

theorem cell23_7910994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_7910994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7910994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7910994 prefixEnd_7910994 := by exact prefixLift 7910994
  have htrace : WordTrace (prefixWord ++ tailWord_7910994) baseStart_7910994 baseEnd_7910994 := by
    simpa [prefixWord, tailWord_7910994, baseEnd_7910994] using wordTrace_append hprefix tailTrace_7910994
  have hstable : (prefixWord ++ tailWord_7910994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7910994).length < 2 ^ (prefixWord ++ tailWord_7910994).sum := by decide
  have hdescent : baseEnd_7910994 < baseStart_7910994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7910994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911017 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_7911017 : Nat := 118140960795 + 7911017 * 2 ^ 59
def prefixEnd_7911017 : Nat := 4983230072969 + 3 ^ 40 * 7911017 * 2
def baseEnd_7911017 : Nat := 4062154186889779843305401

theorem tailTrace_7911017 : CollatzResearch.WordTrace tailWord_7911017 prefixEnd_7911017 4062154186889779843305401 := by
  unfold tailWord_7911017
  simp only [CollatzResearch.WordTrace]
  refine ⟨288538494380743977982611305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192358996253829318655074203 288538494380743977982611305)
  ·
    refine ⟨216403870785557983486958479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288538494380743977982611305 216403870785557983486958479)
    ·
      refine ⟨324605806178336975230437719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216403870785557983486958479 324605806178336975230437719)
      ·
        refine ⟨486908709267505462845656579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324605806178336975230437719 486908709267505462845656579)
        ·
          refine ⟨730363063901258194268484869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486908709267505462845656579 730363063901258194268484869)
          ·
            refine ⟨136943074481485911425340913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730363063901258194268484869 136943074481485911425340913)
            ·
              refine ⟨102707305861114433569005685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136943074481485911425340913 102707305861114433569005685)
              ·
                refine ⟨9628809924479478147094283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102707305861114433569005685 9628809924479478147094283)
                ·
                  refine ⟨14443214886719217220641425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628809924479478147094283 14443214886719217220641425)
                  ·
                    refine ⟨10832411165039412915481069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14443214886719217220641425 10832411165039412915481069)
                    ·
                      refine ⟨4062154186889779843305401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832411165039412915481069 4062154186889779843305401)
                      ·
                        rfl

theorem cell23_7911017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_7911017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911017 prefixEnd_7911017 := by exact prefixLift 7911017
  have htrace : WordTrace (prefixWord ++ tailWord_7911017) baseStart_7911017 baseEnd_7911017 := by
    simpa [prefixWord, tailWord_7911017, baseEnd_7911017] using wordTrace_append hprefix tailTrace_7911017
  have hstable : (prefixWord ++ tailWord_7911017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911017).length < 2 ^ (prefixWord ++ tailWord_7911017).sum := by decide
  have hdescent : baseEnd_7911017 < baseStart_7911017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911024 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_7911024 : Nat := 118140960795 + 7911024 * 2 ^ 59
def prefixEnd_7911024 : Nat := 4983230072969 + 3 ^ 40 * 7911024 * 2
def baseEnd_7911024 : Nat := 1354052593751453771972623

theorem tailTrace_7911024 : CollatzResearch.WordTrace tailWord_7911024 prefixEnd_7911024 1354052593751453771972623 := by
  unfold tailWord_7911024
  simp only [CollatzResearch.WordTrace]
  refine ⟨144269374845859309089058063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192359166461145745452077417 144269374845859309089058063)
  ·
    refine ⟨216404062268788963633587095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144269374845859309089058063 216404062268788963633587095)
    ·
      refine ⟨324606093403183445450380643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216404062268788963633587095 324606093403183445450380643)
      ·
        refine ⟨486909140104775168175570965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324606093403183445450380643 486909140104775168175570965)
        ·
          refine ⟨22823865942411336008229889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 486909140104775168175570965 22823865942411336008229889)
          ·
            refine ⟨17117899456808502006172417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22823865942411336008229889 17117899456808502006172417)
            ·
              refine ⟨12838424592606376504629313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17117899456808502006172417 12838424592606376504629313)
              ·
                refine ⟨9628818444454782378471985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12838424592606376504629313 9628818444454782378471985)
                ·
                  refine ⟨7221613833341086783853989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9628818444454782378471985 7221613833341086783853989)
                  ·
                    refine ⟨1354052593751453771972623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221613833341086783853989 1354052593751453771972623)
                    ·
                      rfl

theorem cell23_7911024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_7911024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911024 prefixEnd_7911024 := by exact prefixLift 7911024
  have htrace : WordTrace (prefixWord ++ tailWord_7911024) baseStart_7911024 baseEnd_7911024 := by
    simpa [prefixWord, tailWord_7911024, baseEnd_7911024] using wordTrace_append hprefix tailTrace_7911024
  have hstable : (prefixWord ++ tailWord_7911024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911024).length < 2 ^ (prefixWord ++ tailWord_7911024).sum := by decide
  have hdescent : baseEnd_7911024 < baseStart_7911024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911037 : List Nat := [1, 4, 1, 1, 4, 3, 1, 8]
def baseStart_7911037 : Nat := 118140960795 + 7911037 * 2 ^ 59
def prefixEnd_7911037 : Nat := 4983230072969 + 3 ^ 40 * 7911037 * 2
def baseEnd_7911037 : Nat := 150450535426032213520567

theorem tailTrace_7911037 : CollatzResearch.WordTrace tailWord_7911037 prefixEnd_7911037 150450535426032213520567 := by
  unfold tailWord_7911037
  simp only [CollatzResearch.WordTrace]
  refine ⟨288539223840671521398339365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192359482560447680932226243 288539223840671521398339365)
  ·
    refine ⟨54101104470125910262188631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288539223840671521398339365 54101104470125910262188631)
    ·
      refine ⟨81151656705188865393282947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54101104470125910262188631 81151656705188865393282947)
      ·
        refine ⟨121727485057783298089924421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81151656705188865393282947 121727485057783298089924421)
        ·
          refine ⟨22823903448334368391860829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121727485057783298089924421 22823903448334368391860829)
          ·
            refine ⟨8558963793125388146947811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22823903448334368391860829 8558963793125388146947811)
            ·
              refine ⟨12838445689688082220421717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558963793125388146947811 12838445689688082220421717)
              ·
                refine ⟨150450535426032213520567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12838445689688082220421717 150450535426032213520567)
                ·
                  rfl

theorem cell23_7911037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 8].length) (baseStart_7911037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911037 prefixEnd_7911037 := by exact prefixLift 7911037
  have htrace : WordTrace (prefixWord ++ tailWord_7911037) baseStart_7911037 baseEnd_7911037 := by
    simpa [prefixWord, tailWord_7911037, baseEnd_7911037] using wordTrace_append hprefix tailTrace_7911037
  have hstable : (prefixWord ++ tailWord_7911037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911037).length < 2 ^ (prefixWord ++ tailWord_7911037).sum := by decide
  have hdescent : baseEnd_7911037 < baseStart_7911037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911044 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7911044 : Nat := 118140960795 + 7911044 * 2 ^ 59
def prefixEnd_7911044 : Nat := 4983230072969 + 3 ^ 40 * 7911044 * 2
def baseEnd_7911044 : Nat := 4062168050867451237667777

theorem tailTrace_7911044 : CollatzResearch.WordTrace tailWord_7911044 prefixEnd_7911044 4062168050867451237667777 := by
  unfold tailWord_7911044
  simp only [CollatzResearch.WordTrace]
  refine ⟨144269739575823080796922093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192359652767764107729229457 144269739575823080796922093)
  ·
    refine ⟨54101152340933655298845785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144269739575823080796922093 54101152340933655298845785)
    ·
      refine ⟨40575864255700241474134339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54101152340933655298845785 40575864255700241474134339)
      ·
        refine ⟨60863796383550362211201509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40575864255700241474134339 60863796383550362211201509)
        ·
          refine ⟨11411961821915692914600283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60863796383550362211201509 11411961821915692914600283)
          ·
            refine ⟨17117942732873539371900425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411961821915692914600283 17117942732873539371900425)
            ·
              refine ⟨12838457049655154528925319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17117942732873539371900425 12838457049655154528925319)
              ·
                refine ⟨19257685574482731793387979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12838457049655154528925319 19257685574482731793387979)
                ·
                  refine ⟨28886528361724097690081969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19257685574482731793387979 28886528361724097690081969)
                  ·
                    refine ⟨21664896271293073267561477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28886528361724097690081969 21664896271293073267561477)
                    ·
                      refine ⟨4062168050867451237667777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21664896271293073267561477 4062168050867451237667777)
                      ·
                        rfl

theorem cell23_7911044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7911044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911044 prefixEnd_7911044 := by exact prefixLift 7911044
  have htrace : WordTrace (prefixWord ++ tailWord_7911044) baseStart_7911044 baseEnd_7911044 := by
    simpa [prefixWord, tailWord_7911044, baseEnd_7911044] using wordTrace_append hprefix tailTrace_7911044
  have hstable : (prefixWord ++ tailWord_7911044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911044).length < 2 ^ (prefixWord ++ tailWord_7911044).sum := by decide
  have hdescent : baseEnd_7911044 < baseStart_7911044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911047 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_7911047 : Nat := 118140960795 + 7911047 * 2 ^ 59
def prefixEnd_7911047 : Nat := 4983230072969 + 3 ^ 40 * 7911047 * 2
def baseEnd_7911047 : Nat := 4062169591309414725930263

theorem tailTrace_7911047 : CollatzResearch.WordTrace tailWord_7911047 prefixEnd_7911047 4062169591309414725930263 := by
  unfold tailWord_7911047
  simp only [CollatzResearch.WordTrace]
  refine ⟨288539588570635293106203395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192359725713756862070802263 288539588570635293106203395)
  ·
    refine ⟨432809382855952939659305093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288539588570635293106203395 432809382855952939659305093)
    ·
      refine ⟨81151759285491176186119705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432809382855952939659305093 81151759285491176186119705)
      ·
        refine ⟨60863819464118382139589779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81151759285491176186119705 60863819464118382139589779)
        ·
          refine ⟨91295729196177573209384669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60863819464118382139589779 91295729196177573209384669)
          ·
            refine ⟨34235898448566589953519251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91295729196177573209384669 34235898448566589953519251)
            ·
              refine ⟨51353847672849884930278877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34235898448566589953519251 51353847672849884930278877)
              ·
                refine ⟨19257692877318706848854579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51353847672849884930278877 19257692877318706848854579)
                ·
                  refine ⟨28886539315978060273281869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19257692877318706848854579 28886539315978060273281869)
                  ·
                    refine ⟨10832452243491772602480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28886539315978060273281869 10832452243491772602480701)
                    ·
                      refine ⟨4062169591309414725930263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832452243491772602480701 4062169591309414725930263)
                      ·
                        rfl

theorem cell23_7911047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_7911047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911047 prefixEnd_7911047 := by exact prefixLift 7911047
  have htrace : WordTrace (prefixWord ++ tailWord_7911047) baseStart_7911047 baseEnd_7911047 := by
    simpa [prefixWord, tailWord_7911047, baseEnd_7911047] using wordTrace_append hprefix tailTrace_7911047
  have hstable : (prefixWord ++ tailWord_7911047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911047).length < 2 ^ (prefixWord ++ tailWord_7911047).sum := by decide
  have hdescent : baseEnd_7911047 < baseStart_7911047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911048 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7911048 : Nat := 118140960795 + 7911048 * 2 ^ 59
def prefixEnd_7911048 : Nat := 4983230072969 + 3 ^ 40 * 7911048 * 2
def baseEnd_7911048 : Nat := 4062170104790069222017759

theorem tailTrace_7911048 : CollatzResearch.WordTrace tailWord_7911048 prefixEnd_7911048 4062170104790069222017759 := by
  unfold tailWord_7911048
  simp only [CollatzResearch.WordTrace]
  refine ⟨144269812521815835138494899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192359750029087780184659865 144269812521815835138494899)
  ·
    refine ⟨216404718782723752707742349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144269812521815835138494899 216404718782723752707742349)
    ·
      refine ⟨81151769543521407265403381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216404718782723752707742349 81151769543521407265403381)
      ·
        refine ⟨7607978394705131931131567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81151769543521407265403381 7607978394705131931131567)
        ·
          refine ⟨11411967592057697896697351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607978394705131931131567 11411967592057697896697351)
          ·
            refine ⟨17117951388086546845046027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411967592057697896697351 17117951388086546845046027)
            ·
              refine ⟨25676927082129820267569041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17117951388086546845046027 25676927082129820267569041)
              ·
                refine ⟨19257695311597365200676781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25676927082129820267569041 19257695311597365200676781)
                ·
                  refine ⟨7221635741849011950253793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19257695311597365200676781 7221635741849011950253793)
                  ·
                    refine ⟨5416226806386758962690345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7221635741849011950253793 5416226806386758962690345)
                    ·
                      refine ⟨4062170104790069222017759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416226806386758962690345 4062170104790069222017759)
                      ·
                        rfl

theorem cell23_7911048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7911048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911048 prefixEnd_7911048 := by exact prefixLift 7911048
  have htrace : WordTrace (prefixWord ++ tailWord_7911048) baseStart_7911048 baseEnd_7911048 := by
    simpa [prefixWord, tailWord_7911048, baseEnd_7911048] using wordTrace_append hprefix tailTrace_7911048
  have hstable : (prefixWord ++ tailWord_7911048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911048).length < 2 ^ (prefixWord ++ tailWord_7911048).sum := by decide
  have hdescent : baseEnd_7911048 < baseStart_7911048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911068 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7911068 : Nat := 118140960795 + 7911068 * 2 ^ 59
def prefixEnd_7911068 : Nat := 4983230072969 + 3 ^ 40 * 7911068 * 2
def baseEnd_7911068 : Nat := 4062180374403159143767667

theorem tailTrace_7911068 : CollatzResearch.WordTrace tailWord_7911068 prefixEnd_7911068 4062180374403159143767667 := by
  unfold tailWord_7911068
  simp only [CollatzResearch.WordTrace]
  refine ⟨144270177251779606846358929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192360236335706142461811905 144270177251779606846358929)
  ·
    refine ⟨108202632938834705134769197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144270177251779606846358929 108202632938834705134769197)
    ·
      refine ⟨40575987352063014425538449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108202632938834705134769197 40575987352063014425538449)
      ·
        refine ⟨30431990514047260819153837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40575987352063014425538449 30431990514047260819153837)
        ·
          refine ⟨11411996442767722807182689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30431990514047260819153837 11411996442767722807182689)
          ·
            refine ⟨8558997332075792105387017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11411996442767722807182689 8558997332075792105387017)
            ·
              refine ⟨6419247999056844079040263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558997332075792105387017 6419247999056844079040263)
              ·
                refine ⟨9628871998585266118560395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419247999056844079040263 9628871998585266118560395)
                ·
                  refine ⟨14443307997877899177840593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628871998585266118560395 14443307997877899177840593)
                  ·
                    refine ⟨10832480998408424383380445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14443307997877899177840593 10832480998408424383380445)
                    ·
                      refine ⟨4062180374403159143767667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832480998408424383380445 4062180374403159143767667)
                      ·
                        rfl

theorem cell23_7911068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7911068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911068 prefixEnd_7911068 := by exact prefixLift 7911068
  have htrace : WordTrace (prefixWord ++ tailWord_7911068) baseStart_7911068 baseEnd_7911068 := by
    simpa [prefixWord, tailWord_7911068, baseEnd_7911068] using wordTrace_append hprefix tailTrace_7911068
  have hstable : (prefixWord ++ tailWord_7911068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911068).length < 2 ^ (prefixWord ++ tailWord_7911068).sum := by decide
  have hdescent : baseEnd_7911068 < baseStart_7911068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911124 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7911124 : Nat := 118140960795 + 7911124 * 2 ^ 59
def prefixEnd_7911124 : Nat := 4983230072969 + 3 ^ 40 * 7911124 * 2
def baseEnd_7911124 : Nat := 4062209129319810924667409

theorem tailTrace_7911124 : CollatzResearch.WordTrace tailWord_7911124 prefixEnd_7911124 4062209129319810924667409 := by
  unfold tailWord_7911124
  simp only [CollatzResearch.WordTrace]
  refine ⟨144271198495678167628378213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192361597994237556837837617 144271198495678167628378213)
  ·
    refine ⟨27050849717939656430320915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144271198495678167628378213 27050849717939656430320915)
    ·
      refine ⟨40576274576909484645481373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27050849717939656430320915 40576274576909484645481373)
      ·
        refine ⟨15216102966341056742055515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40576274576909484645481373 15216102966341056742055515)
        ·
          refine ⟨22824154449511585113083273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15216102966341056742055515 22824154449511585113083273)
          ·
            refine ⟨17118115837133688834812455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22824154449511585113083273 17118115837133688834812455)
            ·
              refine ⟨25677173755700533252218683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17118115837133688834812455 25677173755700533252218683)
              ·
                refine ⟨38515760633550799878328025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25677173755700533252218683 38515760633550799878328025)
                ·
                  refine ⟨28886820475163099908746019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38515760633550799878328025 28886820475163099908746019)
                  ·
                    refine ⟨43330230712744649863119029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28886820475163099908746019 43330230712744649863119029)
                    ·
                      refine ⟨4062209129319810924667409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43330230712744649863119029 4062209129319810924667409)
                      ·
                        rfl

theorem cell23_7911124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7911124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911124 prefixEnd_7911124 := by exact prefixLift 7911124
  have htrace : WordTrace (prefixWord ++ tailWord_7911124) baseStart_7911124 baseEnd_7911124 := by
    simpa [prefixWord, tailWord_7911124, baseEnd_7911124] using wordTrace_append hprefix tailTrace_7911124
  have hstable : (prefixWord ++ tailWord_7911124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911124).length < 2 ^ (prefixWord ++ tailWord_7911124).sum := by decide
  have hdescent : baseEnd_7911124 < baseStart_7911124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911144 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 7]
def baseStart_7911144 : Nat := 118140960795 + 7911144 * 2 ^ 59
def prefixEnd_7911144 : Nat := 4983230072969 + 3 ^ 40 * 7911144 * 2
def baseEnd_7911144 : Nat := 451357710992544538490813

theorem tailTrace_7911144 : CollatzResearch.WordTrace tailWord_7911144 prefixEnd_7911144 451357710992544538490813 := by
  unfold tailWord_7911144
  simp only [CollatzResearch.WordTrace]
  refine ⟨144271563225641939336242243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192362084300855919114989657 144271563225641939336242243)
  ·
    refine ⟨216407344838462909004363365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144271563225641939336242243 216407344838462909004363365)
    ·
      refine ⟨40576377157211795438318131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216407344838462909004363365 40576377157211795438318131)
      ·
        refine ⟨60864565735817693157477197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40576377157211795438318131 60864565735817693157477197)
        ·
          refine ⟨22824212150931634934053949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60864565735817693157477197 22824212150931634934053949)
          ·
            refine ⟨8559079556599363100270231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22824212150931634934053949 8559079556599363100270231)
            ·
              refine ⟨12838619334899044650405347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559079556599363100270231 12838619334899044650405347)
              ·
                refine ⟨19257929002348566975608021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12838619334899044650405347 19257929002348566975608021)
                ·
                  refine ⟨451357710992544538490813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19257929002348566975608021 451357710992544538490813)
                  ·
                    rfl

theorem cell23_7911144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_7911144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911144 prefixEnd_7911144 := by exact prefixLift 7911144
  have htrace : WordTrace (prefixWord ++ tailWord_7911144) baseStart_7911144 baseEnd_7911144 := by
    simpa [prefixWord, tailWord_7911144, baseEnd_7911144] using wordTrace_append hprefix tailTrace_7911144
  have hstable : (prefixWord ++ tailWord_7911144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911144).length < 2 ^ (prefixWord ++ tailWord_7911144).sum := by decide
  have hdescent : baseEnd_7911144 < baseStart_7911144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911187 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 7, 4]
def baseStart_7911187 : Nat := 118140960795 + 7911187 * 2 ^ 59
def prefixEnd_7911187 : Nat := 4983230072969 + 3 ^ 40 * 7911187 * 2
def baseEnd_7911187 : Nat := 1354080492867014726059873

theorem tailTrace_7911187 : CollatzResearch.WordTrace tailWord_7911187 prefixEnd_7911187 1354080492867014726059873 := by
  unfold tailWord_7911187
  simp only [CollatzResearch.WordTrace]
  refine ⟨288544694790128097016299815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192363129860085398010866543 288544694790128097016299815)
  ·
    refine ⟨432817042185192145524449723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288544694790128097016299815 432817042185192145524449723)
    ·
      refine ⟨649225563277788218286674585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432817042185192145524449723 649225563277788218286674585)
      ·
        refine ⟨486919172458341163715005939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649225563277788218286674585 486919172458341163715005939)
        ·
          refine ⟨730378758687511745572508909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486919172458341163715005939 730378758687511745572508909)
          ·
            refine ⟨273892034507816904589690841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730378758687511745572508909 273892034507816904589690841)
            ·
              refine ⟨205419025880862678442268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273892034507816904589690841 205419025880862678442268131)
              ·
                refine ⟨308128538821294017663402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205419025880862678442268131 308128538821294017663402197)
                ·
                  refine ⟨7221762628624078538985989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 308128538821294017663402197 7221762628624078538985989)
                  ·
                    refine ⟨1354080492867014726059873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221762628624078538985989 1354080492867014726059873)
                    ·
                      rfl

theorem cell23_7911187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 4].length) (baseStart_7911187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911187 prefixEnd_7911187 := by exact prefixLift 7911187
  have htrace : WordTrace (prefixWord ++ tailWord_7911187) baseStart_7911187 baseEnd_7911187 := by
    simpa [prefixWord, tailWord_7911187, baseEnd_7911187] using wordTrace_append hprefix tailTrace_7911187
  have hstable : (prefixWord ++ tailWord_7911187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911187).length < 2 ^ (prefixWord ++ tailWord_7911187).sum := by decide
  have hdescent : baseEnd_7911187 < baseStart_7911187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911194 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_7911194 : Nat := 118140960795 + 7911194 * 2 ^ 59
def prefixEnd_7911194 : Nat := 4983230072969 + 3 ^ 40 * 7911194 * 2
def baseEnd_7911194 : Nat := 4062245072965625650792087

theorem tailTrace_7911194 : CollatzResearch.WordTrace tailWord_7911194 prefixEnd_7911194 4062245072965625650792087 := by
  unfold tailWord_7911194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72136237525275684302951159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192363300067401824807869757 72136237525275684302951159)
  ·
    refine ⟨108204356287913526454426739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72136237525275684302951159 108204356287913526454426739)
    ·
      refine ⟨162306534431870289681640109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108204356287913526454426739 162306534431870289681640109)
      ·
        refine ⟨60864950411951358630615041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162306534431870289681640109 60864950411951358630615041)
        ·
          refine ⟨45648712808963518972961281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60864950411951358630615041 45648712808963518972961281)
          ·
            refine ⟨34236534606722639229720961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45648712808963518972961281 34236534606722639229720961)
            ·
              refine ⟨25677400955041979422290721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34236534606722639229720961 25677400955041979422290721)
              ·
                refine ⟨19258050716281484566718041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25677400955041979422290721 19258050716281484566718041)
                ·
                  refine ⟨14443538037211113425038531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19258050716281484566718041 14443538037211113425038531)
                  ·
                    refine ⟨21665307055816670137557797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14443538037211113425038531 21665307055816670137557797)
                    ·
                      refine ⟨4062245072965625650792087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21665307055816670137557797 4062245072965625650792087)
                      ·
                        rfl

theorem cell23_7911194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_7911194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911194 prefixEnd_7911194 := by exact prefixLift 7911194
  have htrace : WordTrace (prefixWord ++ tailWord_7911194) baseStart_7911194 baseEnd_7911194 := by
    simpa [prefixWord, tailWord_7911194, baseEnd_7911194] using wordTrace_append hprefix tailTrace_7911194
  have hstable : (prefixWord ++ tailWord_7911194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911194).length < 2 ^ (prefixWord ++ tailWord_7911194).sum := by decide
  have hdescent : baseEnd_7911194 < baseStart_7911194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911221 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7911221 : Nat := 118140960795 + 7911221 * 2 ^ 59
def prefixEnd_7911221 : Nat := 4983230072969 + 3 ^ 40 * 7911221 * 2
def baseEnd_7911221 : Nat := 1354086312314432348384821

theorem tailTrace_7911221 : CollatzResearch.WordTrace tailWord_7911221 prefixEnd_7911221 1354086312314432348384821 := by
  unfold tailWord_7911221
  simp only [CollatzResearch.WordTrace]
  refine ⟨288545934872004920823037517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192363956581336613882025011 288545934872004920823037517)
  ·
    refine ⟨108204725577001845308639069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288545934872004920823037517 108204725577001845308639069)
    ·
      refine ⟨40576772091375691990739651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108204725577001845308639069 40576772091375691990739651)
      ·
        refine ⟨60865158137063537986109477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40576772091375691990739651 60865158137063537986109477)
        ·
          refine ⟨11412217150699413372395527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60865158137063537986109477 11412217150699413372395527)
          ·
            refine ⟨17118325726049120058593291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412217150699413372395527 17118325726049120058593291)
            ·
              refine ⟨25677488589073680087889937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17118325726049120058593291 25677488589073680087889937)
              ·
                refine ⟨19258116441805260065917453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25677488589073680087889937 19258116441805260065917453)
                ·
                  refine ⟨7221793665676972524719045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19258116441805260065917453 7221793665676972524719045)
                  ·
                    refine ⟨1354086312314432348384821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221793665676972524719045 1354086312314432348384821)
                    ·
                      rfl

theorem cell23_7911221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7911221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911221 prefixEnd_7911221 := by exact prefixLift 7911221
  have htrace : WordTrace (prefixWord ++ tailWord_7911221) baseStart_7911221 baseEnd_7911221 := by
    simpa [prefixWord, tailWord_7911221, baseEnd_7911221] using wordTrace_append hprefix tailTrace_7911221
  have hstable : (prefixWord ++ tailWord_7911221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911221).length < 2 ^ (prefixWord ++ tailWord_7911221).sum := by decide
  have hdescent : baseEnd_7911221 < baseStart_7911221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911278 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7911278 : Nat := 118140960795 + 7911278 * 2 ^ 59
def prefixEnd_7911278 : Nat := 4983230072969 + 3 ^ 40 * 7911278 * 2
def baseEnd_7911278 : Nat := 4062288205340603322141701

theorem tailTrace_7911278 : CollatzResearch.WordTrace tailWord_7911278 prefixEnd_7911278 4062288205340603322141701 := by
  unfold tailWord_7911278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068501729099802444732811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192365342555198946371908325 36068501729099802444732811)
  ·
    refine ⟨54102752593649703667099217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36068501729099802444732811 54102752593649703667099217)
    ·
      refine ⟨40577064445237277750324413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54102752593649703667099217 40577064445237277750324413)
      ·
        refine ⟨15216399166963979156371655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40577064445237277750324413 15216399166963979156371655)
        ·
          refine ⟨22824598750445968734557483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15216399166963979156371655 22824598750445968734557483)
          ·
            refine ⟨34236898125668953101836225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22824598750445968734557483 34236898125668953101836225)
            ·
              refine ⟨25677673594251714826377169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34236898125668953101836225 25677673594251714826377169)
              ·
                refine ⟨19258255195688786119782877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25677673594251714826377169 19258255195688786119782877)
                ·
                  refine ⟨7221845698383294794918579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19258255195688786119782877 7221845698383294794918579)
                  ·
                    refine ⟨10832768547574942192377869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7221845698383294794918579 10832768547574942192377869)
                    ·
                      refine ⟨4062288205340603322141701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832768547574942192377869 4062288205340603322141701)
                      ·
                        rfl

theorem cell23_7911278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7911278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911278 prefixEnd_7911278 := by exact prefixLift 7911278
  have htrace : WordTrace (prefixWord ++ tailWord_7911278) baseStart_7911278 baseEnd_7911278 := by
    simpa [prefixWord, tailWord_7911278, baseEnd_7911278] using wordTrace_append hprefix tailTrace_7911278
  have hstable : (prefixWord ++ tailWord_7911278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911278).length < 2 ^ (prefixWord ++ tailWord_7911278).sum := by decide
  have hdescent : baseEnd_7911278 < baseStart_7911278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911324 : List Nat := [2, 2, 3, 3, 1, 1, 1, 10]
def baseStart_7911324 : Nat := 118140960795 + 7911324 * 2 ^ 59
def prefixEnd_7911324 : Nat := 4983230072969 + 3 ^ 40 * 7911324 * 2
def baseEnd_7911324 : Nat := 150455993535211486746907

theorem tailTrace_7911324 : CollatzResearch.WordTrace tailWord_7911324 prefixEnd_7911324 150455993535211486746907 := by
  unfold tailWord_7911324
  simp only [CollatzResearch.WordTrace]
  refine ⟨144274845795315884707018513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192366461060421179609358017 144274845795315884707018513)
  ·
    refine ⟨108206134346486913530263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144274845795315884707018513 108206134346486913530263885)
    ·
      refine ⟨40577300379932592573848957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108206134346486913530263885 40577300379932592573848957)
      ·
        refine ⟨15216487642474722215193359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40577300379932592573848957 15216487642474722215193359)
        ·
          refine ⟨22824731463712083322790039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15216487642474722215193359 22824731463712083322790039)
          ·
            refine ⟨34237097195568124984185059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22824731463712083322790039 34237097195568124984185059)
            ·
              refine ⟨51355645793352187476277589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34237097195568124984185059 51355645793352187476277589)
              ·
                refine ⟨150455993535211486746907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51355645793352187476277589 150455993535211486746907)
                ·
                  rfl

theorem cell23_7911324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 10].length) (baseStart_7911324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911324 prefixEnd_7911324 := by exact prefixLift 7911324
  have htrace : WordTrace (prefixWord ++ tailWord_7911324) baseStart_7911324 baseEnd_7911324 := by
    simpa [prefixWord, tailWord_7911324, baseEnd_7911324] using wordTrace_append hprefix tailTrace_7911324
  have hstable : (prefixWord ++ tailWord_7911324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911324).length < 2 ^ (prefixWord ++ tailWord_7911324).sum := by decide
  have hdescent : baseEnd_7911324 < baseStart_7911324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911337 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_7911337 : Nat := 118140960795 + 7911337 * 2 ^ 59
def prefixEnd_7911337 : Nat := 4983230072969 + 3 ^ 40 * 7911337 * 2
def baseEnd_7911337 : Nat := 1354106166899739530434643

theorem tailTrace_7911337 : CollatzResearch.WordTrace tailWord_7911337 prefixEnd_7911337 1354106166899739530434643 := by
  unfold tailWord_7911337
  simp only [CollatzResearch.WordTrace]
  refine ⟨288550165739584672634260265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192366777159723115089506843 288550165739584672634260265)
  ·
    refine ⟨216412624304688504475695199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288550165739584672634260265 216412624304688504475695199)
    ·
      refine ⟨324618936457032756713542799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216412624304688504475695199 324618936457032756713542799)
      ·
        refine ⟨486928404685549135070314199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324618936457032756713542799 486928404685549135070314199)
        ·
          refine ⟨730392607028323702605471299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486928404685549135070314199 730392607028323702605471299)
          ·
            refine ⟨1095588910542485553908206949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730392607028323702605471299 1095588910542485553908206949)
            ·
              refine ⟨205422920726716041357788803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1095588910542485553908206949 205422920726716041357788803)
              ·
                refine ⟨308134381090074062036683205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205422920726716041357788803 308134381090074062036683205)
                ·
                  refine ⟨57775196454388886631878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308134381090074062036683205 57775196454388886631878101)
                  ·
                    refine ⟨1354106166899739530434643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57775196454388886631878101 1354106166899739530434643)
                    ·
                      rfl

theorem cell23_7911337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_7911337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911337 prefixEnd_7911337 := by exact prefixLift 7911337
  have htrace : WordTrace (prefixWord ++ tailWord_7911337) baseStart_7911337 baseEnd_7911337 := by
    simpa [prefixWord, tailWord_7911337, baseEnd_7911337] using wordTrace_append hprefix tailTrace_7911337
  have hstable : (prefixWord ++ tailWord_7911337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911337).length < 2 ^ (prefixWord ++ tailWord_7911337).sum := by decide
  have hdescent : baseEnd_7911337 < baseStart_7911337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911368 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_7911368 : Nat := 118140960795 + 7911368 * 2 ^ 59
def prefixEnd_7911368 : Nat := 4983230072969 + 3 ^ 40 * 7911368 * 2
def baseEnd_7911368 : Nat := 4062334418599507970016287

theorem tailTrace_7911368 : CollatzResearch.WordTrace tailWord_7911368 prefixEnd_7911368 4062334418599507970016287 := by
  unfold tailWord_7911368
  simp only [CollatzResearch.WordTrace]
  refine ⟨144275648201236182464319379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192367530934981576619092505 144275648201236182464319379)
  ·
    refine ⟨216413472301854273696479069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144275648201236182464319379 216413472301854273696479069)
    ·
      refine ⟨81155052113195352636179651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216413472301854273696479069 81155052113195352636179651)
      ·
        refine ⟨121732578169793028954269477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81155052113195352636179651 121732578169793028954269477)
        ·
          refine ⟨22824858406836192928925527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121732578169793028954269477 22824858406836192928925527)
          ·
            refine ⟨34237287610254289393388291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22824858406836192928925527 34237287610254289393388291)
            ·
              refine ⟨51355931415381434090082437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34237287610254289393388291 51355931415381434090082437)
              ·
                refine ⟨9629237140384018891890457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51355931415381434090082437 9629237140384018891890457)
                ·
                  refine ⟨7221927855288014168917843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9629237140384018891890457 7221927855288014168917843)
                  ·
                    refine ⟨10832891782932021253376765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7221927855288014168917843 10832891782932021253376765)
                    ·
                      refine ⟨4062334418599507970016287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10832891782932021253376765 4062334418599507970016287)
                      ·
                        rfl

theorem cell23_7911368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_7911368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911368 prefixEnd_7911368 := by exact prefixLift 7911368
  have htrace : WordTrace (prefixWord ++ tailWord_7911368) baseStart_7911368 baseEnd_7911368 := by
    simpa [prefixWord, tailWord_7911368, baseEnd_7911368] using wordTrace_append hprefix tailTrace_7911368
  have hstable : (prefixWord ++ tailWord_7911368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911368).length < 2 ^ (prefixWord ++ tailWord_7911368).sum := by decide
  have hdescent : baseEnd_7911368 < baseStart_7911368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911374 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7911374 : Nat := 118140960795 + 7911374 * 2 ^ 59
def prefixEnd_7911374 : Nat := 4983230072969 + 3 ^ 40 * 7911374 * 2
def baseEnd_7911374 : Nat := 4062337499483434946541259

theorem tailTrace_7911374 : CollatzResearch.WordTrace tailWord_7911374 prefixEnd_7911374 4062337499483434946541259 := by
  unfold tailWord_7911374
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068939405056328494169647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192367676826967085302238117 36068939405056328494169647)
  ·
    refine ⟨54103409107584492741254471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36068939405056328494169647 54103409107584492741254471)
    ·
      refine ⟨81155113661376739111881707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54103409107584492741254471 81155113661376739111881707)
      ·
        refine ⟨121732670492065108667822561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81155113661376739111881707 121732670492065108667822561)
        ·
          refine ⟨91299502869048831500866921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121732670492065108667822561 91299502869048831500866921)
          ·
            refine ⟨68474627151786623625650191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91299502869048831500866921 68474627151786623625650191)
            ·
              refine ⟨102711940727679935438475287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68474627151786623625650191 102711940727679935438475287)
              ·
                refine ⟨154067911091519903157712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102711940727679935438475287 154067911091519903157712931)
                ·
                  refine ⟨231101866637279854736569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154067911091519903157712931 231101866637279854736569397)
                  ·
                    refine ⟨21665799997244986381553381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231101866637279854736569397 21665799997244986381553381)
                    ·
                      refine ⟨4062337499483434946541259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21665799997244986381553381 4062337499483434946541259)
                      ·
                        rfl

theorem cell23_7911374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7911374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911374 prefixEnd_7911374 := by exact prefixLift 7911374
  have htrace : WordTrace (prefixWord ++ tailWord_7911374) baseStart_7911374 baseEnd_7911374 := by
    simpa [prefixWord, tailWord_7911374, baseEnd_7911374] using wordTrace_append hprefix tailTrace_7911374
  have hstable : (prefixWord ++ tailWord_7911374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911374).length < 2 ^ (prefixWord ++ tailWord_7911374).sum := by decide
  have hdescent : baseEnd_7911374 < baseStart_7911374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911384 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_7911384 : Nat := 118140960795 + 7911384 * 2 ^ 59
def prefixEnd_7911384 : Nat := 4983230072969 + 3 ^ 40 * 7911384 * 2
def baseEnd_7911384 : Nat := 1354114211429993302472071

theorem tailTrace_7911384 : CollatzResearch.WordTrace tailWord_7911384 prefixEnd_7911384 1354114211429993302472071 := by
  unfold tailWord_7911384
  simp only [CollatzResearch.WordTrace]
  refine ⟨144275939985207199830610603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192367919980276266440814137 144275939985207199830610603)
  ·
    refine ⟨216413909977810799745915905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144275939985207199830610603 216413909977810799745915905)
    ·
      refine ⟨162310432483358099809436929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216413909977810799745915905 162310432483358099809436929)
      ·
        refine ⟨121732824362518574857077697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162310432483358099809436929 121732824362518574857077697)
        ·
          refine ⟨91299618271888931142808273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121732824362518574857077697 91299618271888931142808273)
          ·
            refine ⟨68474713703916698357106205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91299618271888931142808273 68474713703916698357106205)
            ·
              refine ⟨25678017638968761883914827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68474713703916698357106205 25678017638968761883914827)
              ·
                refine ⟨38517026458453142825872241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25678017638968761883914827 38517026458453142825872241)
                ·
                  refine ⟨28887769843839857119404181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38517026458453142825872241 28887769843839857119404181)
                  ·
                    refine ⟨1354114211429993302472071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28887769843839857119404181 1354114211429993302472071)
                    ·
                      rfl

theorem cell23_7911384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_7911384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911384 prefixEnd_7911384 := by exact prefixLift 7911384
  have htrace : WordTrace (prefixWord ++ tailWord_7911384) baseStart_7911384 baseEnd_7911384 := by
    simpa [prefixWord, tailWord_7911384, baseEnd_7911384] using wordTrace_append hprefix tailTrace_7911384
  have hstable : (prefixWord ++ tailWord_7911384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911384).length < 2 ^ (prefixWord ++ tailWord_7911384).sum := by decide
  have hdescent : baseEnd_7911384 < baseStart_7911384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911431 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 7]
def baseStart_7911431 : Nat := 118140960795 + 7911431 * 2 ^ 59
def prefixEnd_7911431 : Nat := 4983230072969 + 3 ^ 40 * 7911431 * 2
def baseEnd_7911431 : Nat := 451374085320082358169833

theorem tailTrace_7911431 : CollatzResearch.WordTrace tailWord_7911431 prefixEnd_7911431 451374085320082358169833 := by
  unfold tailWord_7911431
  simp only [CollatzResearch.WordTrace]
  refine ⟨288553594201244126688182147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192369062800829417792121431 288553594201244126688182147)
  ·
    refine ⟨432830391301866190032273221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288553594201244126688182147 432830391301866190032273221)
    ·
      refine ⟨81155698369099910631051229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432830391301866190032273221 81155698369099910631051229)
      ·
        refine ⟨30433386888412466486644211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81155698369099910631051229 30433386888412466486644211)
        ·
          refine ⟨45650080332618699729966317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30433386888412466486644211 45650080332618699729966317)
          ·
            refine ⟨17118780124732012398737369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45650080332618699729966317 17118780124732012398737369)
            ·
              refine ⟨12839085093549009299053027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17118780124732012398737369 12839085093549009299053027)
              ·
                refine ⟨19258627640323513948579541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12839085093549009299053027 19258627640323513948579541)
                ·
                  refine ⟨451374085320082358169833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19258627640323513948579541 451374085320082358169833)
                  ·
                    rfl

theorem cell23_7911431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 7].length) (baseStart_7911431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911431 prefixEnd_7911431 := by exact prefixLift 7911431
  have htrace : WordTrace (prefixWord ++ tailWord_7911431) baseStart_7911431 baseEnd_7911431 := by
    simpa [prefixWord, tailWord_7911431, baseEnd_7911431] using wordTrace_append hprefix tailTrace_7911431
  have hstable : (prefixWord ++ tailWord_7911431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911431).length < 2 ^ (prefixWord ++ tailWord_7911431).sum := by decide
  have hdescent : baseEnd_7911431 < baseStart_7911431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911478 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_7911478 : Nat := 118140960795 + 7911478 * 2 ^ 59
def prefixEnd_7911478 : Nat := 4983230072969 + 3 ^ 40 * 7911478 * 2
def baseEnd_7911478 : Nat := 1354130300490500846546927

theorem tailTrace_7911478 : CollatzResearch.WordTrace tailWord_7911478 prefixEnd_7911478 1354130300490500846546927 := by
  unfold tailWord_7911478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034706777004615857196443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192370205621382569143428725 18034706777004615857196443)
  ·
    refine ⟨27052060165506923785794665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18034706777004615857196443 27052060165506923785794665)
    ·
      refine ⟨20289045124130192839345999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27052060165506923785794665 20289045124130192839345999)
      ·
        refine ⟨30433567686195289259018999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20289045124130192839345999 30433567686195289259018999)
        ·
          refine ⟨45650351529292933888528499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30433567686195289259018999 45650351529292933888528499)
          ·
            refine ⟨68475527293939400832792749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45650351529292933888528499 68475527293939400832792749)
            ·
              refine ⟨25678322735227275312297281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68475527293939400832792749 25678322735227275312297281)
              ·
                refine ⟨19258742051420456484222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25678322735227275312297281 19258742051420456484222961)
                ·
                  refine ⟨14444056538565342363167221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19258742051420456484222961 14444056538565342363167221)
                  ·
                    refine ⟨1354130300490500846546927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14444056538565342363167221 1354130300490500846546927)
                    ·
                      rfl

theorem cell23_7911478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_7911478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911478 prefixEnd_7911478 := by exact prefixLift 7911478
  have htrace : WordTrace (prefixWord ++ tailWord_7911478) baseStart_7911478 baseEnd_7911478 := by
    simpa [prefixWord, tailWord_7911478, baseEnd_7911478] using wordTrace_append hprefix tailTrace_7911478
  have hstable : (prefixWord ++ tailWord_7911478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911478).length < 2 ^ (prefixWord ++ tailWord_7911478).sum := by decide
  have hdescent : baseEnd_7911478 < baseStart_7911478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911491 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 3, 4]
def baseStart_7911491 : Nat := 118140960795 + 7911491 * 2 ^ 59
def prefixEnd_7911491 : Nat := 4983230072969 + 3 ^ 40 * 7911491 * 2
def baseEnd_7911491 : Nat := 1354132525573336996259407

theorem tailTrace_7911491 : CollatzResearch.WordTrace tailWord_7911491 prefixEnd_7911491 1354132525573336996259407 := by
  unfold tailWord_7911491
  simp only [CollatzResearch.WordTrace]
  refine ⟨288555782581026756935366327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192370521720684504623577551 288555782581026756935366327)
  ·
    refine ⟨432833673871540135403049491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288555782581026756935366327 432833673871540135403049491)
    ·
      refine ⟨649250510807310203104574237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432833673871540135403049491 649250510807310203104574237)
      ·
        refine ⟨243468941552741326164215339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 649250510807310203104574237 243468941552741326164215339)
        ·
          refine ⟨365203412329111989246323009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243468941552741326164215339 365203412329111989246323009)
          ·
            refine ⟨273902559246833991934742257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365203412329111989246323009 273902559246833991934742257)
            ·
              refine ⟨205426919435125493951056693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273902559246833991934742257 205426919435125493951056693)
              ·
                refine ⟨19258773697043015057911565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205426919435125493951056693 19258773697043015057911565)
                ·
                  refine ⟨7222040136391130646716837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19258773697043015057911565 7222040136391130646716837)
                  ·
                    refine ⟨1354132525573336996259407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222040136391130646716837 1354132525573336996259407)
                    ·
                      rfl

theorem cell23_7911491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 4].length) (baseStart_7911491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911491 prefixEnd_7911491 := by exact prefixLift 7911491
  have htrace : WordTrace (prefixWord ++ tailWord_7911491) baseStart_7911491 baseEnd_7911491 := by
    simpa [prefixWord, tailWord_7911491, baseEnd_7911491] using wordTrace_append hprefix tailTrace_7911491
  have hstable : (prefixWord ++ tailWord_7911491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911491).length < 2 ^ (prefixWord ++ tailWord_7911491).sum := by decide
  have hdescent : baseEnd_7911491 < baseStart_7911491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911538 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_7911538 : Nat := 118140960795 + 7911538 * 2 ^ 59
def prefixEnd_7911538 : Nat := 4983230072969 + 3 ^ 40 * 7911538 * 2
def baseEnd_7911538 : Nat := 451380190034530256098945

theorem tailTrace_7911538 : CollatzResearch.WordTrace tailWord_7911538 prefixEnd_7911538 451380190034530256098945 := by
  unfold tailWord_7911538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72139374202964120990581817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192371664541237655974884845 72139374202964120990581817)
  ·
    refine ⟨54104530652223090742936363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72139374202964120990581817 54104530652223090742936363)
    ·
      refine ⟨81156795978334636114404545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54104530652223090742936363 81156795978334636114404545)
      ·
        refine ⟨60867596983750977085803409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81156795978334636114404545 60867596983750977085803409)
        ·
          refine ⟨45650697737813232814352557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60867596983750977085803409 45650697737813232814352557)
          ·
            refine ⟨17119011651679962305382209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45650697737813232814352557 17119011651679962305382209)
            ·
              refine ⟨12839258738759971729036657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17119011651679962305382209 12839258738759971729036657)
              ·
                refine ⟨9629444054069978796777493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12839258738759971729036657 9629444054069978796777493)
                ·
                  refine ⟨451380190034530256098945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9629444054069978796777493 451380190034530256098945)
                  ·
                    rfl

theorem cell23_7911538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_7911538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911538 prefixEnd_7911538 := by exact prefixLift 7911538
  have htrace : WordTrace (prefixWord ++ tailWord_7911538) baseStart_7911538 baseEnd_7911538 := by
    simpa [prefixWord, tailWord_7911538, baseEnd_7911538] using wordTrace_append hprefix tailTrace_7911538
  have hstable : (prefixWord ++ tailWord_7911538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911538).length < 2 ^ (prefixWord ++ tailWord_7911538).sum := by decide
  have hdescent : baseEnd_7911538 < baseStart_7911538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911542 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_7911542 : Nat := 118140960795 + 7911542 * 2 ^ 59
def prefixEnd_7911542 : Nat := 4983230072969 + 3 ^ 40 * 7911542 * 2
def baseEnd_7911542 : Nat := 1354141254744463429746829

theorem tailTrace_7911542 : CollatzResearch.WordTrace tailWord_7911542 prefixEnd_7911542 1354141254744463429746829 := by
  unfold tailWord_7911542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034852668990124540342055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192371761802561328430315253 18034852668990124540342055)
  ·
    refine ⟨27052279003485186810513083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18034852668990124540342055 27052279003485186810513083)
    ·
      refine ⟨40578418505227780215769625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27052279003485186810513083 40578418505227780215769625)
      ·
        refine ⟨30433813878920835161827219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40578418505227780215769625 30433813878920835161827219)
        ·
          refine ⟨45650720818381252742740829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30433813878920835161827219 45650720818381252742740829)
          ·
            refine ⟨17119020306892969778527811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45650720818381252742740829 17119020306892969778527811)
            ·
              refine ⟨25678530460339454667791717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17119020306892969778527811 25678530460339454667791717)
              ·
                refine ⟨4814724461313647750210947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25678530460339454667791717 4814724461313647750210947)
                ·
                  refine ⟨7222086691970471625316421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814724461313647750210947 7222086691970471625316421)
                  ·
                    refine ⟨1354141254744463429746829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222086691970471625316421 1354141254744463429746829)
                    ·
                      rfl

theorem cell23_7911542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_7911542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911542 prefixEnd_7911542 := by exact prefixLift 7911542
  have htrace : WordTrace (prefixWord ++ tailWord_7911542) baseStart_7911542 baseEnd_7911542 := by
    simpa [prefixWord, tailWord_7911542, baseEnd_7911542] using wordTrace_append hprefix tailTrace_7911542
  have hstable : (prefixWord ++ tailWord_7911542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911542).length < 2 ^ (prefixWord ++ tailWord_7911542).sum := by decide
  have hdescent : baseEnd_7911542 < baseStart_7911542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911575 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7911575 : Nat := 118140960795 + 7911575 * 2 ^ 59
def prefixEnd_7911575 : Nat := 4983230072969 + 3 ^ 40 * 7911575 * 2
def baseEnd_7911575 : Nat := 4062440709094988660127835

theorem tailTrace_7911575 : CollatzResearch.WordTrace tailWord_7911575 prefixEnd_7911575 4062440709094988660127835 := by
  unfold tailWord_7911575
  simp only [CollatzResearch.WordTrace]
  refine ⟨288558846312722439281424179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192372564208481626187616119 288558846312722439281424179)
  ·
    refine ⟨432838269469083658922136269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288558846312722439281424179 432838269469083658922136269)
    ·
      refine ⟨162314351050906372095801101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432838269469083658922136269 162314351050906372095801101)
      ·
        refine ⟨60867881644089889535925413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162314351050906372095801101 60867881644089889535925413)
        ·
          refine ⟨11412727808266854287986015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60867881644089889535925413 11412727808266854287986015)
          ·
            refine ⟨17119091712400281431979023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412727808266854287986015 17119091712400281431979023)
            ·
              refine ⟨25678637568600422147968535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17119091712400281431979023 25678637568600422147968535)
              ·
                refine ⟨38517956352900633221952803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25678637568600422147968535 38517956352900633221952803)
                ·
                  refine ⟨57776934529350949832929205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38517956352900633221952803 57776934529350949832929205)
                  ·
                    refine ⟨5416587612126651546837113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57776934529350949832929205 5416587612126651546837113)
                    ·
                      refine ⟨4062440709094988660127835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416587612126651546837113 4062440709094988660127835)
                      ·
                        rfl

theorem cell23_7911575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7911575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911575 prefixEnd_7911575 := by exact prefixLift 7911575
  have htrace : WordTrace (prefixWord ++ tailWord_7911575) baseStart_7911575 baseEnd_7911575 := by
    simpa [prefixWord, tailWord_7911575, baseEnd_7911575] using wordTrace_append hprefix tailTrace_7911575
  have hstable : (prefixWord ++ tailWord_7911575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911575).length < 2 ^ (prefixWord ++ tailWord_7911575).sum := by decide
  have hdescent : baseEnd_7911575 < baseStart_7911575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911585 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_7911585 : Nat := 118140960795 + 7911585 * 2 ^ 59
def prefixEnd_7911585 : Nat := 4983230072969 + 3 ^ 40 * 7911585 * 2
def baseEnd_7911585 : Nat := 1354148614633844540334263

theorem tailTrace_7911585 : CollatzResearch.WordTrace tailWord_7911585 prefixEnd_7911585 1354148614633844540334263 := by
  unfold tailWord_7911585
  simp only [CollatzResearch.WordTrace]
  refine ⟨288559211042686210989288209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192372807361790807326192139 288559211042686210989288209)
  ·
    refine ⟨216419408282014658241966157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288559211042686210989288209 216419408282014658241966157)
    ·
      refine ⟨81157278105755496840737309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216419408282014658241966157 81157278105755496840737309)
      ·
        refine ⟨30433979289658311315276491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81157278105755496840737309 30433979289658311315276491)
        ·
          refine ⟨45650968934487466972914737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30433979289658311315276491 45650968934487466972914737)
          ·
            refine ⟨34238226700865600229686053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45650968934487466972914737 34238226700865600229686053)
            ·
              refine ⟨6419667506412300043066135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34238226700865600229686053 6419667506412300043066135)
              ·
                refine ⟨9629501259618450064599203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419667506412300043066135 9629501259618450064599203)
                ·
                  refine ⟨14444251889427675096898805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9629501259618450064599203 14444251889427675096898805)
                  ·
                    refine ⟨1354148614633844540334263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14444251889427675096898805 1354148614633844540334263)
                    ·
                      rfl

theorem cell23_7911585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_7911585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911585 prefixEnd_7911585 := by exact prefixLift 7911585
  have htrace : WordTrace (prefixWord ++ tailWord_7911585) baseStart_7911585 baseEnd_7911585 := by
    simpa [prefixWord, tailWord_7911585, baseEnd_7911585] using wordTrace_append hprefix tailTrace_7911585
  have hstable : (prefixWord ++ tailWord_7911585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911585).length < 2 ^ (prefixWord ++ tailWord_7911585).sum := by decide
  have hdescent : baseEnd_7911585 < baseStart_7911585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911650 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7911650 : Nat := 118140960795 + 7911650 * 2 ^ 59
def prefixEnd_7911650 : Nat := 4983230072969 + 3 ^ 40 * 7911650 * 2
def baseEnd_7911650 : Nat := 4062479220144075866689991

theorem tailTrace_7911650 : CollatzResearch.WordTrace tailWord_7911650 prefixEnd_7911650 4062479220144075866689991 := by
  unfold tailWord_7911650
  simp only [CollatzResearch.WordTrace]
  refine ⟨72140395446862681772601101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192374387858300484726936269 72140395446862681772601101)
  ·
    refine ⟨27052648292573505664725413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72140395446862681772601101 27052648292573505664725413)
    ·
      refine ⟨5072371554857532312136015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27052648292573505664725413 5072371554857532312136015)
      ·
        refine ⟨7608557332286298468204023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072371554857532312136015 7608557332286298468204023)
        ·
          refine ⟨11412835998429447702306035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608557332286298468204023 11412835998429447702306035)
          ·
            refine ⟨17119253997644171553459053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412835998429447702306035 17119253997644171553459053)
            ·
              refine ⟨6419720249116564332547145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17119253997644171553459053 6419720249116564332547145)
              ·
                refine ⟨4814790186837423249410359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419720249116564332547145 4814790186837423249410359)
                ·
                  refine ⟨7222185280256134874115539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814790186837423249410359 7222185280256134874115539)
                  ·
                    refine ⟨10833277920384202311173309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7222185280256134874115539 10833277920384202311173309)
                    ·
                      refine ⟨4062479220144075866689991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10833277920384202311173309 4062479220144075866689991)
                      ·
                        rfl

theorem cell23_7911650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7911650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911650 prefixEnd_7911650 := by exact prefixLift 7911650
  have htrace : WordTrace (prefixWord ++ tailWord_7911650) baseStart_7911650 baseEnd_7911650 := by
    simpa [prefixWord, tailWord_7911650, baseEnd_7911650] using wordTrace_append hprefix tailTrace_7911650
  have hstable : (prefixWord ++ tailWord_7911650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911650).length < 2 ^ (prefixWord ++ tailWord_7911650).sum := by decide
  have hdescent : baseEnd_7911650 < baseStart_7911650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911656 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7911656 : Nat := 118140960795 + 7911656 * 2 ^ 59
def prefixEnd_7911656 : Nat := 4983230072969 + 3 ^ 40 * 7911656 * 2
def baseEnd_7911656 : Nat := 4062482301028002843214963

theorem tailTrace_7911656 : CollatzResearch.WordTrace tailWord_7911656 prefixEnd_7911656 4062482301028002843214963 := by
  unfold tailWord_7911656
  simp only [CollatzResearch.WordTrace]
  refine ⟨144280900312714495057561411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192374533750285993410081881 144280900312714495057561411)
  ·
    refine ⟨216421350469071742586342117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144280900312714495057561411 216421350469071742586342117)
    ·
      refine ⟨40579003212950951734939147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216421350469071742586342117 40579003212950951734939147)
      ·
        refine ⟨60868504819426427602408721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40579003212950951734939147 60868504819426427602408721)
        ·
          refine ⟨45651378614569820701806541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60868504819426427602408721 45651378614569820701806541)
          ·
            refine ⟨17119266980463682763177453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45651378614569820701806541 17119266980463682763177453)
            ·
              refine ⟨6419725117673881036191545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17119266980463682763177453 6419725117673881036191545)
              ·
                refine ⟨4814793838255410777143659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419725117673881036191545 4814793838255410777143659)
                ·
                  refine ⟨7222190757383116165715489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814793838255410777143659 7222190757383116165715489)
                  ·
                    refine ⟨5416643068037337124286617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222190757383116165715489 5416643068037337124286617)
                    ·
                      refine ⟨4062482301028002843214963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416643068037337124286617 4062482301028002843214963)
                      ·
                        rfl

theorem cell23_7911656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7911656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911656 prefixEnd_7911656 := by exact prefixLift 7911656
  have htrace : WordTrace (prefixWord ++ tailWord_7911656) baseStart_7911656 baseEnd_7911656 := by
    simpa [prefixWord, tailWord_7911656, baseEnd_7911656] using wordTrace_append hprefix tailTrace_7911656
  have hstable : (prefixWord ++ tailWord_7911656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911656).length < 2 ^ (prefixWord ++ tailWord_7911656).sum := by decide
  have hdescent : baseEnd_7911656 < baseStart_7911656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911695 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 6, 2, 2]
def baseStart_7911695 : Nat := 118140960795 + 7911695 * 2 ^ 59
def prefixEnd_7911695 : Nat := 4983230072969 + 3 ^ 40 * 7911695 * 2
def baseEnd_7911695 : Nat := 4062502326773528190627283

theorem tailTrace_7911695 : CollatzResearch.WordTrace tailWord_7911695 prefixEnd_7911695 4062502326773528190627283 := by
  unfold tailWord_7911695
  simp only [CollatzResearch.WordTrace]
  refine ⟨288563223072287699775792539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192375482048191799850528359 288563223072287699775792539)
  ·
    refine ⟨432844834608431549663688809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288563223072287699775792539 432844834608431549663688809)
    ·
      refine ⟨324633625956323662247766607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432844834608431549663688809 324633625956323662247766607)
      ·
        refine ⟨486950438934485493371649911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324633625956323662247766607 486950438934485493371649911)
        ·
          refine ⟨730425658401728240057474867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486950438934485493371649911 730425658401728240057474867)
          ·
            refine ⟨1095638487602592360086212301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730425658401728240057474867 1095638487602592360086212301)
            ·
              refine ⟨410864432850972135032329613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095638487602592360086212301 410864432850972135032329613)
              ·
                refine ⟨154074162319114550637123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410864432850972135032329613 154074162319114550637123605)
                ·
                  refine ⟨7222226358708494561115169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154074162319114550637123605 7222226358708494561115169)
                  ·
                    refine ⟨5416669769031370920836377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222226358708494561115169 5416669769031370920836377)
                    ·
                      refine ⟨4062502326773528190627283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416669769031370920836377 4062502326773528190627283)
                      ·
                        rfl

theorem cell23_7911695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 2, 2].length) (baseStart_7911695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911695 prefixEnd_7911695 := by exact prefixLift 7911695
  have htrace : WordTrace (prefixWord ++ tailWord_7911695) baseStart_7911695 baseEnd_7911695 := by
    simpa [prefixWord, tailWord_7911695, baseEnd_7911695] using wordTrace_append hprefix tailTrace_7911695
  have hstable : (prefixWord ++ tailWord_7911695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911695).length < 2 ^ (prefixWord ++ tailWord_7911695).sum := by decide
  have hdescent : baseEnd_7911695 < baseStart_7911695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911708 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7911708 : Nat := 118140960795 + 7911708 * 2 ^ 59
def prefixEnd_7911708 : Nat := 4983230072969 + 3 ^ 40 * 7911708 * 2
def baseEnd_7911708 : Nat := 4062509002022036639764723

theorem tailTrace_7911708 : CollatzResearch.WordTrace tailWord_7911708 prefixEnd_7911708 4062509002022036639764723 := by
  unfold tailWord_7911708
  simp only [CollatzResearch.WordTrace]
  refine ⟨144281848610620301498007889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192375798147493735330677185 144281848610620301498007889)
  ·
    refine ⟨108211386457965226123505917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144281848610620301498007889 108211386457965226123505917)
    ·
      refine ⟨40579269921736959796314719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108211386457965226123505917 40579269921736959796314719)
      ·
        refine ⟨60868904882605439694472079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40579269921736959796314719 60868904882605439694472079)
        ·
          refine ⟨91303357323908159541708119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60868904882605439694472079 91303357323908159541708119)
          ·
            refine ⟨136955035985862239312562179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91303357323908159541708119 136955035985862239312562179)
            ·
              refine ⟨205432553978793358968843269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136955035985862239312562179 205432553978793358968843269)
              ·
                refine ⟨38518603871023754806658113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205432553978793358968843269 38518603871023754806658113)
                ·
                  refine ⟨28888952903267816104993585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38518603871023754806658113 28888952903267816104993585)
                  ·
                    refine ⟨21666714677450862078745189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28888952903267816104993585 21666714677450862078745189)
                    ·
                      refine ⟨4062509002022036639764723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21666714677450862078745189 4062509002022036639764723)
                      ·
                        rfl

theorem cell23_7911708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7911708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911708 prefixEnd_7911708 := by exact prefixLift 7911708
  have htrace : WordTrace (prefixWord ++ tailWord_7911708) baseStart_7911708 baseEnd_7911708 := by
    simpa [prefixWord, tailWord_7911708, baseEnd_7911708] using wordTrace_append hprefix tailTrace_7911708
  have hstable : (prefixWord ++ tailWord_7911708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911708).length < 2 ^ (prefixWord ++ tailWord_7911708).sum := by decide
  have hdescent : baseEnd_7911708 < baseStart_7911708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911721 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_7911721 : Nat := 118140960795 + 7911721 * 2 ^ 59
def prefixEnd_7911721 : Nat := 4983230072969 + 3 ^ 40 * 7911721 * 2
def baseEnd_7911721 : Nat := 4062515677270545088902163

theorem tailTrace_7911721 : CollatzResearch.WordTrace tailWord_7911721 prefixEnd_7911721 4062515677270545088902163 := by
  unfold tailWord_7911721
  simp only [CollatzResearch.WordTrace]
  refine ⟨288564171370193506216239017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192376114246795670810826011 288564171370193506216239017)
  ·
    refine ⟨216423128527645129662179263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288564171370193506216239017 216423128527645129662179263)
    ·
      refine ⟨324634692791467694493268895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216423128527645129662179263 324634692791467694493268895)
      ·
        refine ⟨486952039187201541739903343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324634692791467694493268895 486952039187201541739903343)
        ·
          refine ⟨730428058780802312609855015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486952039187201541739903343 730428058780802312609855015)
          ·
            refine ⟨1095642088171203468914782523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730428058780802312609855015 1095642088171203468914782523)
            ·
              refine ⟨1643463132256805203372173785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095642088171203468914782523 1643463132256805203372173785)
              ·
                refine ⟨1232597349192603902529130339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643463132256805203372173785 1232597349192603902529130339)
                ·
                  refine ⟨1848896023788905853793695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232597349192603902529130339 1848896023788905853793695509)
                  ·
                    refine ⟨86667001115104961896579477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1848896023788905853793695509 86667001115104961896579477)
                    ·
                      refine ⟨4062515677270545088902163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86667001115104961896579477 4062515677270545088902163)
                      ·
                        rfl

theorem cell23_7911721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_7911721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911721 prefixEnd_7911721 := by exact prefixLift 7911721
  have htrace : WordTrace (prefixWord ++ tailWord_7911721) baseStart_7911721 baseEnd_7911721 := by
    simpa [prefixWord, tailWord_7911721, baseEnd_7911721] using wordTrace_append hprefix tailTrace_7911721
  have hstable : (prefixWord ++ tailWord_7911721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911721).length < 2 ^ (prefixWord ++ tailWord_7911721).sum := by decide
  have hdescent : baseEnd_7911721 < baseStart_7911721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911758 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7911758 : Nat := 118140960795 + 7911758 * 2 ^ 59
def prefixEnd_7911758 : Nat := 4983230072969 + 3 ^ 40 * 7911758 * 2
def baseEnd_7911758 : Nat := 4062534676054761444139493

theorem tailTrace_7911758 : CollatzResearch.WordTrace tailWord_7911758 prefixEnd_7911758 4062534676054761444139493 := by
  unfold tailWord_7911758
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070690108882432691916991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192377013914039641023557285 36070690108882432691916991)
  ·
    refine ⟨54106035163323649037875487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070690108882432691916991 54106035163323649037875487)
    ·
      refine ⟨81159052744985473556813231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54106035163323649037875487 81159052744985473556813231)
      ·
        refine ⟨121738579117478210335219847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81159052744985473556813231 121738579117478210335219847)
        ·
          refine ⟨182607868676217315502829771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121738579117478210335219847 182607868676217315502829771)
          ·
            refine ⟨273911803014325973254244657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182607868676217315502829771 273911803014325973254244657)
            ·
              refine ⟨205433852260744479940683493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273911803014325973254244657 205433852260744479940683493)
              ·
                refine ⟨38518847298889589988878155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205433852260744479940683493 38518847298889589988878155)
                ·
                  refine ⟨57778270948334384983317233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38518847298889589988878155 57778270948334384983317233)
                  ·
                    refine ⟨43333703211250788737487925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57778270948334384983317233 43333703211250788737487925)
                    ·
                      refine ⟨4062534676054761444139493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43333703211250788737487925 4062534676054761444139493)
                      ·
                        rfl

theorem cell23_7911758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7911758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911758 prefixEnd_7911758 := by exact prefixLift 7911758
  have htrace : WordTrace (prefixWord ++ tailWord_7911758) baseStart_7911758 baseEnd_7911758 := by
    simpa [prefixWord, tailWord_7911758, baseEnd_7911758] using wordTrace_append hprefix tailTrace_7911758
  have hstable : (prefixWord ++ tailWord_7911758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911758).length < 2 ^ (prefixWord ++ tailWord_7911758).sum := by decide
  have hdescent : baseEnd_7911758 < baseStart_7911758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911785 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 4, 2]
def baseStart_7911785 : Nat := 118140960795 + 7911785 * 2 ^ 59
def prefixEnd_7911785 : Nat := 4983230072969 + 3 ^ 40 * 7911785 * 2
def baseEnd_7911785 : Nat := 4062548540032432838501869

theorem tailTrace_7911785 : CollatzResearch.WordTrace tailWord_7911785 prefixEnd_7911785 4062548540032432838501869 := by
  unfold tailWord_7911785
  simp only [CollatzResearch.WordTrace]
  refine ⟨288566505641961645146568809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192377670427974430097712539 288566505641961645146568809)
  ·
    refine ⟨216424879231471233859926607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288566505641961645146568809 216424879231471233859926607)
    ·
      refine ⟨324637318847206850789889911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216424879231471233859926607 324637318847206850789889911)
      ·
        refine ⟨486955978270810276184834867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324637318847206850789889911 486955978270810276184834867)
        ·
          refine ⟨730433967406215414277252301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486955978270810276184834867 730433967406215414277252301)
          ·
            refine ⟨273912737777330780353969613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730433967406215414277252301 273912737777330780353969613)
            ·
              refine ⟨102717276666499042632738605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273912737777330780353969613 102717276666499042632738605)
              ·
                refine ⟨38518978749937140987276977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102717276666499042632738605 38518978749937140987276977)
                ·
                  refine ⟨28889234062452855740457733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38518978749937140987276977 28889234062452855740457733)
                  ·
                    refine ⟨5416731386709910451335825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28889234062452855740457733 5416731386709910451335825)
                    ·
                      refine ⟨4062548540032432838501869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416731386709910451335825 4062548540032432838501869)
                      ·
                        rfl

theorem cell23_7911785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 4, 2].length) (baseStart_7911785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911785 prefixEnd_7911785 := by exact prefixLift 7911785
  have htrace : WordTrace (prefixWord ++ tailWord_7911785) baseStart_7911785 baseEnd_7911785 := by
    simpa [prefixWord, tailWord_7911785, baseEnd_7911785] using wordTrace_append hprefix tailTrace_7911785
  have hstable : (prefixWord ++ tailWord_7911785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911785).length < 2 ^ (prefixWord ++ tailWord_7911785).sum := by decide
  have hdescent : baseEnd_7911785 < baseStart_7911785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911805 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_7911805 : Nat := 118140960795 + 7911805 * 2 ^ 59
def prefixEnd_7911805 : Nat := 4983230072969 + 3 ^ 40 * 7911805 * 2
def baseEnd_7911805 : Nat := 4062558809645522760251777

theorem tailTrace_7911805 : CollatzResearch.WordTrace tailWord_7911805 prefixEnd_7911805 4062558809645522760251777 := by
  unfold tailWord_7911805
  simp only [CollatzResearch.WordTrace]
  refine ⟨288567235101889188562296869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192378156734592792374864579 288567235101889188562296869)
  ·
    refine ⟨54106356581604222855430663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288567235101889188562296869 54106356581604222855430663)
    ·
      refine ⟨81159534872406334283145995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54106356581604222855430663 81159534872406334283145995)
      ·
        refine ⟨121739302308609501424718993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81159534872406334283145995 121739302308609501424718993)
        ·
          refine ⟨91304476731457126068539245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121739302308609501424718993 91304476731457126068539245)
          ·
            refine ⟨34239178774296422275702217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91304476731457126068539245 34239178774296422275702217)
            ·
              refine ⟨25679384080722316706776663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34239178774296422275702217 25679384080722316706776663)
              ·
                refine ⟨38519076121083475060164995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25679384080722316706776663 38519076121083475060164995)
                ·
                  refine ⟨57778614181625212590247493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38519076121083475060164995 57778614181625212590247493)
                  ·
                    refine ⟨10833490159054727360671405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57778614181625212590247493 10833490159054727360671405)
                    ·
                      refine ⟨4062558809645522760251777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10833490159054727360671405 4062558809645522760251777)
                      ·
                        rfl

theorem cell23_7911805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_7911805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911805 prefixEnd_7911805 := by exact prefixLift 7911805
  have htrace : WordTrace (prefixWord ++ tailWord_7911805) baseStart_7911805 baseEnd_7911805 := by
    simpa [prefixWord, tailWord_7911805, baseEnd_7911805] using wordTrace_append hprefix tailTrace_7911805
  have hstable : (prefixWord ++ tailWord_7911805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911805).length < 2 ^ (prefixWord ++ tailWord_7911805).sum := by decide
  have hdescent : baseEnd_7911805 < baseStart_7911805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911822 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7911822 : Nat := 118140960795 + 7911822 * 2 ^ 59
def prefixEnd_7911822 : Nat := 4983230072969 + 3 ^ 40 * 7911822 * 2
def baseEnd_7911822 : Nat := 4062567538816649193739199

theorem tailTrace_7911822 : CollatzResearch.WordTrace tailWord_7911822 prefixEnd_7911822 4062567538816649193739199 := by
  unfold tailWord_7911822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070981892853450058208215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192378570095218400310443813 36070981892853450058208215)
  ·
    refine ⟨54106472839280175087312323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070981892853450058208215 54106472839280175087312323)
    ·
      refine ⟨81159709258920262630968485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54106472839280175087312323 81159709258920262630968485)
      ·
        refine ⟨15217445486047549243306591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81159709258920262630968485 15217445486047549243306591)
        ·
          refine ⟨22826168229071323864959887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15217445486047549243306591 22826168229071323864959887)
          ·
            refine ⟨34239252343606985797439831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22826168229071323864959887 34239252343606985797439831)
            ·
              refine ⟨51358878515410478696159747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34239252343606985797439831 51358878515410478696159747)
              ·
                refine ⟨77038317773115718044239621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51358878515410478696159747 77038317773115718044239621)
                ·
                  refine ⟨14444684582459197133294929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77038317773115718044239621 14444684582459197133294929)
                  ·
                    refine ⟨10833513436844397849971197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14444684582459197133294929 10833513436844397849971197)
                    ·
                      refine ⟨4062567538816649193739199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10833513436844397849971197 4062567538816649193739199)
                      ·
                        rfl

theorem cell23_7911822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7911822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911822 prefixEnd_7911822 := by exact prefixLift 7911822
  have htrace : WordTrace (prefixWord ++ tailWord_7911822) baseStart_7911822 baseEnd_7911822 := by
    simpa [prefixWord, tailWord_7911822, baseEnd_7911822] using wordTrace_append hprefix tailTrace_7911822
  have hstable : (prefixWord ++ tailWord_7911822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911822).length < 2 ^ (prefixWord ++ tailWord_7911822).sum := by decide
  have hdescent : baseEnd_7911822 < baseStart_7911822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911892 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7911892 : Nat := 118140960795 + 7911892 * 2 ^ 59
def prefixEnd_7911892 : Nat := 4983230072969 + 3 ^ 40 * 7911892 * 2
def baseEnd_7911892 : Nat := 4062603482462463919863877

theorem tailTrace_7911892 : CollatzResearch.WordTrace tailWord_7911892 prefixEnd_7911892 4062603482462463919863877 := by
  unfold tailWord_7911892
  simp only [CollatzResearch.WordTrace]
  refine ⟨144285204126287001210356965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192380272168382668280475953 144285204126287001210356965)
  ·
    refine ⟨27053475773678812726941931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144285204126287001210356965 27053475773678812726941931)
    ·
      refine ⟨40580213660518219090412897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27053475773678812726941931 40580213660518219090412897)
      ·
        refine ⟨30435160245388664317809673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40580213660518219090412897 30435160245388664317809673)
        ·
          refine ⟨22826370184041498238357255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30435160245388664317809673 22826370184041498238357255)
          ·
            refine ⟨34239555276062247357535883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22826370184041498238357255 34239555276062247357535883)
            ·
              refine ⟨51359332914093371036303825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34239555276062247357535883 51359332914093371036303825)
              ·
                refine ⟨38519499685570028277227869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51359332914093371036303825 38519499685570028277227869)
                ·
                  refine ⟨14444812382088760603960451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38519499685570028277227869 14444812382088760603960451)
                  ·
                    refine ⟨21667218573133140905940677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14444812382088760603960451 21667218573133140905940677)
                    ·
                      refine ⟨4062603482462463919863877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21667218573133140905940677 4062603482462463919863877)
                      ·
                        rfl

theorem cell23_7911892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7911892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911892 prefixEnd_7911892 := by exact prefixLift 7911892
  have htrace : WordTrace (prefixWord ++ tailWord_7911892) baseStart_7911892 baseEnd_7911892 := by
    simpa [prefixWord, tailWord_7911892, baseEnd_7911892] using wordTrace_append hprefix tailTrace_7911892
  have hstable : (prefixWord ++ tailWord_7911892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911892).length < 2 ^ (prefixWord ++ tailWord_7911892).sum := by decide
  have hdescent : baseEnd_7911892 < baseStart_7911892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911912 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7911912 : Nat := 118140960795 + 7911912 * 2 ^ 59
def prefixEnd_7911912 : Nat := 4983230072969 + 3 ^ 40 * 7911912 * 2
def baseEnd_7911912 : Nat := 4062613752075553841613785

theorem tailTrace_7911912 : CollatzResearch.WordTrace tailWord_7911912 prefixEnd_7911912 4062613752075553841613785 := by
  unfold tailWord_7911912
  simp only [CollatzResearch.WordTrace]
  refine ⟨144285568856250772918220995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192380758475001030557627993 144285568856250772918220995)
  ·
    refine ⟨216428353284376159377331493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144285568856250772918220995 216428353284376159377331493)
    ·
      refine ⟨40580316240820529883249655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216428353284376159377331493 40580316240820529883249655)
      ·
        refine ⟨60870474361230794824874483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40580316240820529883249655 60870474361230794824874483)
        ·
          refine ⟨91305711541846192237311725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60870474361230794824874483 91305711541846192237311725)
          ·
            refine ⟨34239641828192322088991897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91305711541846192237311725 34239641828192322088991897)
            ·
              refine ⟨25679731371144241566743923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34239641828192322088991897 25679731371144241566743923)
              ·
                refine ⟨38519597056716362350115885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25679731371144241566743923 38519597056716362350115885)
                ·
                  refine ⟨14444848896268635881293457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38519597056716362350115885 14444848896268635881293457)
                  ·
                    refine ⟨10833636672201476910970093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14444848896268635881293457 10833636672201476910970093)
                    ·
                      refine ⟨4062613752075553841613785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10833636672201476910970093 4062613752075553841613785)
                      ·
                        rfl

theorem cell23_7911912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7911912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911912 prefixEnd_7911912 := by exact prefixLift 7911912
  have htrace : WordTrace (prefixWord ++ tailWord_7911912) baseStart_7911912 baseEnd_7911912 := by
    simpa [prefixWord, tailWord_7911912, baseEnd_7911912] using wordTrace_append hprefix tailTrace_7911912
  have hstable : (prefixWord ++ tailWord_7911912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911912).length < 2 ^ (prefixWord ++ tailWord_7911912).sum := by decide
  have hdescent : baseEnd_7911912 < baseStart_7911912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911915 : List Nat := [1, 1, 1, 1, 2, 3, 7, 7]
def baseStart_7911915 : Nat := 118140960795 + 7911915 * 2 ^ 59
def prefixEnd_7911915 : Nat := 4983230072969 + 3 ^ 40 * 7911915 * 2
def baseEnd_7911915 : Nat := 150467233056204345550973

theorem tailTrace_7911915 : CollatzResearch.WordTrace tailWord_7911915 prefixEnd_7911915 150467233056204345550973 := by
  unfold tailWord_7911915
  simp only [CollatzResearch.WordTrace]
  refine ⟨288571247131490677348801199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192380831420993784899200799 288571247131490677348801199)
  ·
    refine ⟨432856870697236016023201799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288571247131490677348801199 432856870697236016023201799)
    ·
      refine ⟨649285306045854024034802699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432856870697236016023201799 649285306045854024034802699)
      ·
        refine ⟨973927959068781036052204049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649285306045854024034802699 973927959068781036052204049)
        ·
          refine ⟨730445969301585777039153037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973927959068781036052204049 730445969301585777039153037)
          ·
            refine ⟨273917238488094666389682389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730445969301585777039153037 273917238488094666389682389)
            ·
              refine ⟨6419935277064718743508181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 273917238488094666389682389 6419935277064718743508181)
              ·
                refine ⟨150467233056204345550973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6419935277064718743508181 150467233056204345550973)
                ·
                  rfl

theorem cell23_7911915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 7].length) (baseStart_7911915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911915 prefixEnd_7911915 := by exact prefixLift 7911915
  have htrace : WordTrace (prefixWord ++ tailWord_7911915) baseStart_7911915 baseEnd_7911915 := by
    simpa [prefixWord, tailWord_7911915, baseEnd_7911915] using wordTrace_append hprefix tailTrace_7911915
  have hstable : (prefixWord ++ tailWord_7911915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911915).length < 2 ^ (prefixWord ++ tailWord_7911915).sum := by decide
  have hdescent : baseEnd_7911915 < baseStart_7911915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911929 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 1, 2, 3]
def baseStart_7911929 : Nat := 118140960795 + 7911929 * 2 ^ 59
def prefixEnd_7911929 : Nat := 4983230072969 + 3 ^ 40 * 7911929 * 2
def baseEnd_7911929 : Nat := 4062622481246680275101207

theorem tailTrace_7911929 : CollatzResearch.WordTrace tailWord_7911929 prefixEnd_7911929 4062622481246680275101207 := by
  unfold tailWord_7911929
  simp only [CollatzResearch.WordTrace]
  refine ⟨288571757753439957739810841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192381171835626638493207227 288571757753439957739810841)
  ·
    refine ⟨216428818315079968304858131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288571757753439957739810841 216428818315079968304858131)
    ·
      refine ⟨324643227472619952457287197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216428818315079968304858131 324643227472619952457287197)
      ·
        refine ⟨121741210302232482171482699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324643227472619952457287197 121741210302232482171482699)
        ·
          refine ⟨182611815453348723257224049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121741210302232482171482699 182611815453348723257224049)
          ·
            refine ⟨136958861590011542442918037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182611815453348723257224049 136958861590011542442918037)
            ·
              refine ⟨6419946637031791052011783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136958861590011542442918037 6419946637031791052011783)
              ·
                refine ⟨9629919955547686578017675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419946637031791052011783 9629919955547686578017675)
                ·
                  refine ⟨14444879933321529867026513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9629919955547686578017675 14444879933321529867026513)
                  ·
                    refine ⟨10833659949991147400269885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14444879933321529867026513 10833659949991147400269885)
                    ·
                      refine ⟨4062622481246680275101207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10833659949991147400269885 4062622481246680275101207)
                      ·
                        rfl

theorem cell23_7911929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_7911929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911929 prefixEnd_7911929 := by exact prefixLift 7911929
  have htrace : WordTrace (prefixWord ++ tailWord_7911929) baseStart_7911929 baseEnd_7911929 := by
    simpa [prefixWord, tailWord_7911929, baseEnd_7911929] using wordTrace_append hprefix tailTrace_7911929
  have hstable : (prefixWord ++ tailWord_7911929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911929).length < 2 ^ (prefixWord ++ tailWord_7911929).sum := by decide
  have hdescent : baseEnd_7911929 < baseStart_7911929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911956 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7911956 : Nat := 118140960795 + 7911956 * 2 ^ 59
def prefixEnd_7911956 : Nat := 4983230072969 + 3 ^ 40 * 7911956 * 2
def baseEnd_7911956 : Nat := 4062636345224351669463583

theorem tailTrace_7911956 : CollatzResearch.WordTrace tailWord_7911956 prefixEnd_7911956 4062636345224351669463583 := by
  unfold tailWord_7911956
  simp only [CollatzResearch.WordTrace]
  refine ⟨144286371262171070675521861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192381828349561427567362481 144286371262171070675521861)
  ·
    refine ⟨27053694611657075751660349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144286371262171070675521861 27053694611657075751660349)
    ·
      refine ⟨10145135479371403406872631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27053694611657075751660349 10145135479371403406872631)
      ·
        refine ⟨15217703219057105110308947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145135479371403406872631 15217703219057105110308947)
        ·
          refine ⟨22826554828585657665463421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15217703219057105110308947 22826554828585657665463421)
          ·
            refine ⟨8559958060719621624548783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22826554828585657665463421 8559958060719621624548783)
            ·
              refine ⟨12839937091079432436823175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559958060719621624548783 12839937091079432436823175)
              ·
                refine ⟨19259905636619148655234763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12839937091079432436823175 19259905636619148655234763)
                ·
                  refine ⟨28889858454928722982852145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19259905636619148655234763 28889858454928722982852145)
                  ·
                    refine ⟨21667393841196542237139109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28889858454928722982852145 21667393841196542237139109)
                    ·
                      refine ⟨4062636345224351669463583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21667393841196542237139109 4062636345224351669463583)
                      ·
                        rfl

theorem cell23_7911956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7911956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911956 prefixEnd_7911956 := by exact prefixLift 7911956
  have htrace : WordTrace (prefixWord ++ tailWord_7911956) baseStart_7911956 baseEnd_7911956 := by
    simpa [prefixWord, tailWord_7911956, baseEnd_7911956] using wordTrace_append hprefix tailTrace_7911956
  have hstable : (prefixWord ++ tailWord_7911956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911956).length < 2 ^ (prefixWord ++ tailWord_7911956).sum := by decide
  have hdescent : baseEnd_7911956 < baseStart_7911956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911985 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_7911985 : Nat := 118140960795 + 7911985 * 2 ^ 59
def prefixEnd_7911985 : Nat := 4983230072969 + 3 ^ 40 * 7911985 * 2
def baseEnd_7911985 : Nat := 4062651236163332056000949

theorem tailTrace_7911985 : CollatzResearch.WordTrace tailWord_7911985 prefixEnd_7911985 4062651236163332056000949 := by
  unfold tailWord_7911985
  simp only [CollatzResearch.WordTrace]
  refine ⟨288573800241237079303849409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192382533494158052869232939 288573800241237079303849409)
  ·
    refine ⟨216430350180927809477887057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288573800241237079303849409 216430350180927809477887057)
    ·
      refine ⟨162322762635695857108415293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216430350180927809477887057 162322762635695857108415293)
      ·
        refine ⟨60871035988385946415655735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162322762635695857108415293 60871035988385946415655735)
        ·
          refine ⟨91306553982578919623483603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60871035988385946415655735 91306553982578919623483603)
          ·
            refine ⟨136959830973868379435225405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91306553982578919623483603 136959830973868379435225405)
            ·
              refine ⟨51359936615200642288209527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136959830973868379435225405 51359936615200642288209527)
              ·
                refine ⟨77039904922800963432314291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51359936615200642288209527 77039904922800963432314291)
                ·
                  refine ⟨115559857384201445148471437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77039904922800963432314291 115559857384201445148471437)
                  ·
                    refine ⟨43334946519075541930676789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115559857384201445148471437 43334946519075541930676789)
                    ·
                      refine ⟨4062651236163332056000949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43334946519075541930676789 4062651236163332056000949)
                      ·
                        rfl

theorem cell23_7911985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_7911985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911985 prefixEnd_7911985 := by exact prefixLift 7911985
  have htrace : WordTrace (prefixWord ++ tailWord_7911985) baseStart_7911985 baseEnd_7911985 := by
    simpa [prefixWord, tailWord_7911985, baseEnd_7911985] using wordTrace_append hprefix tailTrace_7911985
  have hstable : (prefixWord ++ tailWord_7911985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911985).length < 2 ^ (prefixWord ++ tailWord_7911985).sum := by decide
  have hdescent : baseEnd_7911985 < baseStart_7911985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7911999 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 4, 2, 2]
def baseStart_7911999 : Nat := 118140960795 + 7911999 * 2 ^ 59
def prefixEnd_7911999 : Nat := 4983230072969 + 3 ^ 40 * 7911999 * 2
def baseEnd_7911999 : Nat := 4062658424892495001225885

theorem tailTrace_7911999 : CollatzResearch.WordTrace tailWord_7911999 prefixEnd_7911999 4062658424892495001225885 := by
  unfold tailWord_7911999
  simp only [CollatzResearch.WordTrace]
  refine ⟨288574310863186359694859051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192382873908790906463239367 288574310863186359694859051)
  ·
    refine ⟨432861466294779539542288577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288574310863186359694859051 432861466294779539542288577)
    ·
      refine ⟨324646099721084654656716433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432861466294779539542288577 324646099721084654656716433)
      ·
        refine ⟨243484574790813490992537325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324646099721084654656716433 243484574790813490992537325)
        ·
          refine ⟨91306715546555059122201497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243484574790813490992537325 91306715546555059122201497)
          ·
            refine ⟨68480036659916294341651123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91306715546555059122201497 68480036659916294341651123)
            ·
              refine ⟨102720054989874441512476685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68480036659916294341651123 102720054989874441512476685)
              ·
                refine ⟨38520020621202915567178757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102720054989874441512476685 38520020621202915567178757)
                ·
                  refine ⟨7222503866475546668846017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38520020621202915567178757 7222503866475546668846017)
                  ·
                    refine ⟨5416877899856660001634513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222503866475546668846017 5416877899856660001634513)
                    ·
                      refine ⟨4062658424892495001225885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5416877899856660001634513 4062658424892495001225885)
                      ·
                        rfl

theorem cell23_7911999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_7911999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7911999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7911999 prefixEnd_7911999 := by exact prefixLift 7911999
  have htrace : WordTrace (prefixWord ++ tailWord_7911999) baseStart_7911999 baseEnd_7911999 := by
    simpa [prefixWord, tailWord_7911999, baseEnd_7911999] using wordTrace_append hprefix tailTrace_7911999
  have hstable : (prefixWord ++ tailWord_7911999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7911999).length < 2 ^ (prefixWord ++ tailWord_7911999).sum := by decide
  have hdescent : baseEnd_7911999 < baseStart_7911999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7911999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912159 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 1, 5]
def baseStart_7912159 : Nat := 118140960795 + 7912159 * 2 ^ 59
def prefixEnd_7912159 : Nat := 4983230072969 + 3 ^ 40 * 7912159 * 2
def baseEnd_7912159 : Nat := 1354246860599071458408383

theorem tailTrace_7912159 : CollatzResearch.WordTrace tailWord_7912159 prefixEnd_7912159 1354246860599071458408383 := by
  unfold tailWord_7912159
  simp only [CollatzResearch.WordTrace]
  refine ⟨288580146542606707020683531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192386764361737804680455687 288580146542606707020683531)
  ·
    refine ⟨432870219813910060531025297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288580146542606707020683531 432870219813910060531025297)
    ·
      refine ⟨324652664860432545398268973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432870219813910060531025297 324652664860432545398268973)
      ·
        refine ⟨121744749322662204524350865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324652664860432545398268973 121744749322662204524350865)
        ·
          refine ⟨91308561991996653393263149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121744749322662204524350865 91308561991996653393263149)
          ·
            refine ⟨34240710746998745022473681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91308561991996653393263149 34240710746998745022473681)
            ·
              refine ⟨25680533060249058766855261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34240710746998745022473681 25680533060249058766855261)
              ·
                refine ⟨9630199897593397037570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25680533060249058766855261 9630199897593397037570723)
                ·
                  refine ⟨14445299846390095556356085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630199897593397037570723 14445299846390095556356085)
                  ·
                    refine ⟨1354246860599071458408383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14445299846390095556356085 1354246860599071458408383)
                    ·
                      rfl

theorem cell23_7912159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_7912159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912159 prefixEnd_7912159 := by exact prefixLift 7912159
  have htrace : WordTrace (prefixWord ++ tailWord_7912159) baseStart_7912159 baseEnd_7912159 := by
    simpa [prefixWord, tailWord_7912159, baseEnd_7912159] using wordTrace_append hprefix tailTrace_7912159
  have hstable : (prefixWord ++ tailWord_7912159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912159).length < 2 ^ (prefixWord ++ tailWord_7912159).sum := by decide
  have hdescent : baseEnd_7912159 < baseStart_7912159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912202 : List Nat := [3, 1, 2, 2, 1, 2, 1, 11]
def baseStart_7912202 : Nat := 118140960795 + 7912202 * 2 ^ 59
def prefixEnd_7912202 : Nat := 4983230072969 + 3 ^ 40 * 7912202 * 2
def baseEnd_7912202 : Nat := 150472691165383618777313

theorem tailTrace_7912202 : CollatzResearch.WordTrace tailWord_7912202 prefixEnd_7912202 150472691165383618777313 := by
  unfold tailWord_7912202
  simp only [CollatzResearch.WordTrace]
  refine ⟨72145428720362731341124715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192387809920967283576332573 72145428720362731341124715)
  ·
    refine ⟨108218143080544097011687073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72145428720362731341124715 108218143080544097011687073)
    ·
      refine ⟨81163607310408072758765305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108218143080544097011687073 81163607310408072758765305)
      ·
        refine ⟨60872705482806054569073979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81163607310408072758765305 60872705482806054569073979)
        ·
          refine ⟨91309058224209081853610969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60872705482806054569073979 91309058224209081853610969)
          ·
            refine ⟨68481793668156811390208227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91309058224209081853610969 68481793668156811390208227)
            ·
              refine ⟨102722690502235217085312341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68481793668156811390208227 102722690502235217085312341)
              ·
                refine ⟨150472691165383618777313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102722690502235217085312341 150472691165383618777313)
                ·
                  rfl

theorem cell23_7912202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_7912202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912202 prefixEnd_7912202 := by exact prefixLift 7912202
  have htrace : WordTrace (prefixWord ++ tailWord_7912202) baseStart_7912202 baseEnd_7912202 := by
    simpa [prefixWord, tailWord_7912202, baseEnd_7912202] using wordTrace_append hprefix tailTrace_7912202
  have hstable : (prefixWord ++ tailWord_7912202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912202).length < 2 ^ (prefixWord ++ tailWord_7912202).sum := by decide
  have hdescent : baseEnd_7912202 < baseStart_7912202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912210 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7912210 : Nat := 118140960795 + 7912210 * 2 ^ 59
def prefixEnd_7912210 : Nat := 4983230072969 + 3 ^ 40 * 7912210 * 2
def baseEnd_7912210 : Nat := 1354255589770197891895805

theorem tailTrace_7912210 : CollatzResearch.WordTrace tailWord_7912210 prefixEnd_7912210 1354255589770197891895805 := by
  unfold tailWord_7912210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72145501666355485682697521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192388004443614628487193389 72145501666355485682697521)
  ·
    refine ⟨54109126249766614262023141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72145501666355485682697521 54109126249766614262023141)
    ·
      refine ⟨10145461171831240174129339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54109126249766614262023141 10145461171831240174129339)
      ·
        refine ⟨15218191757746860261194009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145461171831240174129339 15218191757746860261194009)
        ·
          refine ⟨11413643818310145195895507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15218191757746860261194009 11413643818310145195895507)
          ·
            refine ⟨17120465727465217793843261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11413643818310145195895507 17120465727465217793843261)
            ·
              refine ⟨6420174647799456672691223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17120465727465217793843261 6420174647799456672691223)
              ·
                refine ⟨9630261971699185009036835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420174647799456672691223 9630261971699185009036835)
                ·
                  refine ⟨14445392957548777513555253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630261971699185009036835 14445392957548777513555253)
                  ·
                    refine ⟨1354255589770197891895805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14445392957548777513555253 1354255589770197891895805)
                    ·
                      rfl

theorem cell23_7912210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7912210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912210 prefixEnd_7912210 := by exact prefixLift 7912210
  have htrace : WordTrace (prefixWord ++ tailWord_7912210) baseStart_7912210 baseEnd_7912210 := by
    simpa [prefixWord, tailWord_7912210, baseEnd_7912210] using wordTrace_append hprefix tailTrace_7912210
  have hstable : (prefixWord ++ tailWord_7912210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912210).length < 2 ^ (prefixWord ++ tailWord_7912210).sum := by decide
  have hdescent : baseEnd_7912210 < baseStart_7912210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912229 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_7912229 : Nat := 118140960795 + 7912229 * 2 ^ 59
def prefixEnd_7912229 : Nat := 4983230072969 + 3 ^ 40 * 7912229 * 2
def baseEnd_7912229 : Nat := 4062776525443029101349827

theorem tailTrace_7912229 : CollatzResearch.WordTrace tailWord_7912229 prefixEnd_7912229 4062776525443029101349827 := by
  unfold tailWord_7912229
  simp only [CollatzResearch.WordTrace]
  refine ⟨288582699652353108975731741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192388466434902072650487827 288582699652353108975731741)
  ·
    refine ⟨108218512369632415865899403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288582699652353108975731741 108218512369632415865899403)
    ·
      refine ⟨162327768554448623798849105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108218512369632415865899403 162327768554448623798849105)
      ·
        refine ⟨121745826415836467849136829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162327768554448623798849105 121745826415836467849136829)
        ·
          refine ⟨45654684905938675443426311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121745826415836467849136829 45654684905938675443426311)
          ·
            refine ⟨68482027358908013165139467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45654684905938675443426311 68482027358908013165139467)
            ·
              refine ⟨102723041038362019747709201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68482027358908013165139467 102723041038362019747709201)
              ·
                refine ⟨77042280778771514810781901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102723041038362019747709201 77042280778771514810781901)
                ·
                  refine ⟨28890855292039318054043213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77042280778771514810781901 28890855292039318054043213)
                  ·
                    refine ⟨10834070734514744270266205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28890855292039318054043213 10834070734514744270266205)
                    ·
                      refine ⟨4062776525443029101349827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834070734514744270266205 4062776525443029101349827)
                      ·
                        rfl

theorem cell23_7912229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_7912229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912229 prefixEnd_7912229 := by exact prefixLift 7912229
  have htrace : WordTrace (prefixWord ++ tailWord_7912229) baseStart_7912229 baseEnd_7912229 := by
    simpa [prefixWord, tailWord_7912229, baseEnd_7912229] using wordTrace_append hprefix tailTrace_7912229
  have hstable : (prefixWord ++ tailWord_7912229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912229).length < 2 ^ (prefixWord ++ tailWord_7912229).sum := by decide
  have hdescent : baseEnd_7912229 < baseStart_7912229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912239 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 9, 2]
def baseStart_7912239 : Nat := 118140960795 + 7912239 * 2 ^ 59
def prefixEnd_7912239 : Nat := 4983230072969 + 3 ^ 40 * 7912239 * 2
def baseEnd_7912239 : Nat := 4062781660249574062224781

theorem tailTrace_7912239 : CollatzResearch.WordTrace tailWord_7912239 prefixEnd_7912239 4062781660249574062224781 := by
  unfold tailWord_7912239
  simp only [CollatzResearch.WordTrace]
  refine ⟨288583064382316880683595771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192388709588211253789063847 288583064382316880683595771)
  ·
    refine ⟨432874596573475321025393657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288583064382316880683595771 432874596573475321025393657)
    ·
      refine ⟨324655947430106490769045243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432874596573475321025393657 324655947430106490769045243)
      ·
        refine ⟨486983921145159736153567865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324655947430106490769045243 486983921145159736153567865)
        ·
          refine ⟨365237940858869802115175899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486983921145159736153567865 365237940858869802115175899)
          ·
            refine ⟨547856911288304703172763849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365237940858869802115175899 547856911288304703172763849)
            ·
              refine ⟨410892683466228527379572887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547856911288304703172763849 410892683466228527379572887)
              ·
                refine ⟨616339025199342791069359331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410892683466228527379572887 616339025199342791069359331)
                ·
                  refine ⟨924508537799014186604038997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616339025199342791069359331 924508537799014186604038997)
                  ·
                    refine ⟨5417042213666098749633041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 924508537799014186604038997 5417042213666098749633041)
                    ·
                      refine ⟨4062781660249574062224781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417042213666098749633041 4062781660249574062224781)
                      ·
                        rfl

theorem cell23_7912239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9, 2].length) (baseStart_7912239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912239 prefixEnd_7912239 := by exact prefixLift 7912239
  have htrace : WordTrace (prefixWord ++ tailWord_7912239) baseStart_7912239 baseEnd_7912239 := by
    simpa [prefixWord, tailWord_7912239, baseEnd_7912239] using wordTrace_append hprefix tailTrace_7912239
  have hstable : (prefixWord ++ tailWord_7912239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912239).length < 2 ^ (prefixWord ++ tailWord_7912239).sum := by decide
  have hdescent : baseEnd_7912239 < baseStart_7912239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912279 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 6]
def baseStart_7912279 : Nat := 118140960795 + 7912279 * 2 ^ 59
def prefixEnd_7912279 : Nat := 4983230072969 + 3 ^ 40 * 7912279 * 2
def baseEnd_7912279 : Nat := 1354267399825251301908199

theorem tailTrace_7912279 : CollatzResearch.WordTrace tailWord_7912279 prefixEnd_7912279 1354267399825251301908199 := by
  unfold tailWord_7912279
  simp only [CollatzResearch.WordTrace]
  refine ⟨288584523302171967515051891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192389682201447978343367927 288584523302171967515051891)
  ·
    refine ⟨432876784953257951272577837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288584523302171967515051891 432876784953257951272577837)
    ·
      refine ⟨162328794357471731727216689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432876784953257951272577837 162328794357471731727216689)
      ·
        refine ⟨121746595768103798795412517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162328794357471731727216689 121746595768103798795412517)
        ·
          refine ⟨22827486706519462274139847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121746595768103798795412517 22827486706519462274139847)
          ·
            refine ⟨34241230059779193411209771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22827486706519462274139847 34241230059779193411209771)
            ·
              refine ⟨51361845089668790116814657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34241230059779193411209771 51361845089668790116814657)
              ·
                refine ⟨38521383817251592587610993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51361845089668790116814657 38521383817251592587610993)
                ·
                  refine ⟨28891037862938694440708245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38521383817251592587610993 28891037862938694440708245)
                  ·
                    refine ⟨1354267399825251301908199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28891037862938694440708245 1354267399825251301908199)
                    ·
                      rfl

theorem cell23_7912279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_7912279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912279 prefixEnd_7912279 := by exact prefixLift 7912279
  have htrace : WordTrace (prefixWord ++ tailWord_7912279) baseStart_7912279 baseEnd_7912279 := by
    simpa [prefixWord, tailWord_7912279, baseEnd_7912279] using wordTrace_append hprefix tailTrace_7912279
  have hstable : (prefixWord ++ tailWord_7912279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912279).length < 2 ^ (prefixWord ++ tailWord_7912279).sum := by decide
  have hdescent : baseEnd_7912279 < baseStart_7912279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912289 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_7912289 : Nat := 118140960795 + 7912289 * 2 ^ 59
def prefixEnd_7912289 : Nat := 4983230072969 + 3 ^ 40 * 7912289 * 2
def baseEnd_7912289 : Nat := 4062807334282298866599551

theorem tailTrace_7912289 : CollatzResearch.WordTrace tailWord_7912289 prefixEnd_7912289 4062807334282298866599551 := by
  unfold tailWord_7912289
  simp only [CollatzResearch.WordTrace]
  refine ⟨288584888032135739222915921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192389925354757159481943947 288584888032135739222915921)
  ·
    refine ⟨216438666024101804417186941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288584888032135739222915921 216438666024101804417186941)
    ·
      refine ⟨81164499759038176656445103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216438666024101804417186941 81164499759038176656445103)
      ·
        refine ⟨121746749638557264984667655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81164499759038176656445103 121746749638557264984667655)
        ·
          refine ⟨182620124457835897477001483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121746749638557264984667655 182620124457835897477001483)
          ·
            refine ⟨273930186686753846215502225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182620124457835897477001483 273930186686753846215502225)
            ·
              refine ⟨205447640015065384661626669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273930186686753846215502225 205447640015065384661626669)
              ·
                refine ⟨77042865005649519248110001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205447640015065384661626669 77042865005649519248110001)
                ·
                  refine ⟨57782148754237139436082501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77042865005649519248110001 57782148754237139436082501)
                  ·
                    refine ⟨10834152891419463644265469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57782148754237139436082501 10834152891419463644265469)
                    ·
                      refine ⟨4062807334282298866599551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834152891419463644265469 4062807334282298866599551)
                      ·
                        rfl

theorem cell23_7912289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_7912289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912289 prefixEnd_7912289 := by exact prefixLift 7912289
  have htrace : WordTrace (prefixWord ++ tailWord_7912289) baseStart_7912289 baseEnd_7912289 := by
    simpa [prefixWord, tailWord_7912289, baseEnd_7912289] using wordTrace_append hprefix tailTrace_7912289
  have hstable : (prefixWord ++ tailWord_7912289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912289).length < 2 ^ (prefixWord ++ tailWord_7912289).sum := by decide
  have hdescent : baseEnd_7912289 < baseStart_7912289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912299 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_7912299 : Nat := 118140960795 + 7912299 * 2 ^ 59
def prefixEnd_7912299 : Nat := 4983230072969 + 3 ^ 40 * 7912299 * 2
def baseEnd_7912299 : Nat := 4062812469088843827474505

theorem tailTrace_7912299 : CollatzResearch.WordTrace tailWord_7912299 prefixEnd_7912299 4062812469088843827474505 := by
  unfold tailWord_7912299
  simp only [CollatzResearch.WordTrace]
  refine ⟨288585252762099510930779951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192390168508066340620519967 288585252762099510930779951)
  ·
    refine ⟨432877879143149266396169927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288585252762099510930779951 432877879143149266396169927)
    ·
      refine ⟨649316818714723899594254891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432877879143149266396169927 649316818714723899594254891)
      ·
        refine ⟨973975228072085849391382337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649316818714723899594254891 973975228072085849391382337)
        ·
          refine ⟨730481421054064387043536753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973975228072085849391382337 730481421054064387043536753)
          ·
            refine ⟨547861065790548290282652565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730481421054064387043536753 547861065790548290282652565)
            ·
              refine ⟨25680987458931951106999339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 547861065790548290282652565 25680987458931951106999339)
              ·
                refine ⟨38521481188397926660499009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25680987458931951106999339 38521481188397926660499009)
                ·
                  refine ⟨28891110891298444995374257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38521481188397926660499009 28891110891298444995374257)
                  ·
                    refine ⟨21668333168473833746530693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28891110891298444995374257 21668333168473833746530693)
                    ·
                      refine ⟨4062812469088843827474505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21668333168473833746530693 4062812469088843827474505)
                      ·
                        rfl

theorem cell23_7912299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_7912299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912299 prefixEnd_7912299 := by exact prefixLift 7912299
  have htrace : WordTrace (prefixWord ++ tailWord_7912299) baseStart_7912299 baseEnd_7912299 := by
    simpa [prefixWord, tailWord_7912299, baseEnd_7912299] using wordTrace_append hprefix tailTrace_7912299
  have hstable : (prefixWord ++ tailWord_7912299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912299).length < 2 ^ (prefixWord ++ tailWord_7912299).sum := by decide
  have hdescent : baseEnd_7912299 < baseStart_7912299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912303 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 2, 2, 2]
def baseStart_7912303 : Nat := 118140960795 + 7912303 * 2 ^ 59
def prefixEnd_7912303 : Nat := 4983230072969 + 3 ^ 40 * 7912303 * 2
def baseEnd_7912303 : Nat := 4062814523011461811824487

theorem tailTrace_7912303 : CollatzResearch.WordTrace tailWord_7912303 prefixEnd_7912303 4062814523011461811824487 := by
  unfold tailWord_7912303
  simp only [CollatzResearch.WordTrace]
  refine ⟨288585398654085019613925563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192390265769390013075950375 288585398654085019613925563)
  ·
    refine ⟨432878097981127529420888345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288585398654085019613925563 432878097981127529420888345)
    ·
      refine ⟨324658573485845647065666259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432878097981127529420888345 324658573485845647065666259)
      ·
        refine ⟨486987860228768470598499389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324658573485845647065666259 486987860228768470598499389)
        ·
          refine ⟨182620447585788176474437271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486987860228768470598499389 182620447585788176474437271)
          ·
            refine ⟨273930671378682264711655907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182620447585788176474437271 273930671378682264711655907)
            ·
              refine ⟨410896007068023397067483861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273930671378682264711655907 410896007068023397067483861)
              ·
                refine ⟨9630375165656798368769153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410896007068023397067483861 9630375165656798368769153)
                ·
                  refine ⟨7222781374242598776576865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630375165656798368769153 7222781374242598776576865)
                  ·
                    refine ⟨5417086030681949082432649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222781374242598776576865 5417086030681949082432649)
                    ·
                      refine ⟨4062814523011461811824487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417086030681949082432649 4062814523011461811824487)
                      ·
                        rfl

theorem cell23_7912303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 2, 2].length) (baseStart_7912303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912303 prefixEnd_7912303 := by exact prefixLift 7912303
  have htrace : WordTrace (prefixWord ++ tailWord_7912303) baseStart_7912303 baseEnd_7912303 := by
    simpa [prefixWord, tailWord_7912303, baseEnd_7912303] using wordTrace_append hprefix tailTrace_7912303
  have hstable : (prefixWord ++ tailWord_7912303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912303).length < 2 ^ (prefixWord ++ tailWord_7912303).sum := by decide
  have hdescent : baseEnd_7912303 < baseStart_7912303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912319 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_7912319 : Nat := 118140960795 + 7912319 * 2 ^ 59
def prefixEnd_7912319 : Nat := 4983230072969 + 3 ^ 40 * 7912319 * 2
def baseEnd_7912319 : Nat := 4062822738701933749224413

theorem tailTrace_7912319 : CollatzResearch.WordTrace tailWord_7912319 prefixEnd_7912319 4062822738701933749224413 := by
  unfold tailWord_7912319
  simp only [CollatzResearch.WordTrace]
  refine ⟨288585982222027054346508011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192390654814684702897672007 288585982222027054346508011)
  ·
    refine ⟨432878973333040581519762017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288585982222027054346508011 432878973333040581519762017)
    ·
      refine ⟨324659229999780436139821513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432878973333040581519762017 324659229999780436139821513)
      ·
        refine ⟨243494422499835327104866135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324659229999780436139821513 243494422499835327104866135)
        ·
          refine ⟨365241633749752990657299203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243494422499835327104866135 365241633749752990657299203)
          ·
            refine ⟨547862450624629485985948805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365241633749752990657299203 547862450624629485985948805)
            ·
              refine ⟨102724209492118028622365401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547862450624629485985948805 102724209492118028622365401)
              ·
                refine ⟨77043157119088521466774051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102724209492118028622365401 77043157119088521466774051)
                ·
                  refine ⟨115564735678632782200161077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77043157119088521466774051 115564735678632782200161077)
                  ·
                    refine ⟨10834193969871823331265101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115564735678632782200161077 10834193969871823331265101)
                    ·
                      refine ⟨4062822738701933749224413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834193969871823331265101 4062822738701933749224413)
                      ·
                        rfl

theorem cell23_7912319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_7912319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912319 prefixEnd_7912319 := by exact prefixLift 7912319
  have htrace : WordTrace (prefixWord ++ tailWord_7912319) baseStart_7912319 baseEnd_7912319 := by
    simpa [prefixWord, tailWord_7912319, baseEnd_7912319] using wordTrace_append hprefix tailTrace_7912319
  have hstable : (prefixWord ++ tailWord_7912319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912319).length < 2 ^ (prefixWord ++ tailWord_7912319).sum := by decide
  have hdescent : baseEnd_7912319 < baseStart_7912319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912343 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 5]
def baseStart_7912343 : Nat := 118140960795 + 7912343 * 2 ^ 59
def prefixEnd_7912343 : Nat := 4983230072969 + 3 ^ 40 * 7912343 * 2
def baseEnd_7912343 : Nat := 451426118026404628369367

theorem tailTrace_7912343 : CollatzResearch.WordTrace tailWord_7912343 prefixEnd_7912343 451426118026404628369367 := by
  unfold tailWord_7912343
  simp only [CollatzResearch.WordTrace]
  refine ⟨288586857573940106445381683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192391238382626737630254455 288586857573940106445381683)
  ·
    refine ⟨432880286360910159668072525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288586857573940106445381683 432880286360910159668072525)
    ·
      refine ⟨162330107385341309875527197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432880286360910159668072525 162330107385341309875527197)
      ·
        refine ⟨60873790269502991203322699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162330107385341309875527197 60873790269502991203322699)
        ·
          refine ⟨91310685404254486804984049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60873790269502991203322699 91310685404254486804984049)
          ·
            refine ⟨68483014053190865103738037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91310685404254486804984049 68483014053190865103738037)
            ·
              refine ⟨6420282567486643603475441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68483014053190865103738037 6420282567486643603475441)
              ·
                refine ⟨4815211925614982702606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6420282567486643603475441 4815211925614982702606581)
                ·
                  refine ⟨451426118026404628369367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815211925614982702606581 451426118026404628369367)
                  ·
                    rfl

theorem cell23_7912343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 5].length) (baseStart_7912343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912343 prefixEnd_7912343 := by exact prefixLift 7912343
  have htrace : WordTrace (prefixWord ++ tailWord_7912343) baseStart_7912343 baseEnd_7912343 := by
    simpa [prefixWord, tailWord_7912343, baseEnd_7912343] using wordTrace_append hprefix tailTrace_7912343
  have hstable : (prefixWord ++ tailWord_7912343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912343).length < 2 ^ (prefixWord ++ tailWord_7912343).sum := by decide
  have hdescent : baseEnd_7912343 < baseStart_7912343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912354 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7912354 : Nat := 118140960795 + 7912354 * 2 ^ 59
def prefixEnd_7912354 : Nat := 4983230072969 + 3 ^ 40 * 7912354 * 2
def baseEnd_7912354 : Nat := 4062840710524841112286753

theorem tailTrace_7912354 : CollatzResearch.WordTrace tailWord_7912354 prefixEnd_7912354 4062840710524841112286753 := by
  unfold tailWord_7912354
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146814694225063831008029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192391505851266836882688077 72146814694225063831008029)
  ·
    refine ⟨27055055510334398936628011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72146814694225063831008029 27055055510334398936628011)
    ·
      refine ⟨40582583265501598404942017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27055055510334398936628011 40582583265501598404942017)
      ·
        refine ⟨30436937449126198803706513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40582583265501598404942017 30436937449126198803706513)
        ·
          refine ⟨22827703086844649102779885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30436937449126198803706513 22827703086844649102779885)
          ·
            refine ⟨8560388657566743413542457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22827703086844649102779885 8560388657566743413542457)
            ·
              refine ⟨6420291493175057560156843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560388657566743413542457 6420291493175057560156843)
              ·
                refine ⟨9630437239762586340235265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420291493175057560156843 9630437239762586340235265)
                ·
                  refine ⟨7222827929821939755176449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630437239762586340235265 7222827929821939755176449)
                  ·
                    refine ⟨5417120947366454816382337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222827929821939755176449 5417120947366454816382337)
                    ·
                      refine ⟨4062840710524841112286753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417120947366454816382337 4062840710524841112286753)
                      ·
                        rfl

theorem cell23_7912354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7912354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912354 prefixEnd_7912354 := by exact prefixLift 7912354
  have htrace : WordTrace (prefixWord ++ tailWord_7912354) baseStart_7912354 baseEnd_7912354 := by
    simpa [prefixWord, tailWord_7912354, baseEnd_7912354] using wordTrace_append hprefix tailTrace_7912354
  have hstable : (prefixWord ++ tailWord_7912354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912354).length < 2 ^ (prefixWord ++ tailWord_7912354).sum := by decide
  have hdescent : baseEnd_7912354 < baseStart_7912354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912376 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_7912376 : Nat := 118140960795 + 7912376 * 2 ^ 59
def prefixEnd_7912376 : Nat := 4983230072969 + 3 ^ 40 * 7912376 * 2
def baseEnd_7912376 : Nat := 4062852007099240026211651

theorem tailTrace_7912376 : CollatzResearch.WordTrace tailWord_7912376 prefixEnd_7912376 4062852007099240026211651 := by
  unfold tailWord_7912376
  simp only [CollatzResearch.WordTrace]
  refine ⟨144294030591410276540666491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192392040788547035387555321 144294030591410276540666491)
  ·
    refine ⟨216441045887115414810999737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144294030591410276540666491 216441045887115414810999737)
    ·
      refine ⟨162330784415336561108249803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216441045887115414810999737 162330784415336561108249803)
      ·
        refine ⟨243496176623004841662374705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162330784415336561108249803 243496176623004841662374705)
        ·
          refine ⟨182622132467253631246781029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243496176623004841662374705 182622132467253631246781029)
          ·
            refine ⟨34241649837610055858771443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182622132467253631246781029 34241649837610055858771443)
            ·
              refine ⟨51362474756415083788157165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34241649837610055858771443 51362474756415083788157165)
              ·
                refine ⟨19260928033655656420558937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51362474756415083788157165 19260928033655656420558937)
                ·
                  refine ⟨14445696025241742315419203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19260928033655656420558937 14445696025241742315419203)
                  ·
                    refine ⟨21668544037862613473128805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14445696025241742315419203 21668544037862613473128805)
                    ·
                      refine ⟨4062852007099240026211651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21668544037862613473128805 4062852007099240026211651)
                      ·
                        rfl

theorem cell23_7912376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_7912376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912376 prefixEnd_7912376 := by exact prefixLift 7912376
  have htrace : WordTrace (prefixWord ++ tailWord_7912376) baseStart_7912376 baseEnd_7912376 := by
    simpa [prefixWord, tailWord_7912376, baseEnd_7912376] using wordTrace_append hprefix tailTrace_7912376
  have hstable : (prefixWord ++ tailWord_7912376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912376).length < 2 ^ (prefixWord ++ tailWord_7912376).sum := by decide
  have hdescent : baseEnd_7912376 < baseStart_7912376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912389 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_7912389 : Nat := 118140960795 + 7912389 * 2 ^ 59
def prefixEnd_7912389 : Nat := 4983230072969 + 3 ^ 40 * 7912389 * 2
def baseEnd_7912389 : Nat := 4062858682347748475349091

theorem tailTrace_7912389 : CollatzResearch.WordTrace tailWord_7912389 prefixEnd_7912389 4062858682347748475349091 := by
  unfold tailWord_7912389
  simp only [CollatzResearch.WordTrace]
  refine ⟨288588535331773456301556221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192392356887848970867704147 288588535331773456301556221)
  ·
    refine ⟨108220700749415046113083583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288588535331773456301556221 108220700749415046113083583)
    ·
      refine ⟨162331051124122569169625375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108220700749415046113083583 162331051124122569169625375)
      ·
        refine ⟨243496576686183853754438063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162331051124122569169625375 243496576686183853754438063)
        ·
          refine ⟨365244865029275780631657095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243496576686183853754438063 365244865029275780631657095)
          ·
            refine ⟨547867297543913670947485643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365244865029275780631657095 547867297543913670947485643)
            ·
              refine ⟨821800946315870506421228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547867297543913670947485643 821800946315870506421228465)
              ·
                refine ⟨616350709736902879815921349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821800946315870506421228465 616350709736902879815921349)
                ·
                  refine ⟨115565758075669289965485253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616350709736902879815921349 115565758075669289965485253)
                  ·
                    refine ⟨21668579639187991868528485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115565758075669289965485253 21668579639187991868528485)
                    ·
                      refine ⟨4062858682347748475349091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21668579639187991868528485 4062858682347748475349091)
                      ·
                        rfl

theorem cell23_7912389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_7912389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912389 prefixEnd_7912389 := by exact prefixLift 7912389
  have htrace : WordTrace (prefixWord ++ tailWord_7912389) baseStart_7912389 baseEnd_7912389 := by
    simpa [prefixWord, tailWord_7912389, baseEnd_7912389] using wordTrace_append hprefix tailTrace_7912389
  have hstable : (prefixWord ++ tailWord_7912389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912389).length < 2 ^ (prefixWord ++ tailWord_7912389).sum := by decide
  have hdescent : baseEnd_7912389 < baseStart_7912389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912450 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7912450 : Nat := 118140960795 + 7912450 * 2 ^ 59
def prefixEnd_7912450 : Nat := 4983230072969 + 3 ^ 40 * 7912450 * 2
def baseEnd_7912450 : Nat := 451432222740852526298479

theorem tailTrace_7912450 : CollatzResearch.WordTrace tailWord_7912450 prefixEnd_7912450 451432222740852526298479 := by
  unfold tailWord_7912450
  simp only [CollatzResearch.WordTrace]
  refine ⟨72147690046138115929881701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192393840123034975813017869 72147690046138115929881701)
  ·
    refine ⟨13527691883650896736852819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72147690046138115929881701 13527691883650896736852819)
    ·
      refine ⟨20291537825476345105279229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13527691883650896736852819 20291537825476345105279229)
      ·
        refine ⟨7609326684553629414479711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20291537825476345105279229 7609326684553629414479711)
        ·
          refine ⟨11413990026830444121719567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609326684553629414479711 11413990026830444121719567)
          ·
            refine ⟨17120985040245666182579351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11413990026830444121719567 17120985040245666182579351)
            ·
              refine ⟨25681477560368499273869027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17120985040245666182579351 25681477560368499273869027)
              ·
                refine ⟨38522216340552748910803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25681477560368499273869027 38522216340552748910803541)
                ·
                  refine ⟨451432222740852526298479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38522216340552748910803541 451432222740852526298479)
                  ·
                    rfl

theorem cell23_7912450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7912450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912450 prefixEnd_7912450 := by exact prefixLift 7912450
  have htrace : WordTrace (prefixWord ++ tailWord_7912450) baseStart_7912450 baseEnd_7912450 := by
    simpa [prefixWord, tailWord_7912450, baseEnd_7912450] using wordTrace_append hprefix tailTrace_7912450
  have hstable : (prefixWord ++ tailWord_7912450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912450).length < 2 ^ (prefixWord ++ tailWord_7912450).sum := by decide
  have hdescent : baseEnd_7912450 < baseStart_7912450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912453 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_7912453 : Nat := 118140960795 + 7912453 * 2 ^ 59
def prefixEnd_7912453 : Nat := 4983230072969 + 3 ^ 40 * 7912453 * 2
def baseEnd_7912453 : Nat := 4062891545109636224948797

theorem tailTrace_7912453 : CollatzResearch.WordTrace tailWord_7912453 prefixEnd_7912453 4062891545109636224948797 := by
  unfold tailWord_7912453
  simp only [CollatzResearch.WordTrace]
  refine ⟨288590869603541595231886013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192393913069027730154590675 288590869603541595231886013)
  ·
    refine ⟨108221576101328098211957255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288590869603541595231886013 108221576101328098211957255)
    ·
      refine ⟨162332364151992147317935883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108221576101328098211957255 162332364151992147317935883)
      ·
        refine ⟨243498546227988220976903825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162332364151992147317935883 243498546227988220976903825)
        ·
          refine ⟨182623909670991165732677869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243498546227988220976903825 182623909670991165732677869)
          ·
            refine ⟨68483966126621687149754201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182623909670991165732677869 68483966126621687149754201)
            ·
              refine ⟨51362974594966265362315651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68483966126621687149754201 51362974594966265362315651)
              ·
                refine ⟨77044461892449398043473477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51362974594966265362315651 77044461892449398043473477)
                ·
                  refine ⟨14445836604834262133151277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77044461892449398043473477 14445836604834262133151277)
                  ·
                    refine ⟨5417188726812848299931729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14445836604834262133151277 5417188726812848299931729)
                    ·
                      refine ⟨4062891545109636224948797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417188726812848299931729 4062891545109636224948797)
                      ·
                        rfl

theorem cell23_7912453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_7912453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912453 prefixEnd_7912453 := by exact prefixLift 7912453
  have htrace : WordTrace (prefixWord ++ tailWord_7912453) baseStart_7912453 baseEnd_7912453 := by
    simpa [prefixWord, tailWord_7912453, baseEnd_7912453] using wordTrace_append hprefix tailTrace_7912453
  have hstable : (prefixWord ++ tailWord_7912453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912453).length < 2 ^ (prefixWord ++ tailWord_7912453).sum := by decide
  have hdescent : baseEnd_7912453 < baseStart_7912453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912460 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_7912460 : Nat := 118140960795 + 7912460 * 2 ^ 59
def prefixEnd_7912460 : Nat := 4983230072969 + 3 ^ 40 * 7912460 * 2
def baseEnd_7912460 : Nat := 4062895139474217697561265

theorem tailTrace_7912460 : CollatzResearch.WordTrace tailWord_7912460 prefixEnd_7912460 4062895139474217697561265 := by
  unfold tailWord_7912460
  simp only [CollatzResearch.WordTrace]
  refine ⟨144295562457258117713695417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192394083276344156951593889 144295562457258117713695417)
  ·
    refine ⟨108221671842943588285271563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144295562457258117713695417 108221671842943588285271563)
    ·
      refine ⟨162332507764415382427907345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108221671842943588285271563 162332507764415382427907345)
      ·
        refine ⟨121749380823311536820930509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162332507764415382427907345 121749380823311536820930509)
        ·
          refine ⟨45656017808741826307848941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121749380823311536820930509 45656017808741826307848941)
          ·
            refine ⟨17121006678278184865443353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45656017808741826307848941 17121006678278184865443353)
            ·
              refine ⟨12840755008708638649082515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17121006678278184865443353 12840755008708638649082515)
              ·
                refine ⟨19261132513062957973623773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12840755008708638649082515 19261132513062957973623773)
                ·
                  refine ⟨7222924692398609240108915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19261132513062957973623773 7222924692398609240108915)
                  ·
                    refine ⟨10834387038597913860163373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7222924692398609240108915 10834387038597913860163373)
                    ·
                      refine ⟨4062895139474217697561265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834387038597913860163373 4062895139474217697561265)
                      ·
                        rfl

theorem cell23_7912460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_7912460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912460 prefixEnd_7912460 := by exact prefixLift 7912460
  have htrace : WordTrace (prefixWord ++ tailWord_7912460) baseStart_7912460 baseEnd_7912460 := by
    simpa [prefixWord, tailWord_7912460, baseEnd_7912460] using wordTrace_append hprefix tailTrace_7912460
  have hstable : (prefixWord ++ tailWord_7912460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912460).length < 2 ^ (prefixWord ++ tailWord_7912460).sum := by decide
  have hdescent : baseEnd_7912460 < baseStart_7912460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912483 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 4]
def baseStart_7912483 : Nat := 118140960795 + 7912483 * 2 ^ 59
def prefixEnd_7912483 : Nat := 4983230072969 + 3 ^ 40 * 7912483 * 2
def baseEnd_7912483 : Nat := 4062906949529271107573659

theorem tailTrace_7912483 : CollatzResearch.WordTrace tailWord_7912483 prefixEnd_7912483 4062906949529271107573659 := by
  unfold tailWord_7912483
  simp only [CollatzResearch.WordTrace]
  refine ⟨288591963793432910355478103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192394642528955273570318735 288591963793432910355478103)
  ·
    refine ⟨432887945690149365533217155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288591963793432910355478103 432887945690149365533217155)
    ·
      refine ⟨649331918535224048299825733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432887945690149365533217155 649331918535224048299825733)
      ·
        refine ⟨121749734725354509056217325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649331918535224048299825733 121749734725354509056217325)
        ·
          refine ⟨45656150522007940896081497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121749734725354509056217325 45656150522007940896081497)
          ·
            refine ⟨34242112891505955672061123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45656150522007940896081497 34242112891505955672061123)
            ·
              refine ⟨51363169337258933508091685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34242112891505955672061123 51363169337258933508091685)
              ·
                refine ⟨9630594250736050032767191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51363169337258933508091685 9630594250736050032767191)
                ·
                  refine ⟨14445891376104075049150787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630594250736050032767191 14445891376104075049150787)
                  ·
                    refine ⟨21668837064156112573726181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14445891376104075049150787 21668837064156112573726181)
                    ·
                      refine ⟨4062906949529271107573659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21668837064156112573726181 4062906949529271107573659)
                      ·
                        rfl

theorem cell23_7912483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_7912483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912483 prefixEnd_7912483 := by exact prefixLift 7912483
  have htrace : WordTrace (prefixWord ++ tailWord_7912483) baseStart_7912483 baseEnd_7912483 := by
    simpa [prefixWord, tailWord_7912483, baseEnd_7912483] using wordTrace_append hprefix tailTrace_7912483
  have hstable : (prefixWord ++ tailWord_7912483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912483).length < 2 ^ (prefixWord ++ tailWord_7912483).sum := by decide
  have hdescent : baseEnd_7912483 < baseStart_7912483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912496 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_7912496 : Nat := 118140960795 + 7912496 * 2 ^ 59
def prefixEnd_7912496 : Nat := 4983230072969 + 3 ^ 40 * 7912496 * 2
def baseEnd_7912496 : Nat := 4062913624777779556711099

theorem tailTrace_7912496 : CollatzResearch.WordTrace tailWord_7912496 prefixEnd_7912496 4062913624777779556711099 := by
  unfold tailWord_7912496
  simp only [CollatzResearch.WordTrace]
  refine ⟨144296218971192906787850671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192394958628257209050467561 144296218971192906787850671)
  ·
    refine ⟨216444328456789360181776007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144296218971192906787850671 216444328456789360181776007)
    ·
      refine ⟨324666492685184040272664011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216444328456789360181776007 324666492685184040272664011)
      ·
        refine ⟨486999739027776060408996017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324666492685184040272664011 486999739027776060408996017)
        ·
          refine ⟨365249804270832045306747013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486999739027776060408996017 365249804270832045306747013)
          ·
            refine ⟨68484338300781008495015065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365249804270832045306747013 68484338300781008495015065)
            ·
              refine ⟨51363253725585756371261299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68484338300781008495015065 51363253725585756371261299)
              ·
                refine ⟨77044880588378634556891949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51363253725585756371261299 77044880588378634556891949)
                ·
                  refine ⟨28891830220641987958834481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77044880588378634556891949 28891830220641987958834481)
                  ·
                    refine ⟨21668872665481490969125861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28891830220641987958834481 21668872665481490969125861)
                    ·
                      refine ⟨4062913624777779556711099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21668872665481490969125861 4062913624777779556711099)
                      ·
                        rfl

theorem cell23_7912496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_7912496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912496 prefixEnd_7912496 := by exact prefixLift 7912496
  have htrace : WordTrace (prefixWord ++ tailWord_7912496) baseStart_7912496 baseEnd_7912496 := by
    simpa [prefixWord, tailWord_7912496, baseEnd_7912496] using wordTrace_append hprefix tailTrace_7912496
  have hstable : (prefixWord ++ tailWord_7912496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912496).length < 2 ^ (prefixWord ++ tailWord_7912496).sum := by decide
  have hdescent : baseEnd_7912496 < baseStart_7912496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912510 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7912510 : Nat := 118140960795 + 7912510 * 2 ^ 59
def prefixEnd_7912510 : Nat := 4983230072969 + 3 ^ 40 * 7912510 * 2
def baseEnd_7912510 : Nat := 1354306937835647500645345

theorem tailTrace_7912510 : CollatzResearch.WordTrace tailWord_7912510 prefixEnd_7912510 1354306937835647500645345 := by
  unfold tailWord_7912510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074118570541886745838873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192395299042890062644473989 36074118570541886745838873)
  ·
    refine ⟨27055588927906415059379155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074118570541886745838873 27055588927906415059379155)
    ·
      refine ⟨40583383391859622589068733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27055588927906415059379155 40583383391859622589068733)
      ·
        refine ⟨15218768771947358470900775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40583383391859622589068733 15218768771947358470900775)
        ·
          refine ⟨22828153157921037706351163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218768771947358470900775 22828153157921037706351163)
          ·
            refine ⟨34242229736881556559526745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22828153157921037706351163 34242229736881556559526745)
            ·
              refine ⟨25681672302661167419645059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34242229736881556559526745 25681672302661167419645059)
              ·
                refine ⟨38522508453991751129467589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25681672302661167419645059 38522508453991751129467589)
                ·
                  refine ⟨7222970335123453336775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38522508453991751129467589 7222970335123453336775173)
                  ·
                    refine ⟨1354306937835647500645345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222970335123453336775173 1354306937835647500645345)
                    ·
                      rfl

theorem cell23_7912510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7912510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912510 prefixEnd_7912510 := by exact prefixLift 7912510
  have htrace : WordTrace (prefixWord ++ tailWord_7912510) baseStart_7912510 baseEnd_7912510 := by
    simpa [prefixWord, tailWord_7912510, baseEnd_7912510] using wordTrace_append hprefix tailTrace_7912510
  have hstable : (prefixWord ++ tailWord_7912510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912510).length < 2 ^ (prefixWord ++ tailWord_7912510).sum := by decide
  have hdescent : baseEnd_7912510 < baseStart_7912510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912517 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_7912517 : Nat := 118140960795 + 7912517 * 2 ^ 59
def prefixEnd_7912517 : Nat := 4983230072969 + 3 ^ 40 * 7912517 * 2
def baseEnd_7912517 : Nat := 4062924407871523974548503

theorem tailTrace_7912517 : CollatzResearch.WordTrace tailWord_7912517 prefixEnd_7912517 4062924407871523974548503 := by
  unfold tailWord_7912517
  simp only [CollatzResearch.WordTrace]
  refine ⟨288593203875309734162215805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192395469250206489441477203 288593203875309734162215805)
  ·
    refine ⟨108222451453241150310830927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288593203875309734162215805 108222451453241150310830927)
    ·
      refine ⟨162333677179861725466246391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108222451453241150310830927 162333677179861725466246391)
      ·
        refine ⟨243500515769792588199369587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162333677179861725466246391 243500515769792588199369587)
        ·
          refine ⟨365250773654688882299054381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243500515769792588199369587 365250773654688882299054381)
          ·
            refine ⟨136969040120508330862145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365250773654688882299054381 136969040120508330862145393)
            ·
              refine ⟨102726780090381248146609045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136969040120508330862145393 102726780090381248146609045)
              ·
                refine ⟨4815317816736621006872299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102726780090381248146609045 4815317816736621006872299)
                ·
                  refine ⟨7222976725104931510308449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815317816736621006872299 7222976725104931510308449)
                  ·
                    refine ⟨5417232543828698632731337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7222976725104931510308449 5417232543828698632731337)
                    ·
                      refine ⟨4062924407871523974548503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5417232543828698632731337 4062924407871523974548503)
                      ·
                        rfl

theorem cell23_7912517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_7912517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912517 prefixEnd_7912517 := by exact prefixLift 7912517
  have htrace : WordTrace (prefixWord ++ tailWord_7912517) baseStart_7912517 baseEnd_7912517 := by
    simpa [prefixWord, tailWord_7912517, baseEnd_7912517] using wordTrace_append hprefix tailTrace_7912517
  have hstable : (prefixWord ++ tailWord_7912517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912517).length < 2 ^ (prefixWord ++ tailWord_7912517).sum := by decide
  have hdescent : baseEnd_7912517 < baseStart_7912517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912526 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7912526 : Nat := 118140960795 + 7912526 * 2 ^ 59
def prefixEnd_7912526 : Nat := 4983230072969 + 3 ^ 40 * 7912526 * 2
def baseEnd_7912526 : Nat := 4062929029197414439335961

theorem tailTrace_7912526 : CollatzResearch.WordTrace tailWord_7912526 prefixEnd_7912526 4062929029197414439335961 := by
  unfold tailWord_7912526
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074191516534641087411679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192395688088184752466195621 36074191516534641087411679)
  ·
    refine ⟨54111287274801961631117519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36074191516534641087411679 54111287274801961631117519)
    ·
      refine ⟨81166930912202942446676279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54111287274801961631117519 81166930912202942446676279)
      ·
        refine ⟨121750396368304413670014419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81166930912202942446676279 121750396368304413670014419)
        ·
          refine ⟨182625594552456620505021629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121750396368304413670014419 182625594552456620505021629)
          ·
            refine ⟨68484597957171232689383111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182625594552456620505021629 68484597957171232689383111)
            ·
              refine ⟨102726896935756849034074667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68484597957171232689383111 102726896935756849034074667)
              ·
                refine ⟨154090345403635273551112001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102726896935756849034074667 154090345403635273551112001)
                ·
                  refine ⟨115567759052726455163334001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154090345403635273551112001 115567759052726455163334001)
                  ·
                    refine ⟨86675819289544841372500501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115567759052726455163334001 86675819289544841372500501)
                    ·
                      refine ⟨4062929029197414439335961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86675819289544841372500501 4062929029197414439335961)
                      ·
                        rfl

theorem cell23_7912526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7912526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912526 prefixEnd_7912526 := by exact prefixLift 7912526
  have htrace : WordTrace (prefixWord ++ tailWord_7912526) baseStart_7912526 baseEnd_7912526 := by
    simpa [prefixWord, tailWord_7912526, baseEnd_7912526] using wordTrace_append hprefix tailTrace_7912526
  have hstable : (prefixWord ++ tailWord_7912526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912526).length < 2 ^ (prefixWord ++ tailWord_7912526).sum := by decide
  have hdescent : baseEnd_7912526 < baseStart_7912526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912533 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7912533 : Nat := 118140960795 + 7912533 * 2 ^ 59
def prefixEnd_7912533 : Nat := 4983230072969 + 3 ^ 40 * 7912533 * 2
def baseEnd_7912533 : Nat := 4062932623561995911948429

theorem tailTrace_7912533 : CollatzResearch.WordTrace tailWord_7912533 prefixEnd_7912533 4062932623561995911948429 := by
  unfold tailWord_7912533
  simp only [CollatzResearch.WordTrace]
  refine ⟨288593787443251768894798253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192395858295501179263198835 288593787443251768894798253)
  ·
    refine ⟨108222670291219413335549345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288593787443251768894798253 108222670291219413335549345)
    ·
      refine ⟨81167002718414560001662009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108222670291219413335549345 81167002718414560001662009)
      ·
        refine ⟨60875252038810920001246507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81167002718414560001662009 60875252038810920001246507)
        ·
          refine ⟨91312878058216380001869761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60875252038810920001246507 91312878058216380001869761)
          ·
            refine ⟨68484658543662285001402321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91312878058216380001869761 68484658543662285001402321)
            ·
              refine ⟨51363493907746713751051741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68484658543662285001402321 51363493907746713751051741)
              ·
                refine ⟨19261310215405017656644403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51363493907746713751051741 19261310215405017656644403)
                ·
                  refine ⟨28891965323107526484966605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19261310215405017656644403 28891965323107526484966605)
                  ·
                    refine ⟨10834486996165322431862477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28891965323107526484966605 10834486996165322431862477)
                    ·
                      refine ⟨4062932623561995911948429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834486996165322431862477 4062932623561995911948429)
                      ·
                        rfl

theorem cell23_7912533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7912533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912533 prefixEnd_7912533 := by exact prefixLift 7912533
  have htrace : WordTrace (prefixWord ++ tailWord_7912533) baseStart_7912533 baseEnd_7912533 := by
    simpa [prefixWord, tailWord_7912533, baseEnd_7912533] using wordTrace_append hprefix tailTrace_7912533
  have hstable : (prefixWord ++ tailWord_7912533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912533).length < 2 ^ (prefixWord ++ tailWord_7912533).sum := by decide
  have hdescent : baseEnd_7912533 < baseStart_7912533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912574 : List Nat := [4, 2, 4, 1, 1, 2, 1, 8]
def baseStart_7912574 : Nat := 118140960795 + 7912574 * 2 ^ 59
def prefixEnd_7912574 : Nat := 4983230072969 + 3 ^ 40 * 7912574 * 2
def baseEnd_7912574 : Nat := 150479765787734453760583

theorem tailTrace_7912574 : CollatzResearch.WordTrace tailWord_7912574 prefixEnd_7912574 150479765787734453760583 := by
  unfold tailWord_7912574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074410354512904112130097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192396855224068821931360517 36074410354512904112130097)
  ·
    refine ⟨27055807765884678084097573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074410354512904112130097 27055807765884678084097573)
    ·
      refine ⟨5072963956103377140768295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27055807765884678084097573 5072963956103377140768295)
      ·
        refine ⟨7609445934155065711152443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072963956103377140768295 7609445934155065711152443)
        ·
          refine ⟨11414168901232598566728665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609445934155065711152443 11414168901232598566728665)
          ·
            refine ⟨8560626675924448925046499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11414168901232598566728665 8560626675924448925046499)
            ·
              refine ⟨12840940013886673387569749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560626675924448925046499 12840940013886673387569749)
              ·
                refine ⟨150479765787734453760583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12840940013886673387569749 150479765787734453760583)
                ·
                  rfl

theorem cell23_7912574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_7912574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912574 prefixEnd_7912574 := by exact prefixLift 7912574
  have htrace : WordTrace (prefixWord ++ tailWord_7912574) baseStart_7912574 baseEnd_7912574 := by
    simpa [prefixWord, tailWord_7912574, baseEnd_7912574] using wordTrace_append hprefix tailTrace_7912574
  have hstable : (prefixWord ++ tailWord_7912574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912574).length < 2 ^ (prefixWord ++ tailWord_7912574).sum := by decide
  have hdescent : baseEnd_7912574 < baseStart_7912574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912576 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_7912576 : Nat := 118140960795 + 7912576 * 2 ^ 59
def prefixEnd_7912576 : Nat := 4983230072969 + 3 ^ 40 * 7912576 * 2
def baseEnd_7912576 : Nat := 4062954703230139243710731

theorem tailTrace_7912576 : CollatzResearch.WordTrace tailWord_7912576 prefixEnd_7912576 4062954703230139243710731 := by
  unfold tailWord_7912576
  simp only [CollatzResearch.WordTrace]
  refine ⟨144297677891047993619306791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192396903854730658159075721 144297677891047993619306791)
  ·
    refine ⟨216446516836571990428960187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144297677891047993619306791 216446516836571990428960187)
    ·
      refine ⟨324669775254857985643440281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216446516836571990428960187 324669775254857985643440281)
      ·
        refine ⟨243502331441143489232580211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324669775254857985643440281 243502331441143489232580211)
        ·
          refine ⟨365253497161715233848870317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243502331441143489232580211 365253497161715233848870317)
          ·
            refine ⟨136970061435643212693326369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365253497161715233848870317 136970061435643212693326369)
            ·
              refine ⟨102727546076732409519994777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136970061435643212693326369 102727546076732409519994777)
              ·
                refine ⟨77045659557549307139996083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102727546076732409519994777 77045659557549307139996083)
                ·
                  refine ⟨115568489336323960709994125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77045659557549307139996083 115568489336323960709994125)
                  ·
                    refine ⟨43338183501121485266247797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115568489336323960709994125 43338183501121485266247797)
                    ·
                      refine ⟨4062954703230139243710731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43338183501121485266247797 4062954703230139243710731)
                      ·
                        rfl

theorem cell23_7912576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_7912576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912576 prefixEnd_7912576 := by exact prefixLift 7912576
  have htrace : WordTrace (prefixWord ++ tailWord_7912576) baseStart_7912576 baseEnd_7912576 := by
    simpa [prefixWord, tailWord_7912576, baseEnd_7912576] using wordTrace_append hprefix tailTrace_7912576
  have hstable : (prefixWord ++ tailWord_7912576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912576).length < 2 ^ (prefixWord ++ tailWord_7912576).sum := by decide
  have hdescent : baseEnd_7912576 < baseStart_7912576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912623 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_7912623 : Nat := 118140960795 + 7912623 * 2 ^ 59
def prefixEnd_7912623 : Nat := 4983230072969 + 3 ^ 40 * 7912623 * 2
def baseEnd_7912623 : Nat := 4062978836820900559823015

theorem tailTrace_7912623 : CollatzResearch.WordTrace tailWord_7912623 prefixEnd_7912623 4062978836820900559823015 := by
  unfold tailWord_7912623
  simp only [CollatzResearch.WordTrace]
  refine ⟨288597070012925714265574523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192398046675283809510383015 288597070012925714265574523)
  ·
    refine ⟨432895605019388571398361785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288597070012925714265574523 432895605019388571398361785)
    ·
      refine ⟨324671703764541428548771339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432895605019388571398361785 324671703764541428548771339)
      ·
        refine ⟨487007555646812142823157009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324671703764541428548771339 487007555646812142823157009)
        ·
          refine ⟨365255666735109107117367757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487007555646812142823157009 365255666735109107117367757)
          ·
            refine ⟨136970875025665915169012909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365255666735109107117367757 136970875025665915169012909)
            ·
              refine ⟨51364078134624718188379841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136970875025665915169012909 51364078134624718188379841)
              ·
                refine ⟨38523058600968538641284881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51364078134624718188379841 38523058600968538641284881)
                ·
                  refine ⟨28892293950726403980963661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38523058600968538641284881 28892293950726403980963661)
                  ·
                    refine ⟨10834610231522401492861373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28892293950726403980963661 10834610231522401492861373)
                    ·
                      refine ⟨4062978836820900559823015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10834610231522401492861373 4062978836820900559823015)
                      ·
                        rfl

theorem cell23_7912623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_7912623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912623 prefixEnd_7912623 := by exact prefixLift 7912623
  have htrace : WordTrace (prefixWord ++ tailWord_7912623) baseStart_7912623 baseEnd_7912623 := by
    simpa [prefixWord, tailWord_7912623, baseEnd_7912623] using wordTrace_append hprefix tailTrace_7912623
  have hstable : (prefixWord ++ tailWord_7912623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912623).length < 2 ^ (prefixWord ++ tailWord_7912623).sum := by decide
  have hdescent : baseEnd_7912623 < baseStart_7912623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7912663 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7912663 : Nat := 118140960795 + 7912663 * 2 ^ 59
def prefixEnd_7912663 : Nat := 4983230072969 + 3 ^ 40 * 7912663 * 2
def baseEnd_7912663 : Nat := 4062999376047080403322831

theorem tailTrace_7912663 : CollatzResearch.WordTrace tailWord_7912663 prefixEnd_7912663 4062999376047080403322831 := by
  unfold tailWord_7912663
  simp only [CollatzResearch.WordTrace]
  refine ⟨288598528932780801097030643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192399019288520534064687095 288598528932780801097030643)
  ·
    refine ⟨432897793399171201645545965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288598528932780801097030643 432897793399171201645545965)
    ·
      refine ⟨162336672524689200617079737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432897793399171201645545965 162336672524689200617079737)
      ·
        refine ⟨121752504393516900462809803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162336672524689200617079737 121752504393516900462809803)
        ·
          refine ⟨182628756590275350694214705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121752504393516900462809803 182628756590275350694214705)
          ·
            refine ⟨136971567442706513020661029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182628756590275350694214705 136971567442706513020661029)
            ·
              refine ⟨25682168895507471191373943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136971567442706513020661029 25682168895507471191373943)
              ·
                refine ⟨38523253343261206787060915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25682168895507471191373943 38523253343261206787060915)
                ·
                  refine ⟨57784880014891810180591373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38523253343261206787060915 57784880014891810180591373)
                  ·
                    refine ⟨21669330005584428817721765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57784880014891810180591373 21669330005584428817721765)
                    ·
                      refine ⟨4062999376047080403322831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21669330005584428817721765 4062999376047080403322831)
                      ·
                        rfl

theorem cell23_7912663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7912663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7912663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7912663 prefixEnd_7912663 := by exact prefixLift 7912663
  have htrace : WordTrace (prefixWord ++ tailWord_7912663) baseStart_7912663 baseEnd_7912663 := by
    simpa [prefixWord, tailWord_7912663, baseEnd_7912663] using wordTrace_append hprefix tailTrace_7912663
  have hstable : (prefixWord ++ tailWord_7912663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7912663).length < 2 ^ (prefixWord ++ tailWord_7912663).sum := by decide
  have hdescent : baseEnd_7912663 < baseStart_7912663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7912663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
